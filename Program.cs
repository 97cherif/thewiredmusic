using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Imaging;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Windows.Forms;
using NAudio.Dsp;
using NAudio.Wave;
using NAudio.Wave.SampleProviders;

static class Program
{
    [STAThread] static void Main() { ApplicationConfiguration.Initialize(); Application.Run(new Wired()); }
}

class Tap : ISampleProvider
{
    readonly ISampleProvider s; readonly float[] buf = new float[1024]; int pos; readonly object l = new();
    public Tap(ISampleProvider s) { this.s = s; }
    public WaveFormat WaveFormat => s.WaveFormat;
    public int Read(float[] b, int o, int c)
    {
        int r = s.Read(b, o, c), ch = WaveFormat.Channels;
        lock (l) for (int i = 0; i + ch - 1 < r; i += ch) { buf[pos] = b[o + i]; pos = (pos + 1) % buf.Length; }
        return r;
    }
    // fills a caller-owned array (no allocation per frame)
    public void Snap(float[] d) { lock (l) { for (int i = 0; i < d.Length; i++) d[i] = buf[(pos + i) % buf.Length]; } }
}

class Track { public string Url, Path, Artist, Title, Album, Year = "", Lyr; public double Dur; public Bitmap Art; public bool Saved; }

class Wired : Form
{
    [DllImport("user32.dll")] static extern bool ReleaseCapture();
    [DllImport("user32.dll")] static extern IntPtr SendMessage(IntPtr h, int m, int w, int l);

    // ---------- palette: cold water, 3am ----------
    static readonly Color BG = Color.FromArgb(6, 10, 15), ICE = Color.FromArgb(150, 214, 232), ICE2 = Color.FromArgb(214, 242, 250),
        TX = Color.FromArgb(218, 230, 238), DM = Color.FromArgb(108, 132, 146), WH = Color.White;
    static Color Al(Color c, int a) => Color.FromArgb(Math.Clamp(a, 0, 255), c);
    static readonly string[] Ext = { ".mp3", ".flac", ".wav", ".ogg", ".m4a", ".aac", ".wma" };

    // ---------- cached drawing objects (no per-frame allocation) ----------
    static readonly Dictionary<int, SolidBrush> bc = new();
    static readonly Dictionary<long, Pen> pc = new();
    static SolidBrush Br(Color c) { int k = c.ToArgb(); if (!bc.TryGetValue(k, out var b)) bc[k] = b = new SolidBrush(c); return b; }
    static Pen Pe(Color c, float w)
    {
        long k = ((long)c.ToArgb() << 16) ^ (long)(w * 10);
        if (!pc.TryGetValue(k, out var p)) pc[k] = p = new Pen(c, w) { StartCap = LineCap.Round, EndCap = LineCap.Round, LineJoin = LineJoin.Round };
        return p;
    }
    static Font Fn(string fam, float px, FontStyle st = FontStyle.Regular) => new Font(fam, px, st, GraphicsUnit.Pixel);
    static readonly Font fTitle = Fn("Segoe UI Light", 27), fArt = Fn("Segoe UI Semibold", 12), fS = Fn("Segoe UI", 12), fXs = Fn("Segoe UI", 11),
        fRow = Fn("Segoe UI", 13), fBtn = Fn("Segoe UI Semibold", 11), fHdr = Fn("Segoe UI Semibold", 11), fLyr = Fn("Segoe UI", 14);
    static readonly StringFormat sfL = new(StringFormatFlags.NoWrap) { Trimming = StringTrimming.EllipsisCharacter },
        sfR = new(StringFormatFlags.NoWrap) { Alignment = StringAlignment.Far, Trimming = StringTrimming.EllipsisCharacter },
        sfCC = new(StringFormatFlags.NoWrap) { Alignment = StringAlignment.Center, LineAlignment = StringAlignment.Center, Trimming = StringTrimming.EllipsisCharacter },
        sfW = new() { Trimming = StringTrimming.None };

    // ---------- state ----------
    readonly List<Track> pl = new(); int cur = -1, scroll, lyrY;
    WaveOutEvent wo; WaveStream rd; VolumeSampleProvider vsp; Tap tap; int gen;
    bool playing, shuf, rep, mute, dragSeek, dragVol; float vol = .6f, seekFrac;
    readonly float[] bars = new float[48], spec = new float[48], snap = new float[1024], win = new float[1024];
    readonly Complex[] cpx = new Complex[1024];
    string status = ""; int statusEnd;
    readonly Random R = new(); bool dlBusy, dlCancel; System.Diagnostics.Process dlProc;
    double posS, durS; int last = Environment.TickCount;

    // ---------- layout (logical units; scaled by DPI) ----------
    float U => Math.Max(1f, DeviceDpi / 96f);
    int W = 1000, H = 620; const int RowH = 40, HdrH = 44;
    Rectangle rHdr, rMenu, rMin, rMax, rClose, rNow, rVis, rLyr, rPl, rList, rArt, rSeek, rVol, rTime, rBF, rBY, rDT, rDA;
    readonly Rectangle[] rb = new Rectangle[6]; // 0 prev 1 play 2 next 3 repeat 4 shuffle 5 mute
    int colX, colR, hid; Point mp = new(-1, -1);
    Bitmap bg; bool bgDirty = true; Rectangle clip;
    Bitmap artBmp; Track artFor; int artPs;
    int Rows => Math.Max(1, rList.Height / RowH);

    public Wired()
    {
        Text = "THE WIRED MUSIC"; FormBorderStyle = FormBorderStyle.None; StartPosition = FormStartPosition.CenterScreen;
        SetStyle(ControlStyles.AllPaintingInWmPaint | ControlStyles.UserPaint | ControlStyles.OptimizedDoubleBuffer | ControlStyles.ResizeRedraw, true);
        BackColor = BG; AllowDrop = true; KeyPreview = true; try { Icon = Icon.ExtractAssociatedIcon(Environment.ProcessPath); } catch { }
        MinimumSize = new Size((int)(900 * U), (int)(560 * U));
        ClientSize = new Size((int)(1000 * U), (int)(620 * U));
        for (int i = 0; i < 1024; i++) win[i] = (float)FastFourierTransform.HammingWindow(i, 1024);
        var rn = new Random(7); for (int i = 0; i < bx.Length; i++) { bx[i] = (float)rn.NextDouble(); by[i] = (float)rn.NextDouble(); bv[i] = .4f + (float)rn.NextDouble(); bsz[i] = 2f + (float)rn.NextDouble() * 3f; bph[i] = (float)rn.NextDouble() * 6.28f; }
        DragEnter += (s, e) => e.Effect = DragDropEffects.Copy;
        DragDrop += (s, e) => Add((string[])e.Data.GetData(DataFormats.FileDrop));
        var t = new System.Windows.Forms.Timer { Interval = 16 };
        t.Tick += (s, e) => Tick(); t.Start();
        FormClosed += (s, e) => Stop();
        Relayout();
    }

    static readonly List<Bitmap> Covers = LoadCovers();
    static List<Bitmap> LoadCovers()
    {
        var l = new List<Bitmap>(); var asm = System.Reflection.Assembly.GetExecutingAssembly();
        foreach (var n in asm.GetManifestResourceNames().Where(n => n.StartsWith("cover.")))
            try { using var st = asm.GetManifestResourceStream(n); using var tmp = Image.FromStream(st); l.Add(Square(tmp, 320)); } catch { }
        return l;
    }
    Bitmap RandomCover() => Covers.Count > 0 ? Covers[R.Next(Covers.Count)] : null;
    static Bitmap Square(Image im, int s)
    {
        var b = new Bitmap(s, s, PixelFormat.Format32bppPArgb); using var g = Graphics.FromImage(b); g.InterpolationMode = InterpolationMode.HighQualityBicubic;
        int sq = Math.Min(im.Width, im.Height); g.DrawImage(im, new Rectangle(0, 0, s, s), (im.Width - sq) / 2, (im.Height - sq) / 2, sq, sq, GraphicsUnit.Pixel); return b;
    }

    void St(string s, int ms = 0) { status = s; statusEnd = ms > 0 ? Environment.TickCount + ms : 0; Inv(rHdr); }

    // ---------- library (tags are read off the UI thread) ----------
    void Add(IEnumerable<string> paths)
    {
        var src = paths.ToList(); St("Adding music...");
        Task.Run(() =>
        {
            var made = new List<Track>();
            var files = new List<string>();
            foreach (var p in src)
                try { if (Directory.Exists(p)) files.AddRange(Directory.EnumerateFiles(p, "*.*", SearchOption.AllDirectories)); else files.Add(p); } catch { }
            foreach (var f in files.Where(f => Ext.Contains(System.IO.Path.GetExtension(f).ToLower())).OrderBy(f => f))
            {
                var t = new Track { Path = f, Title = System.IO.Path.GetFileNameWithoutExtension(f), Artist = "Unknown" };
                try
                {
                    using var tf = TagLib.File.Create(f);
                    if (!string.IsNullOrWhiteSpace(tf.Tag.Title)) t.Title = tf.Tag.Title;
                    if (tf.Tag.Performers.Length > 0) t.Artist = tf.Tag.Performers[0];
                    t.Album = tf.Tag.Album ?? ""; t.Year = tf.Tag.Year > 0 ? tf.Tag.Year.ToString() : "";
                    t.Dur = tf.Properties.Duration.TotalSeconds; t.Lyr = tf.Tag.Lyrics;
                    if (tf.Tag.Pictures.Length > 0) { using var ms = new MemoryStream(tf.Tag.Pictures[0].Data.Data); using var im = Image.FromStream(ms); t.Art = Square(im, 320); }
                }
                catch { }
                try
                {
                    var lrc = System.IO.Path.ChangeExtension(f, ".lrc");
                    if (string.IsNullOrWhiteSpace(t.Lyr) && System.IO.File.Exists(lrc)) t.Lyr = Regex.Replace(System.IO.File.ReadAllText(lrc), @"\[[^\]]*\]", "").Trim();
                }
                catch { }
                made.Add(t);
            }
            try
            {
                BeginInvoke(new Action(() =>
                {
                    foreach (var t in made) t.Art ??= RandomCover();
                    pl.AddRange(made); St(made.Count == 0 ? "No audio files found" : "", made.Count == 0 ? 4000 : 0);
                    if (cur < 0 && pl.Count > 0) Play(0); else Invalidate();
                }));
            }
            catch { }
        });
    }

    // ---------- playback ----------
    void EnsureVisible() { int v = Rows; if (cur < scroll) scroll = cur; if (cur >= scroll + v) scroll = cur - v + 1; scroll = Math.Clamp(scroll, 0, Math.Max(0, pl.Count - v)); }
    void Play(int i)
    {
        if (i < 0 || i >= pl.Count) return;
        Stop(); cur = i; ++gen; lyrY = 0; posS = 0; EnsureVisible(); Relayout();
        if (pl[i].Url != null) { Tune(i, gen); return; }
        try
        {
            rd = Rd(pl[i].Path); vsp = new VolumeSampleProvider(rd.ToSampleProvider()) { Volume = mute ? 0 : vol }; tap = new Tap(vsp);
            wo = new WaveOutEvent { DesiredLatency = 120 }; wo.Init(tap.ToWaveProvider()); wo.Play(); playing = true; St("");
        }
        catch (Exception ex) { St("Couldn't play: " + ex.Message, 6000); playing = false; }
    }
    // dispose off the UI thread so switching tracks never stalls
    void Stop()
    {
        var w = wo; var r = rd; wo = null; rd = null; vsp = null; tap = null; playing = false;
        if (w != null || r != null) Task.Run(() => { try { w?.Dispose(); } catch { } try { r?.Dispose(); } catch { } });
    }
    void Toggle()
    {
        if (wo == null) { Play(cur < 0 ? 0 : cur); return; }
        if (playing) wo.Pause(); else wo.Play(); playing = !playing;
    }
    void Next() { if (pl.Count == 0) return; Play(shuf ? R.Next(pl.Count) : (cur + 1) % pl.Count); }
    void Prev() { if (pl.Count == 0) return; if (rd != null && rd.CurrentTime.TotalSeconds > 3) rd.CurrentTime = TimeSpan.Zero; else Play((cur - 1 + pl.Count) % pl.Count); }
    void Vol() { if (vsp != null) vsp.Volume = mute ? 0 : vol; }
    static WaveStream Rd(string s) => s.StartsWith("http") ? (WaveStream)new MediaFoundationReader(s) : new AudioFileReader(s);

    // ---------- YouTube (via yt-dlp, downloaded automatically on first use) ----------
    static async Task<string> Ytdlp(string args, Action<System.Diagnostics.Process> onStart = null)
    {
        var dir = System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "TheWiredMusic");
        Directory.CreateDirectory(dir); var exe = System.IO.Path.Combine(dir, "yt-dlp.exe");
        if (!System.IO.File.Exists(exe))
        {
            using var h = new HttpClient();
            System.IO.File.WriteAllBytes(exe, await h.GetByteArrayAsync("https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"));
        }
        var psi = new System.Diagnostics.ProcessStartInfo(exe, args) { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false, CreateNoWindow = true, StandardOutputEncoding = System.Text.Encoding.UTF8 };
        psi.Environment["PYTHONIOENCODING"] = "utf-8"; psi.Environment["PYTHONUTF8"] = "1";
        using var p = System.Diagnostics.Process.Start(psi); onStart?.Invoke(p);
        var errTask = p.StandardError.ReadToEndAsync(); // drain so the process never blocks on a full pipe
        var o = await p.StandardOutput.ReadToEndAsync(); await p.WaitForExitAsync(); await errTask; return o;
    }
    static Button Flat(string t, int x, int y, Color c)
    {
        var b = new Button { Text = t, Left = x, Top = y, Width = 110, Height = 30, FlatStyle = FlatStyle.Flat, BackColor = Color.FromArgb(16, 26, 34), ForeColor = c, Font = new Font("Segoe UI", 9f), UseVisualStyleBackColor = false, Cursor = Cursors.Hand };
        b.FlatAppearance.BorderColor = Color.FromArgb(70, c.R, c.G, c.B); b.FlatAppearance.MouseOverBackColor = Color.FromArgb(26, 44, 56); return b;
    }
    static string Ask(string title)
    {
        using var f = new Form { FormBorderStyle = FormBorderStyle.None, Size = new Size(580, 132), StartPosition = FormStartPosition.CenterParent, BackColor = Color.FromArgb(10, 16, 22), ShowInTaskbar = false };
        f.Paint += (s, e) => { e.Graphics.DrawRectangle(Pe(Al(ICE, 60), 1), 0, 0, f.Width - 1, f.Height - 1); using var fn = new Font("Segoe UI", 9.5f); e.Graphics.DrawString(title, fn, Br(DM), 16, 14); };
        var tb = new TextBox { Left = 16, Top = 44, Width = 548, BorderStyle = BorderStyle.FixedSingle, BackColor = BG, ForeColor = ICE2, Font = new Font("Segoe UI", 10.5f) };
        if (Clipboard.ContainsText() && Clipboard.GetText().Contains("youtu")) tb.Text = Clipboard.GetText().Trim();
        var ok = Flat("Add", 340, 86, ICE); ok.DialogResult = DialogResult.OK; var no = Flat("Cancel", 456, 86, TX); no.DialogResult = DialogResult.Cancel;
        f.Controls.Add(tb); f.Controls.Add(ok); f.Controls.Add(no); f.AcceptButton = ok; f.CancelButton = no; f.Shown += (s, e) => { tb.Focus(); tb.SelectAll(); };
        return f.ShowDialog() == DialogResult.OK ? tb.Text.Trim() : null;
    }
    static void About()
    {
        using var f = new Form { FormBorderStyle = FormBorderStyle.None, Size = new Size(380, 170), StartPosition = FormStartPosition.CenterParent, BackColor = Color.FromArgb(10, 16, 22), ShowInTaskbar = false };
        f.Paint += (s, e) =>
        {
            var g = e.Graphics; g.DrawRectangle(Pe(Al(ICE, 60), 1), 0, 0, f.Width - 1, f.Height - 1); using var fn = new Font("Segoe UI", 10f); using var sf = new StringFormat { Alignment = StringAlignment.Center };
            g.DrawString("THE WIRED MUSIC\n\nNo matter where you are,\neveryone is always connected.", fn, Br(TX), new RectangleF(0, 22, f.Width, 100), sf);
        };
        var ok = Flat("OK", 135, 124, ICE); ok.DialogResult = DialogResult.OK; f.Controls.Add(ok); f.AcceptButton = ok; f.CancelButton = ok; f.ShowDialog();
    }
    void StopDl() { dlCancel = true; St("Stopping download..."); try { dlProc?.Kill(true); } catch { } }
    async void Download(List<Track> list)
    {
        list = list.Where(t => t.Url != null).ToList();
        if (list.Count == 0) { St("Add a YouTube link first", 4000); return; }
        if (dlBusy) { St("A download is already running", 4000); return; }
        using var d = new FolderBrowserDialog { Description = "Choose where to save the music" };
        if (d.ShowDialog() != DialogResult.OK) return;
        dlBusy = true; dlCancel = false; var t0 = DateTime.Now; int ok = 0; var tpl = System.IO.Path.Combine(d.SelectedPath, "%(title)s.%(ext)s");
        for (int i = 0; i < list.Count; i++)
        {
            if (dlCancel) break;
            var t = list[i]; St($"Downloading {i + 1}/{list.Count}: {t.Title}");
            try
            {
                var o = await Ytdlp($"-f \"bestaudio[ext=m4a]/bestaudio\" --no-playlist --no-warnings --no-simulate --print after_move:filepath -o \"{tpl}\" \"{t.Url}\"", p => dlProc = p);
                var path = o.Trim().Split('\n').Last().Trim();
                if (System.IO.File.Exists(path)) { ok++; t.Saved = true; }
            }
            catch { }
        }
        if (dlCancel) { try { foreach (var f in Directory.GetFiles(d.SelectedPath)) if ((f.EndsWith(".part") || f.EndsWith(".ytdl")) && System.IO.File.GetLastWriteTime(f) >= t0.AddSeconds(-2)) System.IO.File.Delete(f); } catch { } }
        dlBusy = false; dlProc = null; St(dlCancel ? $"Stopped - {ok} song(s) kept" : $"Downloaded {ok}/{list.Count}", 6000); Invalidate();
    }
    void OpenYt() { var u = Ask("Paste a YouTube video or playlist link"); if (!string.IsNullOrEmpty(u)) AddYt(u); }
    async void AddYt(string url)
    {
        St("Connecting...");
        try
        {
            var j = await Ytdlp($"-J --flat-playlist --no-warnings \"{url}\"");
            using var d = System.Text.Json.JsonDocument.Parse(j); var root = d.RootElement; int n = 0;
            string S(System.Text.Json.JsonElement e, string k) => e.TryGetProperty(k, out var v) && v.ValueKind == System.Text.Json.JsonValueKind.String ? v.GetString() : null;
            void One(System.Text.Json.JsonElement e, string ch)
            {
                var id = S(e, "id"); var title = S(e, "title"); if (id == null || (title != null && title.StartsWith("["))) return;
                pl.Add(new Track { Url = "https://www.youtube.com/watch?v=" + id, Title = title ?? "Untitled", Artist = S(e, "channel") ?? S(e, "uploader") ?? ch ?? "YouTube", Album = "YouTube", Art = RandomCover(),
                    Dur = e.TryGetProperty("duration", out var du) && du.ValueKind == System.Text.Json.JsonValueKind.Number ? du.GetDouble() : 0 }); n++;
            }
            if (root.TryGetProperty("entries", out var en)) { var pc2 = S(root, "uploader") ?? S(root, "channel"); foreach (var e in en.EnumerateArray()) One(e, pc2); }
            else One(root, null);
            St($"Added {n} tracks", 4000); if (cur < 0 && pl.Count > 0) Play(0); else Invalidate();
        }
        catch (Exception ex) { St("Couldn't connect: " + ex.Message, 6000); }
    }
    void Tune(int i, int my)
    {
        var t = pl[i]; St("Tuning in...");
        Task.Run(async () =>
        {
            try
            {
                var u = (await Ytdlp($"-f \"bestaudio[ext=m4a]/bestaudio\" -g --no-playlist --no-warnings \"{t.Url}\"")).Trim().Split('\n')[0].Trim();
                if (!u.StartsWith("http")) throw new Exception("no stream found - delete %LocalAppData%\\TheWiredMusic\\yt-dlp.exe to update it");
                BeginInvoke(new Action(() =>
                {
                    if (my != gen) return;
                    try
                    {
                        rd = Rd(u); vsp = new VolumeSampleProvider(rd.ToSampleProvider()) { Volume = mute ? 0 : vol }; tap = new Tap(vsp);
                        wo = new WaveOutEvent { DesiredLatency = 150 }; wo.Init(tap.ToWaveProvider()); wo.Play(); playing = true; St("");
                    }
                    catch (Exception ex) { St("Couldn't play: " + ex.Message, 6000); }
                }));
            }
            catch (Exception ex) { BeginInvoke(new Action(() => { if (my == gen) St("Couldn't play: " + ex.Message, 6000); })); }
        });
    }

    // ---------- frame tick: audio analysis + animation only ----------
    void Tick()
    {
        if (WindowState == FormWindowState.Minimized || ClientSize.Width <= 0) return;
        int now = Environment.TickCount; float dt = Math.Clamp((now - last) / 1000f, .001f, .05f); last = now;
        if (statusEnd != 0 && now - statusEnd >= 0) { status = ""; statusEnd = 0; Inv(rHdr); }
        if (wo != null && playing && wo.PlaybackState == PlaybackState.Stopped) { if (rep) Play(cur); else Next(); return; }
        Array.Clear(spec);
        if (playing && tap != null)
        {
            tap.Snap(snap); wave = snap;
            for (int i = 0; i < 1024; i++) { cpx[i].X = snap[i] * win[i]; cpx[i].Y = 0; }
            FastFourierTransform.FFT(true, 10, cpx);
            for (int k = 0; k < 48; k++)
            {
                int a = (int)Math.Pow(511, k / 48.0) + 1, z = Math.Min(511, (int)Math.Pow(511, (k + 1) / 48.0) + 1); float m = 0;
                for (int j = a; j <= z; j++) m = Math.Max(m, (float)Math.Sqrt(cpx[j].X * cpx[j].X + cpx[j].Y * cpx[j].Y));
                spec[k] = Math.Min(1, m * (1.5f + k * .12f));
            }
        }
        float dec = (float)Math.Pow(.88, dt * 30);
        for (int k = 0; k < 48; k++) bars[k] = spec[k] > bars[k] ? bars[k] + (spec[k] - bars[k]) * .75f : bars[k] * dec;
        try { posS = rd?.CurrentTime.TotalSeconds ?? 0; durS = rd?.TotalTime.TotalSeconds ?? 0; } catch { }
        if (durS <= 0 && cur >= 0 && cur < pl.Count) durS = pl[cur].Dur;
        Vis(dt); Inv(rVis); if (playing || dragSeek) Inv(rTime);
    }

    // ---------- visualiser state ----------
    float[] wave; float bassAvg, flash, beatCd, avg; int shI;
    readonly float[] shR = new float[6], shA = new float[6];
    readonly float[] bx = new float[48], by = new float[48], bv = new float[48], bsz = new float[48], bph = new float[48];
    readonly PointF[] ringP = new PointF[96], waveP = new PointF[128];
    void Vis(float dt)
    {
        if (!playing) wave = null;
        float bass = 0; for (int k = 0; k < 5; k++) bass += bars[k]; bass /= 5;
        if (beatCd > 0) beatCd -= dt;
        if (playing && beatCd <= 0 && bass > bassAvg * 1.3f + .06f) { beatCd = .22f; flash = 1; shR[shI] = 0; shA[shI] = 1; shI = (shI + 1) % shR.Length; }
        bassAvg += (bass - bassAvg) * Math.Min(1, dt * 1.8f); flash *= (float)Math.Pow(.86, dt * 30);
        for (int k = 0; k < shR.Length; k++) if (shA[k] > 0) { shR[k] += dt * 150; shA[k] -= dt * 1.1f; }
        float s = 0; for (int k = 0; k < 48; k++) s += bars[k]; avg = s / 48;
        for (int i = 0; i < bx.Length; i++) { by[i] -= bv[i] * dt * (.03f + avg * .3f + flash * .1f); if (by[i] < -.05f) { by[i] = 1.05f; bx[i] = (float)R.NextDouble(); } }
    }

    // ---------- layout ----------
    void Relayout()
    {
        float u = U; W = Math.Max(1, (int)(ClientSize.Width / u)); H = Math.Max(1, (int)(ClientSize.Height / u));
        rHdr = new Rectangle(0, 0, W, HdrH);
        rMenu = new Rectangle(10, 6, 32, 32); rClose = new Rectangle(W - 44, 6, 32, 32); rMax = new Rectangle(W - 80, 6, 32, 32); rMin = new Rectangle(W - 116, 6, 32, 32);
        int pad = 20, top = 52, plw = Math.Clamp((int)(W * .3f), 290, 380);
        rPl = new Rectangle(W - pad - plw, top, plw, Math.Max(100, H - top - pad));
        int lw = rPl.X - 16 - pad;
        rNow = new Rectangle(pad, top, lw, 182);
        int vy = rNow.Bottom + 16, vh = Math.Max(80, H - pad - vy);
        bool hl = cur >= 0 && cur < pl.Count && !string.IsNullOrWhiteSpace(pl[cur].Lyr) && lw >= 640;
        if (hl) { int w2 = (int)(lw * .36f); rVis = new Rectangle(pad, vy, lw - w2 - 16, vh); rLyr = new Rectangle(rVis.Right + 16, vy, w2, vh); }
        else { rVis = new Rectangle(pad, vy, lw, vh); rLyr = Rectangle.Empty; }
        rArt = new Rectangle(rNow.X + 16, rNow.Y + 16, 150, 150);
        colX = rArt.Right + 22; colR = rNow.Right - 22;
        rSeek = new Rectangle(colX, rNow.Y + 100, Math.Max(10, colR - colX), 4);
        rTime = new Rectangle(colX, rNow.Y + 92, colR - colX, 34);
        int cy = rNow.Y + 150;
        rb[4] = new Rectangle(colX, cy - 17, 34, 34); rb[0] = new Rectangle(colX + 38, cy - 18, 36, 36); rb[1] = new Rectangle(colX + 78, cy - 23, 46, 46);
        rb[2] = new Rectangle(colX + 128, cy - 18, 36, 36); rb[3] = new Rectangle(colX + 168, cy - 17, 34, 34);
        int avail = colR - (colX + 210), vw = avail >= 100 ? Math.Min(120, avail - 40) : 0;
        rVol = new Rectangle(colR - vw, cy - 2, vw, 4);
        rb[5] = new Rectangle(vw > 0 ? rVol.X - 38 : colR - 34, cy - 17, 34, 34);
        int by0 = rPl.Bottom - 16 - 32, bw = (rPl.Width - 32 - 18) / 4, bx0 = rPl.X + 16;
        rBF = new Rectangle(bx0, by0, bw, 32); rBY = new Rectangle(bx0 + bw + 6, by0, bw, 32); rDT = new Rectangle(bx0 + 2 * (bw + 6), by0, bw, 32); rDA = new Rectangle(bx0 + 3 * (bw + 6), by0, bw, 32);
        rList = new Rectangle(rPl.X + 6, rPl.Y + 44, rPl.Width - 12, Math.Max(RowH, by0 - 10 - (rPl.Y + 44)));
        scroll = Math.Clamp(scroll, 0, Math.Max(0, pl.Count - Rows));
        bgDirty = true; Invalidate();
    }
    protected override void OnResize(EventArgs e) { base.OnResize(e); if (ClientSize.Width > 0) Relayout(); }
    void Inv(Rectangle r) { if (r.Width <= 0) return; float u = U; Invalidate(new Rectangle((int)(r.X * u) - 3, (int)(r.Y * u) - 3, (int)(r.Width * u) + 6, (int)(r.Height * u) + 6)); }
    bool Dirty(Rectangle r) { float u = U; return clip.IntersectsWith(new Rectangle((int)(r.X * u) - 1, (int)(r.Y * u) - 1, (int)(r.Width * u) + 2, (int)(r.Height * u) + 2)); }

    // ---------- drawing helpers ----------
    static GraphicsPath RR(RectangleF r, float d)
    {
        d = Math.Max(1, Math.Min(d, Math.Min(r.Width, r.Height))); var p = new GraphicsPath();
        p.AddArc(r.X, r.Y, d, d, 180, 90); p.AddArc(r.Right - d, r.Y, d, d, 270, 90); p.AddArc(r.Right - d, r.Bottom - d, d, d, 0, 90); p.AddArc(r.X, r.Bottom - d, d, d, 90, 90); p.CloseFigure(); return p;
    }
    static void FillRR(Graphics g, Brush b, RectangleF r, float d) { using var p = RR(r, d); g.FillPath(b, p); }
    static void DrawRR(Graphics g, Pen pe, RectangleF r, float d) { using var p = RR(r, d); g.DrawPath(pe, p); }
    static void Txt(Graphics g, string s, Font f, Color c, float x, float y, float w, StringFormat sf = null) => g.DrawString(s ?? "", f, Br(c), new RectangleF(x, y, Math.Max(1, w), f.Height + 4), sf ?? sfL);
    static void TxtIn(Graphics g, string s, Font f, Color c, RectangleF r, StringFormat sf) => g.DrawString(s ?? "", f, Br(c), r, sf);
    static string Fm(double s) => s <= 0 || double.IsNaN(s) ? "0:00" : $"{(int)s / 60}:{(int)s % 60:00}";

    const int I_PREV = 0, I_PLAY = 1, I_PAUSE = 2, I_NEXT = 3, I_REP = 4, I_SHUF = 5, I_VOL = 6, I_MUTE = 7, I_MENU = 8, I_MIN = 9, I_MAX = 10, I_CLOSE = 11, I_DOWN = 12, I_CHECK = 13;
    static void Ico(Graphics g, int k, float cx, float cy, float s, Color c, float w = 1.7f)
    {
        var p = Pe(c, w); var b = Br(c);
        switch (k)
        {
            case I_PLAY: { var t = new[] { new PointF(cx - s * .55f, cy - s * .8f), new PointF(cx - s * .55f, cy + s * .8f), new PointF(cx + s * .85f, cy) }; g.FillPolygon(b, t); g.DrawPolygon(p, t); break; }
            case I_PAUSE: g.FillRectangle(b, cx - s * .65f, cy - s * .75f, s * .45f, s * 1.5f); g.FillRectangle(b, cx + s * .2f, cy - s * .75f, s * .45f, s * 1.5f); break;
            case I_PREV: { var t = new[] { new PointF(cx + s * .8f, cy - s * .75f), new PointF(cx + s * .8f, cy + s * .75f), new PointF(cx - s * .4f, cy) }; g.FillPolygon(b, t); g.DrawPolygon(p, t); g.DrawLine(p, cx - s * .8f, cy - s * .75f, cx - s * .8f, cy + s * .75f); break; }
            case I_NEXT: { var t = new[] { new PointF(cx - s * .8f, cy - s * .75f), new PointF(cx - s * .8f, cy + s * .75f), new PointF(cx + s * .4f, cy) }; g.FillPolygon(b, t); g.DrawPolygon(p, t); g.DrawLine(p, cx + s * .8f, cy - s * .75f, cx + s * .8f, cy + s * .75f); break; }
            case I_SHUF:
                g.DrawLines(p, new[] { new PointF(cx - s, cy - s * .55f), new PointF(cx - s * .25f, cy - s * .55f), new PointF(cx + s * .3f, cy + s * .55f), new PointF(cx + s * .85f, cy + s * .55f) });
                g.DrawLines(p, new[] { new PointF(cx - s, cy + s * .55f), new PointF(cx - s * .25f, cy + s * .55f), new PointF(cx + s * .3f, cy - s * .55f), new PointF(cx + s * .85f, cy - s * .55f) });
                g.DrawLines(p, new[] { new PointF(cx + s * .55f, cy + s * .25f), new PointF(cx + s * .85f, cy + s * .55f), new PointF(cx + s * .55f, cy + s * .85f) });
                g.DrawLines(p, new[] { new PointF(cx + s * .55f, cy - s * .85f), new PointF(cx + s * .85f, cy - s * .55f), new PointF(cx + s * .55f, cy - s * .25f) }); break;
            case I_REP:
                g.DrawLines(p, new[] { new PointF(cx - s * .8f, cy + s * .1f), new PointF(cx - s * .8f, cy - s * .5f), new PointF(cx + s * .75f, cy - s * .5f) });
                g.DrawLines(p, new[] { new PointF(cx + s * .45f, cy - s * .8f), new PointF(cx + s * .75f, cy - s * .5f), new PointF(cx + s * .45f, cy - s * .2f) });
                g.DrawLines(p, new[] { new PointF(cx + s * .8f, cy - s * .1f), new PointF(cx + s * .8f, cy + s * .5f), new PointF(cx - s * .75f, cy + s * .5f) });
                g.DrawLines(p, new[] { new PointF(cx - s * .45f, cy + s * .2f), new PointF(cx - s * .75f, cy + s * .5f), new PointF(cx - s * .45f, cy + s * .8f) }); break;
            case I_VOL:
            case I_MUTE:
                { var t = new[] { new PointF(cx - s * .95f, cy - s * .35f), new PointF(cx - s * .5f, cy - s * .35f), new PointF(cx, cy - s * .8f), new PointF(cx, cy + s * .8f), new PointF(cx - s * .5f, cy + s * .35f), new PointF(cx - s * .95f, cy + s * .35f) };
                  g.FillPolygon(b, t); g.DrawPolygon(p, t);
                  if (k == I_MUTE) { g.DrawLine(p, cx + s * .35f, cy - s * .4f, cx + s * 1.05f, cy + s * .4f); g.DrawLine(p, cx + s * .35f, cy + s * .4f, cx + s * 1.05f, cy - s * .4f); }
                  else { g.DrawArc(p, cx - s * .45f, cy - s * .45f, s * .9f, s * .9f, -55, 110); g.DrawArc(p, cx - s * .8f, cy - s * .85f, s * 1.6f, s * 1.7f, -55, 110); }
                  break; }
            case I_MENU: g.DrawLine(p, cx - s * .8f, cy - s * .55f, cx + s * .8f, cy - s * .55f); g.DrawLine(p, cx - s * .8f, cy, cx + s * .8f, cy); g.DrawLine(p, cx - s * .8f, cy + s * .55f, cx + s * .4f, cy + s * .55f); break;
            case I_MIN: g.DrawLine(p, cx - s * .7f, cy, cx + s * .7f, cy); break;
            case I_MAX: g.DrawRectangle(p, cx - s * .6f, cy - s * .6f, s * 1.2f, s * 1.2f); break;
            case I_CLOSE: g.DrawLine(p, cx - s * .65f, cy - s * .65f, cx + s * .65f, cy + s * .65f); g.DrawLine(p, cx - s * .65f, cy + s * .65f, cx + s * .65f, cy - s * .65f); break;
            case I_DOWN:
                g.DrawLine(p, cx, cy - s * .8f, cx, cy + s * .45f); g.DrawLines(p, new[] { new PointF(cx - s * .55f, cy - s * .1f), new PointF(cx, cy + s * .5f), new PointF(cx + s * .55f, cy - s * .1f) });
                g.DrawLine(p, cx - s * .75f, cy + s * .9f, cx + s * .75f, cy + s * .9f); break;
            case I_CHECK: g.DrawLines(p, new[] { new PointF(cx - s * .65f, cy), new PointF(cx - s * .15f, cy + s * .5f), new PointF(cx + s * .7f, cy - s * .5f) }); break;
        }
    }

    // ---------- cached background: gradient, glow, glass panels ----------
    void BuildBg()
    {
        int pw = Math.Max(1, ClientSize.Width), ph = Math.Max(1, ClientSize.Height);
        bg?.Dispose(); bg = new Bitmap(pw, ph, PixelFormat.Format32bppPArgb);
        using var g = Graphics.FromImage(bg); g.SmoothingMode = SmoothingMode.AntiAlias;
        using (var lb = new LinearGradientBrush(new Rectangle(0, 0, pw, ph), Color.FromArgb(10, 18, 26), Color.FromArgb(4, 7, 11), 90f)) g.FillRectangle(lb, 0, 0, pw, ph);
        using (var gp = new GraphicsPath())
        {
            gp.AddEllipse(pw * .05f, -ph * .55f, pw * .9f, ph * 1.2f);
            using var pb = new PathGradientBrush(gp) { CenterColor = Al(ICE, 30), SurroundColors = new[] { Al(ICE, 0) } }; g.FillPath(pb, gp);
        }
        g.ScaleTransform(U, U);
        void Panel(Rectangle r)
        {
            if (r.IsEmpty) return;
            var rf = new RectangleF(r.X, r.Y, r.Width, r.Height);
            using (var lb = new LinearGradientBrush(rf, Al(WH, 15), Al(WH, 4), 90f)) FillRR(g, lb, rf, 36);
            DrawRR(g, Pe(Al(WH, 22), 1f), new RectangleF(r.X + .5f, r.Y + .5f, r.Width - 1, r.Height - 1), 36);
        }
        Panel(rNow); Panel(rVis); Panel(rLyr); Panel(rPl);
        bgDirty = false;
    }

    Bitmap ArtOf(Track T, int logical)
    {
        int ps = Math.Max(8, (int)(logical * U));
        if (artBmp != null && artFor == T && artPs == ps) return artBmp;
        artBmp?.Dispose(); artBmp = new Bitmap(ps, ps, PixelFormat.Format32bppPArgb); artFor = T; artPs = ps;
        using var g = Graphics.FromImage(artBmp); g.SmoothingMode = SmoothingMode.AntiAlias; g.InterpolationMode = InterpolationMode.HighQualityBicubic;
        using var path = RR(new RectangleF(0, 0, ps, ps), ps * .12f); g.SetClip(path);
        if (T?.Art != null) { g.DrawImage(T.Art, new Rectangle(0, 0, ps, ps)); g.FillRectangle(Br(Color.FromArgb(70, 6, 36, 54)), 0, 0, ps, ps); }
        else
        {
            using (var lb = new LinearGradientBrush(new Rectangle(0, 0, ps, ps), Color.FromArgb(22, 44, 58), Color.FromArgb(8, 14, 20), 90f)) g.FillRectangle(lb, 0, 0, ps, ps);
            for (int i = 1; i <= 3; i++) { float rr = ps * .13f * i; g.DrawEllipse(Pe(Al(ICE, 70 - i * 15), 1.2f), ps / 2f - rr, ps / 2f - rr, 2 * rr, 2 * rr); }
        }
        g.ResetClip(); DrawRR(g, Pe(Al(WH, 36), 1.2f), new RectangleF(.6f, .6f, ps - 1.2f, ps - 1.2f), ps * .12f);
        return artBmp;
    }

    // ---------- paint ----------
    protected override void OnPaint(PaintEventArgs e)
    {
        var g = e.Graphics; clip = e.ClipRectangle; if (ClientSize.Width <= 0) return;
        if (bg == null || bgDirty || bg.Width != ClientSize.Width || bg.Height != ClientSize.Height) BuildBg();
        g.CompositingMode = CompositingMode.SourceCopy; g.DrawImage(bg, clip, clip, GraphicsUnit.Pixel); g.CompositingMode = CompositingMode.SourceOver;
        g.SmoothingMode = SmoothingMode.AntiAlias; g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.ClearTypeGridFit; g.ScaleTransform(U, U);
        if (Dirty(rHdr)) DrawHeader(g);
        if (Dirty(rNow)) DrawNow(g);
        if (Dirty(rVis)) DrawVis(g);
        if (!rLyr.IsEmpty && Dirty(rLyr)) DrawLyr(g);
        if (Dirty(rPl)) DrawPl(g);
    }

    void Hov(Graphics g, Rectangle r, bool hot, bool danger) { if (hot) g.FillEllipse(Br(danger ? Color.FromArgb(70, 255, 120, 130) : Al(WH, 20)), r); }

    void DrawHeader(Graphics g)
    {
        Hov(g, rMenu, hid == 4, false); Ico(g, I_MENU, rMenu.X + 16, rMenu.Y + 16, 8, hid == 4 ? WH : TX);
        Txt(g, "THE WIRED MUSIC", fHdr, DM, 54, 15, 200);
        if (status.Length > 0) TxtIn(g, status, fS, DM, new RectangleF(250, 8, Math.Max(10, W - 250 - 130), 28), sfCC);
        Hov(g, rMin, hid == 1, false); Ico(g, I_MIN, rMin.X + 16, rMin.Y + 16, 6, hid == 1 ? WH : TX);
        Hov(g, rMax, hid == 2, false); Ico(g, I_MAX, rMax.X + 16, rMax.Y + 16, 6, hid == 2 ? WH : TX);
        Hov(g, rClose, hid == 3, true); Ico(g, I_CLOSE, rClose.X + 16, rClose.Y + 16, 6, hid == 3 ? WH : TX);
    }

    void DrawNow(Graphics g)
    {
        var T = cur >= 0 && cur < pl.Count ? pl[cur] : null;
        g.DrawImage(ArtOf(T, rArt.Width), rArt);
        float w = colR - colX;
        Txt(g, (T?.Artist ?? "").ToUpper(), fArt, ICE, colX, rNow.Y + 18, w);
        Txt(g, T?.Title ?? "Nothing playing", fTitle, T == null ? DM : WH, colX, rNow.Y + 34, w);
        string sub = T == null ? "" : (T.Album ?? "") + (!string.IsNullOrEmpty(T.Year) && !string.IsNullOrEmpty(T.Album) ? "  ·  " : "") + (T.Year ?? "");
        if (sub.Length > 0) Txt(g, sub, fS, DM, colX, rNow.Y + 72, w);

        double dur = durS, pos = dragSeek ? seekFrac * dur : posS; float fr = dur > 0 ? (float)Math.Min(1, pos / dur) : 0; int fw = (int)(rSeek.Width * fr);
        bool sh = hid == 17 || dragSeek;
        FillRR(g, Br(Al(WH, 24)), rSeek, 4);
        if (fw > 2) { FillRR(g, Br(Al(ICE, 50)), new RectangleF(rSeek.X, rSeek.Y - 2, fw, 8), 8); FillRR(g, Br(ICE), new RectangleF(rSeek.X, rSeek.Y, fw, 4), 4); }
        if (sh) g.FillEllipse(Br(ICE2), rSeek.X + fw - 6, rSeek.Y - 4, 12, 12);
        Txt(g, Fm(pos), fXs, DM, colX, rNow.Y + 110, 80);
        TxtIn(g, dur > 0 ? Fm(dur) : "", fXs, DM, new RectangleF(colR - 80, rNow.Y + 110, 80, 18), sfR);

        for (int i = 0; i < 5; i++)
        {
            var r = rb[i]; bool hot = hid == 10 + i; float cx = r.X + r.Width / 2f, cy = r.Y + r.Height / 2f;
            bool on = (i == 3 && rep) || (i == 4 && shuf);
            if (i == 1)
            {
                g.FillEllipse(Br(hot ? ICE2 : ICE), r); Ico(g, playing ? I_PAUSE : I_PLAY, cx, cy, 9, BG);
            }
            else
            {
                Hov(g, r, hot, false); var col = on ? ICE : (hot ? WH : TX);
                Ico(g, i == 0 ? I_PREV : i == 2 ? I_NEXT : i == 3 ? I_REP : I_SHUF, cx, cy, i == 0 || i == 2 ? 8 : 8.5f, col);
                if (on) g.FillEllipse(Br(ICE), cx - 1.5f, r.Bottom - 3, 3, 3);
            }
        }
        { var r = rb[5]; bool hot = hid == 15; Hov(g, r, hot, false); Ico(g, mute ? I_MUTE : I_VOL, r.X + 17, r.Y + 17, 8.5f, mute ? DM : (hot ? WH : TX)); }
        if (rVol.Width > 0)
        {
            int vw = (int)(rVol.Width * (mute ? 0 : vol));
            FillRR(g, Br(Al(WH, 24)), rVol, 4); if (vw > 2) FillRR(g, Br(ICE), new RectangleF(rVol.X, rVol.Y, vw, 4), 4);
            if (hid == 16 || dragVol) g.FillEllipse(Br(ICE2), rVol.X + vw - 5, rVol.Y - 3, 10, 10);
        }
    }

    void DrawVis(Graphics g)
    {
        var r = rVis; float cx = r.X + r.Width / 2f, cy = r.Y + r.Height / 2f, m = Math.Min(r.Width, r.Height), R0 = m * .2f, amp = m * .2f, t = Environment.TickCount / 1000f;
        var st = g.Save(); g.SetClip(new Rectangle(r.X + 1, r.Y + 1, r.Width - 2, r.Height - 2));
        for (int i = 0; i < 3; i++) { float rr = R0 * (2.2f - i * .45f) + amp * avg; g.FillEllipse(Br(Al(ICE, (int)(4 + i * 2 + flash * 9))), cx - rr, cy - rr, 2 * rr, 2 * rr); }
        for (int i = 1; i <= 3; i++) { float rr = R0 + amp * .4f * i + avg * amp * .2f; g.DrawEllipse(Pe(Al(ICE, 16), 1f), cx - rr, cy - rr, 2 * rr, 2 * rr); }
        float maxR = m * .5f - 6;
        for (int k = 0; k < shR.Length; k++) if (shA[k] > 0)
        {
            float rr = R0 + shR[k]; if (rr >= maxR) continue; float fade = 1 - shR[k] / Math.Max(1, maxR - R0);
            g.DrawEllipse(Pe(Al(ICE, (int)(shA[k] * 150 * fade)), 1.4f), cx - rr, cy - rr, 2 * rr, 2 * rr);
        }
        int ba = 36 + (int)(avg * 90);
        for (int i = 0; i < bx.Length; i++) { float x = r.X + bx[i] * r.Width + (float)Math.Sin(t * .7f + bph[i]) * 6, y = r.Y + by[i] * r.Height; g.DrawEllipse(Pe(Al(ICE, ba), 1f), x, y, bsz[i], bsz[i]); }
        float breathe = playing ? 0 : (float)Math.Sin(t * 1.2f) * 2f, rot = t * .08f;
        for (int k = 0; k < 96; k++)
        {
            int ix = k < 48 ? k : 95 - k; double an = k / 96.0 * Math.PI * 2 + rot - Math.PI / 2; float rr = R0 + 2 + bars[ix] * amp + flash * 4 + breathe;
            ringP[k] = new PointF(cx + (float)Math.Cos(an) * rr, cy + (float)Math.Sin(an) * rr);
        }
        g.FillClosedCurve(Br(Al(ICE, 22)), ringP, FillMode.Winding, .35f);
        g.DrawClosedCurve(Pe(Al(ICE, 34), 7f), ringP, .35f, FillMode.Winding);
        g.DrawClosedCurve(Pe(Al(ICE2, 235), 1.8f), ringP, .35f, FillMode.Winding);
        for (int k = 0; k < 128; k++)
        {
            double an = k / 128.0 * Math.PI * 2; float w = wave != null ? Math.Clamp(wave[k * 8] * amp * .6f, -amp * .4f, amp * .4f) : (float)Math.Sin(t * .5 + k * .35) * 1.2f; float rr = R0 * .62f + w;
            waveP[k] = new PointF(cx + (float)Math.Cos(an) * rr, cy + (float)Math.Sin(an) * rr);
        }
        g.DrawClosedCurve(Pe(Al(WH, 150), 1.2f), waveP, .3f, FillMode.Winding);
        g.DrawEllipse(Pe(Al(ICE2, (int)(flash * 200)), 1.5f), cx - 6 - flash * 12, cy - 6 - flash * 12, 12 + flash * 24, 12 + flash * 24);
        g.FillEllipse(Br(ICE2), cx - 3, cy - 3, 6, 6);
        g.Restore(st);
    }

    void DrawLyr(Graphics g)
    {
        var T = cur >= 0 && cur < pl.Count ? pl[cur] : null; if (T == null || string.IsNullOrWhiteSpace(T.Lyr)) return;
        var st = g.Save(); g.SetClip(new Rectangle(rLyr.X + 2, rLyr.Y + 2, rLyr.Width - 4, rLyr.Height - 4));
        g.DrawString(T.Lyr, fLyr, Br(Al(TX, 215)), new RectangleF(rLyr.X + 20, rLyr.Y + 18 - lyrY, rLyr.Width - 40, 6000), sfW);
        g.Restore(st);
    }

    void DrawPl(Graphics g)
    {
        if (pl.Count > 0) Txt(g, pl.Count + (pl.Count == 1 ? " track" : " tracks"), fXs, DM, rPl.X + 18, rPl.Y + 16, rPl.Width - 36);
        else TxtIn(g, "Drop music here", fRow, DM, new RectangleF(rPl.X, rList.Y, rPl.Width, rList.Height), sfCC);
        var st = g.Save(); g.SetClip(rList);
        int rows = Rows, hr = hid >= 100000 ? hid % 100000 : -1, dlX = rList.Right - 12 - 40 - 26;
        for (int i = 0; i < rows && scroll + i < pl.Count; i++)
        {
            int k = scroll + i, y = rList.Y + i * RowH; var tk = pl[k]; bool cu = k == cur;
            var rr = new RectangleF(rList.X, y + 1, rList.Width, RowH - 2);
            if (cu) FillRR(g, Br(Al(ICE, 28)), rr, 16); else if (k == hr) FillRR(g, Br(Al(WH, 12)), rr, 16);
            float x = rList.X + 12;
            if (cu) g.FillEllipse(Br(ICE), x + 2, y + RowH / 2f - 3, 6, 6); else Txt(g, (k + 1).ToString(), fXs, DM, x, y + 12, 24);
            float tx = x + 26, right = rList.Right - 12 - 40 - (tk.Url != null ? 26 : 0);
            Txt(g, tk.Title, fRow, cu ? WH : TX, tx, y + 4, right - tx); Txt(g, tk.Artist, fXs, DM, tx, y + 21, right - tx);
            if (tk.Dur > 0) TxtIn(g, Fm(tk.Dur), fXs, DM, new RectangleF(rList.Right - 12 - 40, y + 12, 40, 16), sfR);
            if (tk.Url != null) { bool h2 = hid == 200000 + k; if (tk.Saved) Ico(g, I_CHECK, dlX + 11, y + RowH / 2f, 5.5f, ICE); else Ico(g, I_DOWN, dlX + 11, y + RowH / 2f, 5.5f, h2 ? WH : DM); }
        }
        g.Restore(st);
        Pill(g, rBF, "+ Files", hid == 20, false); Pill(g, rBY, "+ Link", hid == 21, true); Pill(g, rDT, "↓ Song", hid == 22, false);
        Pill(g, rDA, dlBusy ? "■ Stop" : "↓ All", hid == 23, dlBusy);
    }
    void Pill(Graphics g, Rectangle r, string t, bool hot, bool acc)
    {
        FillRR(g, Br(Al(acc ? ICE : WH, hot ? (acc ? 50 : 28) : (acc ? 26 : 12))), r, 16);
        DrawRR(g, Pe(Al(acc ? ICE : WH, acc ? 90 : 28), 1f), new RectangleF(r.X + .5f, r.Y + .5f, r.Width - 1, r.Height - 1), 16);
        TxtIn(g, t, fBtn, acc ? ICE2 : TX, r, sfCC);
    }

    // ---------- input ----------
    Point V(Point p) { float u = U; return new Point((int)(p.X / u), (int)(p.Y / u)); }
    Point C(int x, int y) { float u = U; return new Point((int)(x * u), (int)(y * u)); }
    void Max() { MaximizedBounds = Screen.FromControl(this).WorkingArea; WindowState = WindowState == FormWindowState.Maximized ? FormWindowState.Normal : FormWindowState.Maximized; }
    int Hit(Point p)
    {
        if (rClose.Contains(p)) return 3; if (rMax.Contains(p)) return 2; if (rMin.Contains(p)) return 1; if (rMenu.Contains(p)) return 4;
        if (p.Y < HdrH) return 0;
        if (Rectangle.Inflate(rSeek, 0, 10).Contains(p)) return 17;
        if (rVol.Width > 0 && Rectangle.Inflate(rVol, 8, 10).Contains(p)) return 16;
        for (int i = 0; i < 6; i++) if (rb[i].Contains(p)) return 10 + i;
        if (rBF.Contains(p)) return 20; if (rBY.Contains(p)) return 21; if (rDT.Contains(p)) return 22; if (rDA.Contains(p)) return 23;
        if (rList.Contains(p)) { int k = scroll + (p.Y - rList.Y) / RowH; if (k < pl.Count) return (pl[k].Url != null && p.X > rList.Right - 12 - 40 - 28 && p.X < rList.Right - 12 - 40) ? 200000 + k : 100000 + k; }
        return 0;
    }
    void SeekTo(int x) { seekFrac = (float)Math.Clamp((x - rSeek.X) / (double)rSeek.Width, 0, .999); }
    void ApplySeek() { if (rd == null) return; try { rd.CurrentTime = TimeSpan.FromSeconds(rd.TotalTime.TotalSeconds * seekFrac); } catch { } }
    void SetVol(int x) { vol = Math.Clamp((x - rVol.X) / (float)Math.Max(1, rVol.Width), 0, 1); mute = false; Vol(); }
    void PickFiles() { using var d = new OpenFileDialog { Multiselect = true, Filter = "Audio|*.mp3;*.flac;*.wav;*.ogg;*.m4a;*.aac;*.wma" }; if (d.ShowDialog() == DialogResult.OK) Add(d.FileNames); }

    protected override void OnMouseDoubleClick(MouseEventArgs e) { var p = V(e.Location); if (p.Y < HdrH && Hit(p) == 0) Max(); }
    protected override void OnMouseDown(MouseEventArgs e)
    {
        var p = V(e.Location); if (e.Button != MouseButtons.Left) return; int id = Hit(p);
        if (p.Y < HdrH && id == 0) { ReleaseCapture(); SendMessage(Handle, 0xA1, 2, 0); return; }
        switch (id)
        {
            case 1: WindowState = FormWindowState.Minimized; return;
            case 2: Max(); return;
            case 3: Close(); return;
            case 4: ShowMenu(); return;
            case 17: dragSeek = true; SeekTo(p.X); Inv(rNow); return;
            case 16: dragVol = true; SetVol(p.X); Inv(rNow); return;
            case 10: Prev(); break; case 11: Toggle(); break; case 12: Next(); break;
            case 13: rep = !rep; break; case 14: shuf = !shuf; break; case 15: mute = !mute; Vol(); break;
            case 20: PickFiles(); return; case 21: OpenYt(); return;
            case 22: if (cur >= 0) Download(new List<Track> { pl[cur] }); return;
            case 23: if (dlBusy) StopDl(); else Download(pl.ToList()); return;
        }
        if (id >= 200000) Download(new List<Track> { pl[id - 200000] }); else if (id >= 100000) Play(id - 100000);
        Invalidate();
    }
    protected override void OnMouseMove(MouseEventArgs e)
    {
        mp = V(e.Location);
        if (dragSeek) { SeekTo(mp.X); Inv(rNow); }
        if (dragVol) { SetVol(mp.X); Inv(rNow); }
        int h = Hit(mp); if (h != hid) { hid = h; Cursor = h != 0 ? Cursors.Hand : Cursors.Default; Invalidate(); }
    }
    protected override void OnMouseLeave(EventArgs e) { base.OnMouseLeave(e); mp = new Point(-1, -1); if (hid != 0) { hid = 0; Invalidate(); } }
    protected override void OnMouseUp(MouseEventArgs e) { if (dragSeek) { dragSeek = false; ApplySeek(); Inv(rNow); } dragVol = false; }
    protected override void OnMouseWheel(MouseEventArgs e)
    {
        var p = V(e.Location);
        if (rPl.Contains(p)) { scroll = Math.Clamp(scroll - Math.Sign(e.Delta) * 3, 0, Math.Max(0, pl.Count - Rows)); Invalidate(); }
        else if (!rLyr.IsEmpty && rLyr.Contains(p) && cur >= 0)
        {
            using var gg = CreateGraphics(); float need = gg.MeasureString(pl[cur].Lyr ?? "", fLyr, (int)((rLyr.Width - 40) * U), sfW).Height / U;
            lyrY = (int)Math.Clamp(lyrY - Math.Sign(e.Delta) * 40, 0, Math.Max(0, need - rLyr.Height + 40)); Inv(rLyr);
        }
    }
    protected override void OnKeyDown(KeyEventArgs e)
    {
        if (e.Control && e.KeyCode == Keys.V && Clipboard.ContainsText() && Clipboard.GetText().Contains("youtu")) AddYt(Clipboard.GetText().Trim());
        else if (e.KeyCode == Keys.Space) { Toggle(); e.Handled = true; } else if (e.KeyCode == Keys.Right) Next(); else if (e.KeyCode == Keys.Left) Prev();
        Invalidate();
    }

    void ShowMenu()
    {
        var m = new ContextMenuStrip { BackColor = Color.FromArgb(10, 16, 22), ForeColor = TX, Font = new Font("Segoe UI", 9.5f), ShowImageMargin = false, Renderer = new ToolStripProfessionalRenderer(new DarkColors()) { RoundedEdges = false } };
        void Item(string t, Action a, bool chk = false) { var it = new ToolStripMenuItem(t) { Checked = chk, ForeColor = TX }; it.Click += (s, e) => { a(); Invalidate(); }; m.Items.Add(it); }
        void OpenDir() { using var d = new FolderBrowserDialog(); if (d.ShowDialog() == DialogResult.OK) Add(new[] { d.SelectedPath }); }
        Item("Open files...", PickFiles); Item("Open folder...", OpenDir); Item("Add YouTube link...", OpenYt); Item("Download all YouTube tracks...", () => Download(pl.ToList()));
        m.Items.Add(new ToolStripSeparator());
        Item("Shuffle", () => shuf = !shuf, shuf); Item("Repeat", () => rep = !rep, rep);
        m.Items.Add(new ToolStripSeparator());
        Item("Clear playlist", () => { Stop(); pl.Clear(); cur = -1; scroll = 0; posS = durS = 0; St(""); Relayout(); });
        Item("About", About); Item("Exit", Close);
        m.Show(this, C(rMenu.X, rMenu.Bottom + 2));
    }
}

class DarkColors : ProfessionalColorTable
{
    static readonly Color Bg = Color.FromArgb(10, 16, 22), Sel = Color.FromArgb(28, 52, 64), Bd = Color.FromArgb(44, 70, 84);
    public override Color ToolStripDropDownBackground => Bg;
    public override Color ImageMarginGradientBegin => Bg;
    public override Color ImageMarginGradientMiddle => Bg;
    public override Color ImageMarginGradientEnd => Bg;
    public override Color MenuBorder => Bd;
    public override Color MenuItemBorder => Sel;
    public override Color MenuItemSelected => Sel;
    public override Color MenuItemSelectedGradientBegin => Sel;
    public override Color MenuItemSelectedGradientEnd => Sel;
    public override Color SeparatorDark => Bd;
    public override Color SeparatorLight => Bg;
    public override Color CheckBackground => Sel;
    public override Color CheckSelectedBackground => Sel;
}
