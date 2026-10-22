using System.Drawing;
using System.Drawing.Drawing2D;
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
    public float[] Snap() { lock (l) { var c = new float[buf.Length]; for (int i = 0; i < c.Length; i++) c[i] = buf[(pos + i) % buf.Length]; return c; } }
}

class Track { public string Url, Path, Artist, Title, Album, Year = "", Lyr; public double Dur; public Image Art; public bool Saved; }

class Wired : Form
{
    [DllImport("user32.dll")] static extern bool ReleaseCapture();
    [DllImport("user32.dll")] static extern IntPtr SendMessage(IntPtr h, int m, int w, int l);

    static readonly Color BG = Color.FromArgb(5, 6, 12), PN = Color.FromArgb(8, 12, 22), LN = Color.FromArgb(40, 72, 112),
        HI = Color.FromArgb(127, 233, 255), TX = Color.FromArgb(200, 215, 255), DM = Color.FromArgb(92, 112, 146), SEL = Color.FromArgb(22, 56, 96), RED = Color.FromArgb(255, 59, 92);
    static readonly string[] Ext = { ".mp3", ".flac", ".wav", ".ogg", ".m4a", ".aac", ".wma" };
    const string DefLyr = "どこにいても\nみんなつながっている\n\nNo matter where you are,\neveryone is always connected.";

    readonly List<Track> pl = new(); int cur = -1, scroll;
    WaveOutEvent wo; WaveStream rd; VolumeSampleProvider vsp; Tap tap; int gen;
    bool playing, shuf, rep, mute, crt = true, dragSeek, dragVol; float vol = .6f;
    readonly float[] bars = new float[48], sa = new float[300], sr = new float[300];
    string status = "NOT CONNECTED  -  drop files here or use File > Open";
    readonly Font F = new("Tahoma", 9f), FA = new("Tahoma", 10f), FT = new("Segoe UI", 17f), FM = new("Consolas", 9f), FD = new("Consolas", 24f, FontStyle.Bold);

    readonly Rectangle rArt = new(20, 86, 132, 132), rSeek = new(20, 234, 620, 6), rVol = new(372, 278, 230, 8), rA = new(8, 56, 640, 252),
        rVis = new(8, 318, 320, 240), rLyr = new(334, 318, 314, 240), rPl = new(656, 56, 336, 436), rSt = new(8, 566, 984, 24),
        rBF = new(656, 530, 108, 28), rDT = new(656, 496, 164, 28), rDA = new(826, 496, 166, 28), rBY = new(770, 530, 222, 28), rMin = new(918, 5, 22, 16), rMax = new(942, 5, 22, 16), rClose = new(966, 5, 22, 16);
    readonly Rectangle[] rb = { new(20, 260, 44, 44), new(70, 256, 52, 52), new(128, 260, 44, 44), new(190, 268, 32, 32), new(228, 268, 32, 32), new(266, 268, 32, 32) };
    readonly Random R = new(); int gl; Point mp; bool dlBusy;
    readonly string[] menus = { "File", "View", "Playback", "Library", "Help" };

    public Wired()
    {
        Text = "THE WIRED MUSIC.exe"; FormBorderStyle = FormBorderStyle.None; StartPosition = FormStartPosition.CenterScreen;
        ClientSize = new Size(1000, 620); AllowDrop = true; KeyPreview = true;
        SetStyle(ControlStyles.AllPaintingInWmPaint | ControlStyles.UserPaint | ControlStyles.OptimizedDoubleBuffer, true);
        var rn = new Random(7); for (int i = 0; i < 300; i++) { sa[i] = (float)rn.NextDouble() * 6.28f; sr[i] = (float)rn.NextDouble(); }
        DragEnter += (s, e) => e.Effect = DragDropEffects.Copy;
        DragDrop += (s, e) => Add((string[])e.Data.GetData(DataFormats.FileDrop));
        var t = new System.Windows.Forms.Timer { Interval = 33 };
        t.Tick += (s, e) => Tick(); t.Start();
        FormClosed += (s, e) => Stop();
    }

    // ---------- library ----------
    void Add(IEnumerable<string> paths)
    {
        var files = new List<string>();
        foreach (var p in paths)
            if (Directory.Exists(p)) files.AddRange(Directory.EnumerateFiles(p, "*.*", SearchOption.AllDirectories));
            else files.Add(p);
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
                if (tf.Tag.Pictures.Length > 0) t.Art = Image.FromStream(new MemoryStream(tf.Tag.Pictures[0].Data.Data));
            }
            catch { }
            var lrc = System.IO.Path.ChangeExtension(f, ".lrc");
            if (string.IsNullOrWhiteSpace(t.Lyr) && System.IO.File.Exists(lrc))
                t.Lyr = Regex.Replace(System.IO.File.ReadAllText(lrc), @"\[[^\]]*\]", "").Trim();
            pl.Add(t);
        }
        if (cur < 0 && pl.Count > 0) Play(0);
    }

    // ---------- playback ----------
    void Play(int i)
    {
        if (i < 0 || i >= pl.Count) return;
        Stop(); cur = i; ++gen;
        { int v0 = (rPl.Height - 30) / 17; if (cur < scroll) scroll = cur; if (cur >= scroll + v0) scroll = cur - v0 + 1; }
        if (pl[i].Url != null) { Tune(i, gen); return; }
        try
        {
            rd = Rd(pl[i].Path); vsp = new VolumeSampleProvider(rd.ToSampleProvider()) { Volume = mute ? 0 : vol }; tap = new Tap(vsp);
            wo = new WaveOutEvent(); wo.Init(tap.ToWaveProvider()); wo.Play(); playing = true;
            status = "Now Playing: " + pl[i].Artist + " - " + pl[i].Title;
        }
        catch (Exception ex) { status = "SIGNAL LOST: " + ex.Message; playing = false; }
        int vis = (rPl.Height - 30) / 17; if (cur < scroll) scroll = cur; if (cur >= scroll + vis) scroll = cur - vis + 1;
    }
    void Stop() { wo?.Dispose(); rd?.Dispose(); wo = null; rd = null; vsp = null; tap = null; playing = false; }
    void Toggle()
    {
        if (wo == null) { Play(cur < 0 ? 0 : cur); return; }
        if (playing) wo.Pause(); else wo.Play(); playing = !playing;
    }
    void Next() { if (pl.Count == 0) return; Play(shuf ? new Random().Next(pl.Count) : (cur + 1) % pl.Count); }
    void Prev() { if (pl.Count == 0) return; if (rd != null && rd.CurrentTime.TotalSeconds > 3) rd.CurrentTime = TimeSpan.Zero; else Play((cur - 1 + pl.Count) % pl.Count); }
    void Vol() { if (vsp != null) vsp.Volume = mute ? 0 : vol; }
    static WaveStream Rd(string s) => s.StartsWith("http") ? (WaveStream)new MediaFoundationReader(s) : new AudioFileReader(s);

    // ---------- YouTube (via yt-dlp, downloaded automatically on first use) ----------
    static async Task<string> Ytdlp(string args)
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
        using var p = System.Diagnostics.Process.Start(psi);
        var o = await p.StandardOutput.ReadToEndAsync(); await p.WaitForExitAsync(); return o;
    }
    static string Ask(string title)
    {
        using var f = new Form { Text = title, Width = 540, Height = 130, FormBorderStyle = FormBorderStyle.FixedDialog, StartPosition = FormStartPosition.CenterParent, MaximizeBox = false, MinimizeBox = false, BackColor = PN, ForeColor = TX };
        var tb = new TextBox { Left = 10, Top = 12, Width = 500 }; var ok = new Button { Text = "Connect", Left = 420, Top = 45, DialogResult = DialogResult.OK };
        f.Controls.Add(tb); f.Controls.Add(ok); f.AcceptButton = ok;
        return f.ShowDialog() == DialogResult.OK ? tb.Text.Trim() : null;
    }
    async void Download(List<Track> list)
    {
        list = list.Where(t => t.Url != null).ToList();
        if (list.Count == 0) { status = "Nothing to download - add a YouTube link first"; return; }
        if (dlBusy) { status = "A download is already running"; return; }
        using var d = new FolderBrowserDialog { Description = "Choose where to save the music" };
        if (d.ShowDialog() != DialogResult.OK) return;
        dlBusy = true; int ok = 0; var tpl = System.IO.Path.Combine(d.SelectedPath, "%(title)s.%(ext)s");
        for (int i = 0; i < list.Count; i++)
        {
            var t = list[i]; status = $"Downloading {i + 1}/{list.Count}: {t.Title}";
            try
            {
                var o = await Ytdlp($"-f \"bestaudio[ext=m4a]/bestaudio\" --no-playlist --no-warnings --no-simulate --print after_move:filepath -o \"{tpl}\" \"{t.Url}\"");
                var path = o.Trim().Split('\n').Last().Trim();
                if (System.IO.File.Exists(path)) { ok++; t.Saved = true; }
            }
            catch { }
        }
        dlBusy = false; status = $"Downloaded {ok}/{list.Count} to {d.SelectedPath}";
    }
    void OpenYt() { var u = Ask("Paste a YouTube video or playlist link"); if (!string.IsNullOrEmpty(u)) AddYt(u); }
    async void AddYt(string url)
    {
        status = "Connecting to the Wired...";
        try
        {
            var j = await Ytdlp($"-J --flat-playlist --no-warnings \"{url}\"");
            using var d = System.Text.Json.JsonDocument.Parse(j); var root = d.RootElement; int n = 0;
            string S(System.Text.Json.JsonElement e, string k) => e.TryGetProperty(k, out var v) && v.ValueKind == System.Text.Json.JsonValueKind.String ? v.GetString() : null;
            void One(System.Text.Json.JsonElement e, string ch)
            {
                var id = S(e, "id"); var title = S(e, "title"); if (id == null || (title != null && title.StartsWith("["))) return;
                pl.Add(new Track { Url = "https://www.youtube.com/watch?v=" + id, Title = title ?? "Untitled", Artist = S(e, "channel") ?? S(e, "uploader") ?? ch ?? "YouTube", Album = "YouTube",
                    Dur = e.TryGetProperty("duration", out var du) && du.ValueKind == System.Text.Json.JsonValueKind.Number ? du.GetDouble() : 0 }); n++;
            }
            if (root.TryGetProperty("entries", out var en)) { var pc = S(root, "uploader") ?? S(root, "channel"); foreach (var e in en.EnumerateArray()) One(e, pc); }
            else One(root, null);
            status = $"Linked {n} tracks from the Wired"; if (cur < 0 && pl.Count > 0) Play(0);
        }
        catch (Exception ex) { status = "SIGNAL LOST: " + ex.Message; }
    }
    void Tune(int i, int my)
    {
        var t = pl[i]; status = "Tuning into the Wired...";
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
                        wo = new WaveOutEvent(); wo.Init(tap.ToWaveProvider()); wo.Play(); playing = true; status = "Now Playing: " + t.Artist + " - " + t.Title;
                    }
                    catch (Exception ex) { status = "SIGNAL LOST: " + ex.Message; }
                }));
            }
            catch (Exception ex) { BeginInvoke(new Action(() => { if (my == gen) status = "SIGNAL LOST: " + ex.Message; })); }
        });
    }

    void Tick()
    {
        if (wo != null && playing && wo.PlaybackState == PlaybackState.Stopped) { if (rep) Play(cur); else Next(); }
        var b = new float[48];
        if (playing && tap != null)
        {
            var s = tap.Snap(); var c = new Complex[1024];
            for (int i = 0; i < 1024; i++) { c[i].X = s[i] * (float)FastFourierTransform.HammingWindow(i, 1024); c[i].Y = 0; }
            FastFourierTransform.FFT(true, 10, c);
            for (int k = 0; k < 48; k++)
            {
                int a = (int)Math.Pow(511, k / 48.0) + 1, z = Math.Min(511, (int)Math.Pow(511, (k + 1) / 48.0) + 1); float m = 0;
                for (int j = a; j <= z; j++) m = Math.Max(m, (float)Math.Sqrt(c[j].X * c[j].X + c[j].Y * c[j].Y));
                b[k] = Math.Min(1, m * (1.5f + k * .12f));
            }
        }
        for (int k = 0; k < 48; k++) bars[k] = Math.Max(b[k], bars[k] * .88f);
        Invalidate();
    }

    // ---------- drawing ----------
    static string Fm(double s) => $"{(int)s / 60}:{(int)s % 60:00}";
    static Color A(Color c, int a) => Color.FromArgb(a, c);
    void Tx(Graphics g, string s, Font f, Color c, float x, float y) { using var b = new SolidBrush(c); g.DrawString(s, f, b, x, y); }
    void Ctr(Graphics g, string s, Font f, Color c, Rectangle r) { using var b = new SolidBrush(c); using var sf = new StringFormat { Alignment = StringAlignment.Center, LineAlignment = StringAlignment.Center }; g.DrawString(s, f, b, r, sf); }
    void Fill(Graphics g, Color c, Rectangle r) { using var b = new SolidBrush(c); g.FillRectangle(b, r); }
    void Ln(Graphics g, Color c, float x1, float y1, float x2, float y2, float w = 1) { using var p = new Pen(c, w); g.DrawLine(p, x1, y1, x2, y2); }
    void Brk(Graphics g, Rectangle r, Color c, int l = 9)
    {
        using var p = new Pen(c, 1.5f);
        g.DrawLines(p, new[] { new Point(r.X, r.Y + l), new Point(r.X, r.Y), new Point(r.X + l, r.Y) });
        g.DrawLines(p, new[] { new Point(r.Right - l, r.Y), new Point(r.Right, r.Y), new Point(r.Right, r.Y + l) });
        g.DrawLines(p, new[] { new Point(r.X, r.Bottom - l), new Point(r.X, r.Bottom), new Point(r.X + l, r.Bottom) });
        g.DrawLines(p, new[] { new Point(r.Right - l, r.Bottom), new Point(r.Right, r.Bottom), new Point(r.Right, r.Bottom - l) });
    }
    void Pn(Graphics g, Rectangle r, string t, string tag)
    {
        Fill(g, A(PN, 235), r); using (var p = new Pen(LN)) g.DrawRectangle(p, r);
        Fill(g, A(HI, 20), new Rectangle(r.X + 1, r.Y + 1, r.Width - 1, 19)); Ln(g, LN, r.X, r.Y + 20, r.Right, r.Y + 20);
        Tx(g, t, FM, HI, r.X + 8, r.Y + 3); var sz = g.MeasureString(tag, FM); Tx(g, tag, FM, DM, r.Right - sz.Width - 8, r.Y + 3); Brk(g, r, HI);
    }
    void Bev(Graphics g, Rectangle r, bool hot, bool on, bool dn, Color? acc = null)
    {
        var ac = acc ?? HI;
        using (var lb = new LinearGradientBrush(r, Color.FromArgb(hot ? 36 : 24, hot ? 54 : 38, hot ? 88 : 62), Color.FromArgb(9, 14, 28), 90f)) g.FillRectangle(lb, r);
        var lt = dn ? Color.Black : Color.FromArgb(110, 150, 200); var dk = dn ? Color.FromArgb(110, 150, 200) : Color.Black;
        Ln(g, lt, r.X, r.Y, r.Right - 1, r.Y); Ln(g, lt, r.X, r.Y, r.X, r.Bottom - 1); Ln(g, dk, r.X, r.Bottom - 1, r.Right - 1, r.Bottom - 1); Ln(g, dk, r.Right - 1, r.Y, r.Right - 1, r.Bottom - 1);
        using var p = new Pen(on ? ac : A(ac, hot ? 210 : 90)); g.DrawRectangle(p, r.X + 2, r.Y + 2, r.Width - 5, r.Height - 5);
    }
    void WinBtn(Graphics g, Rectangle r, int k)
    {
        Bev(g, r, r.Contains(mp), false, false, k == 2 ? RED : (Color?)null);
        float cx = r.X + r.Width / 2f, cy = r.Y + r.Height / 2f;
        if (k == 0) Ln(g, Color.White, cx - 4, cy + 3, cx + 4, cy + 3);
        else if (k == 1) { using var p = new Pen(Color.White); g.DrawRectangle(p, cx - 4, cy - 4, 8, 7); }
        else { Ln(g, Color.White, cx - 4, cy - 4, cx + 4, cy + 4); Ln(g, Color.White, cx - 4, cy + 4, cx + 4, cy - 4); }
    }
    void Gl(Graphics g, int i, Rectangle r, Color c)
    {
        float cx = r.X + r.Width / 2f, cy = r.Y + r.Height / 2f, s = Math.Min(r.Width, r.Height) * .24f; using var b = new SolidBrush(c); using var ip = new Pen(c, 1.8f);
        switch (i)
        {
            case 0: g.FillRectangle(b, cx - s, cy - s, 3, 2 * s); g.FillPolygon(b, new[] { new PointF(cx + s, cy - s), new PointF(cx + s, cy + s), new PointF(cx - s + 3, cy) }); break;
            case 1:
                if (playing) { g.FillRectangle(b, cx - s, cy - s, s * .7f, 2 * s); g.FillRectangle(b, cx + s * .3f, cy - s, s * .7f, 2 * s); }
                else g.FillPolygon(b, new[] { new PointF(cx - s * .6f, cy - s), new PointF(cx - s * .6f, cy + s), new PointF(cx + s, cy) }); break;
            case 2: g.FillRectangle(b, cx + s - 3, cy - s, 3, 2 * s); g.FillPolygon(b, new[] { new PointF(cx - s, cy - s), new PointF(cx - s, cy + s), new PointF(cx + s - 3, cy) }); break;
            case 3: g.DrawArc(ip, cx - s, cy - s, 2 * s, 2 * s, 40, 280); g.FillPolygon(b, new[] { new PointF(cx + s + 3, cy - 1), new PointF(cx + s - 5, cy - 1), new PointF(cx + s - 1, cy - 7) }); break;
            case 4: g.DrawLine(ip, cx - s, cy + s, cx + s, cy - s); g.DrawLine(ip, cx - s, cy - s, cx + s, cy + s); break;
            case 5:
                g.FillPolygon(b, new[] { new PointF(cx - s, cy - s * .5f), new PointF(cx - s * .3f, cy - s * .5f), new PointF(cx + s * .4f, cy - s), new PointF(cx + s * .4f, cy + s), new PointF(cx - s * .3f, cy + s * .5f), new PointF(cx - s, cy + s * .5f) });
                if (mute) g.DrawLine(ip, cx + s * .7f, cy - s * .6f, cx + s * 1.4f, cy + s * .6f); else g.DrawArc(ip, cx, cy - s * .6f, s * 1.2f, s * 1.2f, -60, 120); break;
        }
    }

    protected override void OnPaint(PaintEventArgs e)
    {
        var g = e.Graphics; g.SmoothingMode = SmoothingMode.AntiAlias; g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.ClearTypeGridFit;
        var T = cur >= 0 ? pl[cur] : null; int now = Environment.TickCount; if (R.Next(250) == 0) gl = 4;
        g.Clear(BG);
        using (var gp = new GraphicsPath()) { gp.AddEllipse(450, -140, 800, 520); using var pb = new PathGradientBrush(gp) { CenterColor = A(HI, 34), SurroundColors = new[] { A(HI, 0) } }; g.FillPath(pb, gp); }
        using (var p = new Pen(A(HI, 10))) { for (int x = 0; x < 1000; x += 20) g.DrawLine(p, x, 0, x, 620); for (int y = 0; y < 620; y += 20) g.DrawLine(p, 0, y, 1000, y); }
        using (var p = new Pen(LN)) g.DrawRectangle(p, 0, 0, 999, 619);

        // title bar + menu
        using (var lb = new LinearGradientBrush(new Rectangle(0, 0, 1000, 26), Color.FromArgb(16, 30, 54), Color.FromArgb(6, 10, 20), 90f)) g.FillRectangle(lb, 0, 0, 1000, 26);
        using (var p = new Pen(HI, 1.5f)) { g.DrawEllipse(p, 7, 6, 14, 14); g.DrawEllipse(p, 11, 10, 6, 6); }
        int ca = gl > 0 ? 3 : 1; Tx(g, "THE WIRED MUSIC.exe", FA, A(RED, 170), 30 + ca, 5); Tx(g, "THE WIRED MUSIC.exe", FA, A(HI, 170), 30 - ca, 5); Tx(g, "THE WIRED MUSIC.exe", FA, Color.White, 30, 5);
        WinBtn(g, rMin, 0); WinBtn(g, rMax, 1); WinBtn(g, rClose, 2);
        Fill(g, A(PN, 220), new Rectangle(1, 26, 998, 24)); Ln(g, LN, 0, 50, 1000, 50);
        int hm = -1; if (mp.Y >= 26 && mp.Y < 50 && mp.X < 300) for (int i = 4; i >= 0; i--) if (mp.X >= MenuX(i) - 4) { hm = i; break; }
        for (int i = 0; i < 5; i++) { Tx(g, menus[i], F, i == hm ? Color.White : TX, MenuX(i), 31); if (i == hm) Ln(g, HI, MenuX(i), 46, MenuX(i) + 38, 46); }

        // now playing
        Pn(g, rA, "NOW PLAYING", "LAYER 01 / PRESENT DAY, PRESENT TIME");
        if (T?.Art != null) { g.DrawImage(T.Art, rArt); Fill(g, Color.FromArgb(70, 0, 50, 110), rArt); }
        else
        {
            using (var lb = new LinearGradientBrush(rArt, Color.FromArgb(18, 40, 80), Color.FromArgb(4, 8, 18), 90f)) g.FillRectangle(lb, rArt);
            using (var p = new Pen(A(HI, 70))) for (int rr = 14; rr < 70; rr += 14) g.DrawEllipse(p, rArt.X + 66 - rr, rArt.Y + 66 - rr, 2 * rr, 2 * rr);
            Tx(g, "no image", FM, DM, rArt.X + 6, rArt.Bottom - 16);
        }
        g.SetClip(rArt);
        for (int k = 0; k < 50; k++) Fill(g, A(HI, R.Next(20, 70)), new Rectangle(R.Next(rArt.X, rArt.Right), R.Next(rArt.Y, rArt.Bottom), R.Next(2, 14), 1));
        using (var p = new Pen(Color.FromArgb(50, 0, 0, 0))) for (int y = rArt.Y; y < rArt.Bottom; y += 2) g.DrawLine(p, rArt.X, y, rArt.Right, y);
        g.ResetClip(); Brk(g, Rectangle.Inflate(rArt, 3, 3), HI, 12);
        Tx(g, (T?.Artist ?? "THE WIRED MUSIC").ToUpper(), FM, HI, 172, 86);
        g.SetClip(new Rectangle(172, 102, 466, 32)); Tx(g, T?.Title ?? "no signal", FT, Color.White, 170, 102); g.ResetClip();
        Tx(g, T?.Album ?? "", FM, DM, 172, 136); Tx(g, T?.Year ?? "", FM, DM, 172, 150);
        double pos = rd?.CurrentTime.TotalSeconds ?? 0, dur = rd?.TotalTime.TotalSeconds ?? 0; if (dur <= 0 && T != null) dur = T.Dur;
        Tx(g, Fm(pos), FD, A(HI, 90), 173, 177); Tx(g, Fm(pos), FD, Color.White, 172, 176); Tx(g, "/ " + Fm(dur), FM, DM, 262 + (Fm(pos).Length - 4) * 14, 188);
        for (int k = 0; k < 40; k++)
        {
            int n = (int)(bars[k] * 16);
            for (int s2 = 0; s2 < 16; s2++) Fill(g, s2 < n ? (s2 >= 14 ? RED : s2 >= 11 ? Color.FromArgb(225, 242, 255) : HI) : A(HI, 14), new Rectangle(400 + k * 6, 214 - s2 * 4, 5, 3));
        }

        // seek
        for (int k = 0; k <= 20; k++) Ln(g, A(HI, k % 5 == 0 ? 110 : 45), rSeek.X + k * 31, rSeek.Y - 6, rSeek.X + k * 31, rSeek.Y - (k % 5 == 0 ? 2 : 4));
        Fill(g, A(HI, 40), new Rectangle(rSeek.X, rSeek.Y + 2, rSeek.Width, 2)); float fr = dur > 0 ? (float)Math.Min(1, pos / dur) : 0; int fw = (int)(rSeek.Width * fr);
        Fill(g, HI, new Rectangle(rSeek.X, rSeek.Y + 1, fw, 4)); Fill(g, A(HI, 60), new Rectangle(rSeek.X, rSeek.Y - 1, fw, 8));
        Fill(g, Color.White, new Rectangle(rSeek.X + fw - 3, rSeek.Y - 5, 7, 16)); using (var p = new Pen(RED)) g.DrawRectangle(p, rSeek.X + fw - 3, rSeek.Y - 5, 6, 15);

        for (int i = 0; i < 6; i++)
        {
            bool on = (i == 3 && rep) || (i == 4 && shuf) || (i == 5 && mute);
            Bev(g, rb[i], rb[i].Contains(mp), on || (i == 1 && playing), false); Gl(g, i, rb[i], on ? Color.White : TX);
        }
        Tx(g, "VOL", FM, DM, 332, 274); for (int k = 0; k < 23; k++) Fill(g, k < vol * 23 ? (k > 19 ? RED : HI) : A(HI, 20), new Rectangle(rVol.X + k * 10, rVol.Y - (k * 5 / 23), 8, 8 + (k * 5 / 23)));
        Tx(g, ((int)(vol * 100)).ToString("00"), FM, TX, 608, 274);

        // visualisation
        Pn(g, rVis, "VISUALISATION", "SIGNAL");
        var ir = new Rectangle(rVis.X + 1, rVis.Y + 21, rVis.Width - 2, rVis.Height - 22); g.SetClip(ir); Fill(g, BG, ir);
        float cx = ir.X + ir.Width / 2f, cy = ir.Y + ir.Height / 2f, rot = now / 6000f, avg = bars.Average();
        using (var p = new Pen(A(HI, 28))) { for (int rr = 30; rr <= 130; rr += 20) g.DrawEllipse(p, cx - rr, cy - rr, 2 * rr, 2 * rr); g.DrawLine(p, ir.X, cy, ir.Right, cy); g.DrawLine(p, cx, ir.Y, cx, ir.Bottom); }
        using (var p = new Pen(HI, 2f))
            for (int k = 0; k < 48; k++)
            {
                double a2 = k / 48.0 * Math.PI * 2 + rot; float r0 = 34 + avg * 14, r1 = r0 + 4 + bars[k] * 75;
                g.DrawLine(p, cx + (float)Math.Cos(a2) * r0, cy + (float)Math.Sin(a2) * r0, cx + (float)Math.Cos(a2) * r1, cy + (float)Math.Sin(a2) * r1);
            }
        Fill(g, A(Color.White, 210), new Rectangle((int)cx - 3, (int)cy - 3, 6, 6));
        for (int k = 0; k < 30; k++) Fill(g, A(HI, R.Next(30, 120)), new Rectangle(R.Next(ir.X, ir.Right), R.Next(ir.Y, ir.Bottom), 1, 1));
        g.ResetClip(); Tx(g, "LVL " + avg.ToString("0.00"), FM, DM, ir.X + 8, ir.Bottom - 16);

        // lyrics
        Pn(g, rLyr, "LYRICS", "1/1");
        var lr = new RectangleF(rLyr.X + 14, rLyr.Y + 32, rLyr.Width - 28, rLyr.Height - 66);
        using (var b = new SolidBrush(TX)) g.DrawString(string.IsNullOrWhiteSpace(T?.Lyr) ? DefLyr : T.Lyr, FA, b, lr);
        Ln(g, LN, rLyr.X, rLyr.Bottom - 22, rLyr.Right, rLyr.Bottom - 22); Tx(g, T != null ? T.Artist + " - " + T.Title : "", FM, DM, rLyr.X + 8, rLyr.Bottom - 18);

        // playlist
        Pn(g, rPl, "PLAYLIST", pl.Count.ToString("00") + " ITEMS");
        if (pl.Count == 0) Tx(g, "NO SIGNAL\n\nDrop files or folders here,\nor press + ADD YT LINK", FM, DM, rPl.X + 20, rPl.Y + 50);
        int rows = (rPl.Height - 30) / 17;
        for (int i = 0; i < rows && scroll + i < pl.Count; i++)
        {
            int k = scroll + i, y = rPl.Y + 26 + i * 17; var tk = pl[k]; bool cu = k == cur;
            if (cu) { Fill(g, A(SEL, 210), new Rectangle(rPl.X + 2, y, rPl.Width - 4, 17)); Fill(g, RED, new Rectangle(rPl.X + 2, y, 3, 17)); }
            else if (new Rectangle(rPl.X, y, rPl.Width, 17).Contains(mp)) Fill(g, A(HI, 18), new Rectangle(rPl.X + 2, y, rPl.Width - 4, 17));
            Tx(g, (k + 1).ToString("00"), FM, cu ? HI : DM, rPl.X + 10, y + 1);
            g.SetClip(new Rectangle(rPl.X + 36, y, rPl.Width - 136, 17)); Tx(g, tk.Artist + " - " + tk.Title, F, cu ? Color.White : TX, rPl.X + 38, y + 1); g.ResetClip();
            if (tk.Url != null) { Tx(g, "YT", FM, RED, rPl.Right - 96, y + 1); Tx(g, tk.Saved ? "✓" : "↓", FM, tk.Saved ? HI : (new Rectangle(rPl.Right - 28, y, 24, 17).Contains(mp) ? Color.White : TX), rPl.Right - 24, y + 1); }
            Tx(g, Fm(tk.Dur), FM, DM, rPl.Right - 66, y + 1);
        }
        Bev(g, rBF, rBF.Contains(mp), false, false); Ctr(g, "+ FILES", FM, TX, rBF);
        Bev(g, rDT, rDT.Contains(mp), false, false); Ctr(g, "↓ THIS SONG", FM, TX, rDT);
        Bev(g, rDA, rDA.Contains(mp), dlBusy, false); Ctr(g, dlBusy ? "DOWNLOADING..." : "↓ DOWNLOAD ALL", FM, dlBusy ? RED : TX, rDA);
        Bev(g, rBY, rBY.Contains(mp), true, false, RED); Ctr(g, "+ ADD YT LINK", FM, Color.White, rBY);
        g.FillPolygon(new SolidBrush(RED), new[] { new PointF(rBY.X + 14, rBY.Y + 9), new PointF(rBY.X + 14, rBY.Y + 19), new PointF(rBY.X + 23, rBY.Y + 14) });

        // status ticker + taskbar
        Fill(g, A(BG, 230), rSt); using (var p = new Pen(LN)) g.DrawRectangle(p, rSt);
        Fill(g, playing && (now / 500) % 2 == 0 ? RED : A(RED, 50), new Rectangle(16, 574, 8, 8));
        string msg = "  " + status + "   ///   WHERE MUSIC MEETS THE WIRED   ///   NO MATTER WHERE YOU ARE, EVERYONE IS ALWAYS CONNECTED.   ///";
        float mw = g.MeasureString(msg, FM).Width, off = (now / 30) % mw;
        g.SetClip(new Rectangle(30, 567, 950, 22)); Tx(g, msg, FM, TX, 30 - off, 571); Tx(g, msg, FM, TX, 30 - off + mw, 571); g.ResetClip();
        using (var lb = new LinearGradientBrush(new Rectangle(0, 596, 1000, 24), Color.FromArgb(16, 30, 54), Color.FromArgb(6, 10, 20), 90f)) g.FillRectangle(lb, 0, 596, 1000, 24);
        Ln(g, LN, 0, 596, 1000, 596); Bev(g, new Rectangle(6, 598, 170, 20), false, true, true); Ctr(g, "THE WIRED MUSIC", FM, Color.White, new Rectangle(6, 598, 170, 20));
        var tgl = "WHERE MUSIC MEETS THE WIRED"; Tx(g, tgl, FM, DM, 500 - g.MeasureString(tgl, FM).Width / 2, 601);
        using (var p = new Pen(LN)) g.DrawRectangle(p, 926, 598, 66, 19); Tx(g, DateTime.Now.ToString("HH:mm"), FM, TX, 944, 601);

        if (gl > 0) { gl--; for (int k = 0; k < 4; k++) Fill(g, A(k % 2 == 0 ? HI : RED, 45), new Rectangle(R.Next(0, 300), R.Next(620), R.Next(200, 700), R.Next(2, 10))); }
        using (var p = new Pen(Color.FromArgb(48, 0, 0, 0))) for (int y = 0; y < 620; y += 3) g.DrawLine(p, 0, y, 1000, y);
        using (var gp = new GraphicsPath()) { gp.AddRectangle(new Rectangle(0, 0, 1000, 620)); using var pb = new PathGradientBrush(gp) { CenterColor = A(Color.Black, 0), SurroundColors = new[] { A(Color.Black, 150) }, FocusScales = new PointF(.82f, .82f) }; g.FillPath(pb, gp); }
    }

    // ---------- input ----------
    int MenuX(int i) => new[] { 10, 56, 100, 175, 240 }[i];
    void Seek(int x) { if (rd == null) return; var f = Math.Clamp((x - rSeek.X) / (double)rSeek.Width, 0, .999); rd.CurrentTime = TimeSpan.FromSeconds(rd.TotalTime.TotalSeconds * f); }
    void SetVol(int x) { vol = Math.Clamp((x - rVol.X) / (float)rVol.Width, 0, 1); Vol(); }
    void PickFiles() { using var d = new OpenFileDialog { Multiselect = true, Filter = "Audio|*.mp3;*.flac;*.wav;*.ogg;*.m4a;*.aac;*.wma" }; if (d.ShowDialog() == DialogResult.OK) Add(d.FileNames); }

    protected override void OnMouseDown(MouseEventArgs e)
    {
        var p = e.Location; if (e.Button != MouseButtons.Left) return;
        if (p.Y < 26)
        {
            if (rClose.Contains(p)) Close(); else if (rMin.Contains(p)) WindowState = FormWindowState.Minimized;
            else if (!rMax.Contains(p)) { ReleaseCapture(); SendMessage(Handle, 0xA1, 2, 0); }
            return;
        }
        if (p.Y < 50) { for (int i = 4; i >= 0; i--) if (p.X >= MenuX(i) - 4) { ShowMenu(i); break; } return; }
        if (Rectangle.Inflate(rSeek, 0, 8).Contains(p)) { dragSeek = true; Seek(p.X); return; }
        if (Rectangle.Inflate(rVol, 6, 8).Contains(p)) { dragVol = true; SetVol(p.X); return; }
        if (rDT.Contains(p)) { if (cur >= 0) Download(new List<Track> { pl[cur] }); return; }
        if (rDA.Contains(p)) { Download(pl.ToList()); return; }
        if (rBF.Contains(p)) { PickFiles(); return; }
        if (rBY.Contains(p)) { OpenYt(); return; }
        for (int i = 0; i < 6; i++)
            if (rb[i].Contains(p)) { if (i == 0) Prev(); else if (i == 1) Toggle(); else if (i == 2) Next(); else if (i == 3) rep = !rep; else if (i == 4) shuf = !shuf; else { mute = !mute; Vol(); } return; }
        if (rPl.Contains(p) && p.Y > rPl.Y + 26) { int k = scroll + (p.Y - rPl.Y - 26) / 17; if (k < pl.Count) { if (pl[k].Url != null && p.X > rPl.Right - 28) Download(new List<Track> { pl[k] }); else Play(k); } }
    }
    protected override void OnMouseMove(MouseEventArgs e) { mp = e.Location; if (dragSeek) Seek(e.X); if (dragVol) SetVol(e.X); }
    protected override void OnMouseUp(MouseEventArgs e) { dragSeek = dragVol = false; }
    protected override void OnMouseWheel(MouseEventArgs e) { if (rPl.Contains(e.Location)) scroll = Math.Clamp(scroll - Math.Sign(e.Delta) * 3, 0, Math.Max(0, pl.Count - 1)); }
    protected override void OnKeyDown(KeyEventArgs e)
    {
        if (e.Control && e.KeyCode == Keys.V && Clipboard.ContainsText() && Clipboard.GetText().Contains("youtu")) AddYt(Clipboard.GetText().Trim());
        else if (e.KeyCode == Keys.Space) Toggle(); else if (e.KeyCode == Keys.Right) Next(); else if (e.KeyCode == Keys.Left) Prev();
    }

    void ShowMenu(int i)
    {
        var m = new ContextMenuStrip { BackColor = PN, ForeColor = TX, Font = F };
        void A(string t, Action a) => m.Items.Add(t, null, (s, e) => a());
        void OpenFiles() { using var d = new OpenFileDialog { Multiselect = true, Filter = "Audio|*.mp3;*.flac;*.wav;*.ogg;*.m4a;*.aac;*.wma" }; if (d.ShowDialog() == DialogResult.OK) Add(d.FileNames); }
        void OpenDir() { using var d = new FolderBrowserDialog(); if (d.ShowDialog() == DialogResult.OK) Add(new[] { d.SelectedPath }); }
        switch (i)
        {
            case 0: A("Open files...", OpenFiles); A("Open folder...", OpenDir); A("Open YouTube link...", OpenYt); A("Download all YouTube tracks...", () => Download(pl.ToList())); A("Exit", Close); break;
            case 1: A(crt ? "CRT scanlines: on" : "CRT scanlines: off", () => crt = !crt); break;
            case 2: A("Play / Pause", Toggle); A("Previous", Prev); A("Next", Next); A("Shuffle", () => shuf = !shuf); A("Repeat", () => rep = !rep); break;
            case 3: A("Add folder...", OpenDir); A("Add YouTube link...", OpenYt); A("Clear playlist", () => { Stop(); pl.Clear(); cur = -1; scroll = 0; status = "NOT CONNECTED"; }); break;
            case 4: A("About THE WIRED MUSIC", () => MessageBox.Show("THE WIRED MUSIC.exe\nwired.exe  build 1999.12\n\nWHERE MUSIC MEETS THE WIRED\n\nNO MATTER WHERE YOU ARE,\nEVERYONE IS ALWAYS CONNECTED.", "THE WIRED MUSIC", MessageBoxButtons.OK, MessageBoxIcon.Information)); break;
        }
        m.Show(this, new Point(MenuX(i) - 4, 52));
    }
}
