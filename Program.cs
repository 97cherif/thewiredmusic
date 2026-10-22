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

class Track { public string Url, Path, Artist, Title, Album, Year = "", Lyr; public double Dur; public Image Art; }

class Wired : Form
{
    [DllImport("user32.dll")] static extern bool ReleaseCapture();
    [DllImport("user32.dll")] static extern IntPtr SendMessage(IntPtr h, int m, int w, int l);

    static readonly Color BG = Color.FromArgb(2, 13, 24), PN = Color.FromArgb(4, 24, 43), LN = Color.FromArgb(26, 111, 168),
        HI = Color.FromArgb(63, 194, 245), TX = Color.FromArgb(143, 216, 255), DM = Color.FromArgb(61, 134, 179), SEL = Color.FromArgb(27, 95, 156);
    static readonly string[] Ext = { ".mp3", ".flac", ".wav", ".ogg", ".m4a", ".aac", ".wma" };
    const string DefLyr = "どこにいても\nみんなつながっている\n\nNo matter where you are,\neveryone is always connected.";

    readonly List<Track> pl = new(); int cur = -1, scroll;
    WaveOutEvent wo; WaveStream rd; VolumeSampleProvider vsp; Tap tap; int gen;
    bool playing, shuf, rep, mute, crt = true, dragSeek, dragVol; float vol = .6f;
    readonly float[] bars = new float[48], sa = new float[300], sr = new float[300];
    string status = "NOT CONNECTED  -  drop files here or use File > Open";
    readonly Font F = new("Tahoma", 9f), FA = new("Tahoma", 12f), FT = new("Tahoma", 15f);

    readonly Rectangle rArt = new(20, 66, 130, 130), rSeek = new(20, 212, 620, 12), rVol = new(360, 255, 260, 6),
        rVis = new(6, 300, 318, 260), rLyr = new(330, 300, 320, 260), rPl = new(658, 58, 336, 502), rSt = new(6, 566, 988, 26);
    readonly int[] bx = { 48, 108, 168, 235, 275, 315 }, br = { 24, 24, 24, 16, 16, 16 };
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
    void Tx(Graphics g, string s, Font f, Color c, float x, float y) { using var b = new SolidBrush(c); g.DrawString(s, f, b, x, y); }
    void Pn(Graphics g, Rectangle r, string t)
    {
        using (var b = new SolidBrush(PN)) g.FillRectangle(b, r);
        using (var lb = new LinearGradientBrush(new Rectangle(r.X, r.Y, r.Width, 22), Color.FromArgb(11, 53, 88), Color.FromArgb(7, 34, 56), 90f)) g.FillRectangle(lb, r.X, r.Y, r.Width, 22);
        using var p = new Pen(LN); g.DrawRectangle(p, r); g.DrawLine(p, r.X, r.Y + 22, r.Right, r.Y + 22);
        Tx(g, t, F, TX, r.X + 6, r.Y + 4); Tx(g, "▢ ✕", F, TX, r.Right - 40, r.Y + 4);
    }

    protected override void OnPaint(PaintEventArgs e)
    {
        var g = e.Graphics; g.SmoothingMode = SmoothingMode.AntiAlias; g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.ClearTypeGridFit;
        var T = cur >= 0 ? pl[cur] : null;
        using (var lb = new LinearGradientBrush(ClientRectangle, Color.FromArgb(5, 27, 47), BG, 90f)) g.FillRectangle(lb, ClientRectangle);
        using (var p = new Pen(LN)) g.DrawRectangle(p, 0, 0, 999, 619);

        // title bar + menu
        using (var lb = new LinearGradientBrush(new Rectangle(0, 0, 1000, 28), Color.FromArgb(13, 58, 96), Color.FromArgb(8, 38, 64), 90f)) g.FillRectangle(lb, 0, 0, 1000, 28);
        using (var p = new Pen(HI)) { g.DrawEllipse(p, 8, 7, 14, 14); g.DrawLine(p, 8, 14, 22, 14); g.DrawLine(p, 15, 7, 15, 21); g.DrawRectangle(p, 926, 6, 18, 16); g.DrawRectangle(p, 948, 6, 18, 16); g.DrawRectangle(p, 970, 6, 18, 16); }
        Tx(g, "THE WIRED MUSIC.exe", FA, Color.White, 30, 5); Tx(g, "_", F, TX, 932, 5); Tx(g, "▢", F, TX, 951, 5); Tx(g, "x", F, TX, 976, 5);
        using (var p = new Pen(LN)) g.DrawLine(p, 0, 28, 1000, 28);
        for (int i = 0; i < 5; i++) Tx(g, menus[i], F, TX, MenuX(i), 34);

        // now playing
        if (T?.Art != null)
        {
            g.DrawImage(T.Art, rArt); using var tb = new SolidBrush(Color.FromArgb(95, 10, 90, 160)); g.FillRectangle(tb, rArt);
        }
        else
        {
            using (var lb = new LinearGradientBrush(rArt, Color.FromArgb(42, 139, 196), Color.FromArgb(4, 26, 48), 90f)) g.FillRectangle(lb, rArt);
            using var h = new SolidBrush(Color.FromArgb(11, 58, 95)); using var fc = new SolidBrush(Color.FromArgb(150, 79, 180, 230)); using var ey = new SolidBrush(Color.FromArgb(2, 18, 31));
            g.FillEllipse(h, 45, 78, 80, 100); g.FillEllipse(fc, 62, 100, 46, 58); g.FillEllipse(ey, 71, 122, 8, 8); g.FillEllipse(ey, 92, 122, 8, 8);
        }
        using (var p = new Pen(LN)) g.DrawRectangle(p, rArt);
        Tx(g, T?.Artist ?? "THE WIRED MUSIC", FA, Color.FromArgb(216, 242, 255), 165, 66);
        Tx(g, T?.Title ?? "no signal", FT, Color.White, 165, 88);
        Tx(g, T?.Album ?? "", F, DM, 165, 126); Tx(g, T?.Year ?? "", F, DM, 165, 144);
        double pos = rd?.CurrentTime.TotalSeconds ?? 0, dur = rd?.TotalTime.TotalSeconds ?? 0;
        Tx(g, $"{Fm(pos)} / {Fm(dur)}", FA, TX, 165, 172);
        using (var b = new SolidBrush(Color.FromArgb(79, 200, 248)))
            for (int k = 0; k < 48; k++) { float h = Math.Max(2, bars[k] * 46); g.FillRectangle(b, 410 + k * 4.8f, 196 - h, 3.6f, h); }

        // seek
        using (var b = new SolidBrush(Color.FromArgb(3, 17, 32))) g.FillRectangle(b, rSeek);
        float fr = dur > 0 ? (float)(pos / dur) : 0; int fw = (int)(rSeek.Width * fr);
        if (fw > 0) using (var lb = new LinearGradientBrush(rSeek, Color.FromArgb(127, 220, 255), Color.FromArgb(31, 143, 208), 90f)) g.FillRectangle(lb, rSeek.X, rSeek.Y, fw, rSeek.Height);
        using (var p = new Pen(LN)) g.DrawRectangle(p, rSeek);
        using (var b = new SolidBrush(Color.FromArgb(191, 234, 255))) g.FillRectangle(b, rSeek.X + fw - 4, rSeek.Y - 3, 8, 18);

        for (int i = 0; i < 6; i++) Btn(g, i);
        // volume
        using (var b = new SolidBrush(Color.FromArgb(13, 58, 96))) g.FillRectangle(b, rVol);
        using (var b = new SolidBrush(HI)) g.FillRectangle(b, rVol.X, rVol.Y, (int)(rVol.Width * vol), rVol.Height);
        using (var b = new SolidBrush(Color.FromArgb(191, 234, 255))) g.FillRectangle(b, rVol.X + (int)(rVol.Width * vol) - 3, rVol.Y - 4, 6, 14);

        // visualisation
        Pn(g, rVis, "Visualisation");
        var ir = new Rectangle(rVis.X + 1, rVis.Y + 23, rVis.Width - 2, rVis.Height - 24);
        g.SetClip(ir); using (var b = new SolidBrush(Color.FromArgb(2, 13, 26))) g.FillRectangle(b, ir);
        float cx = ir.X + ir.Width / 2f, cy = ir.Y + ir.Height / 2f, tm = Environment.TickCount / 1000f;
        for (int i = 0; i < 300; i++)
        {
            float r = sr[i], v = (float)Math.Sin(sa[i] + tm * (.15f + r * .3f)); float y = cy + v * ir.Height * .46f;
            float w = bars[(int)(Math.Abs(v) * 47)] * ir.Width * .45f + 4;
            using var b = new SolidBrush(Color.FromArgb((int)(70 + r * 150), (int)(80 + r * 120), (int)(190 + r * 60), 255));
            g.FillRectangle(b, cx + r * w, y, 2, 2); g.FillRectangle(b, cx - r * w, y, 2, 2);
        }
        g.ResetClip();

        // lyrics
        Pn(g, rLyr, "Lyrics");
        var lr = new RectangleF(rLyr.X + 14, rLyr.Y + 32, rLyr.Width - 28, rLyr.Height - 64);
        using (var b = new SolidBrush(TX)) g.DrawString(string.IsNullOrWhiteSpace(T?.Lyr) ? DefLyr : T.Lyr, FA, b, lr);
        using (var p = new Pen(Color.FromArgb(13, 58, 96))) g.DrawLine(p, rLyr.X, rLyr.Bottom - 22, rLyr.Right, rLyr.Bottom - 22);
        Tx(g, T != null ? T.Artist + " - " + T.Title : "", F, DM, rLyr.X + 6, rLyr.Bottom - 18); Tx(g, "1/1", F, DM, rLyr.Right - 30, rLyr.Bottom - 18);

        // playlist
        Pn(g, rPl, "Playlist");
        if (pl.Count == 0) Tx(g, "NO SIGNAL\n\nDrop files or folders here\nor use File > Open", F, DM, rPl.X + 20, rPl.Y + 50);
        int rows = (rPl.Height - 30) / 17;
        for (int i = 0; i < rows && scroll + i < pl.Count; i++)
        {
            int k = scroll + i, y = rPl.Y + 26 + i * 17; var tk = pl[k];
            if (k == cur) using (var b = new SolidBrush(SEL)) g.FillRectangle(b, rPl.X + 2, y, rPl.Width - 4, 17);
            var col = k == cur ? Color.White : TX;
            Tx(g, (k + 1).ToString("00"), F, DM, rPl.X + 8, y + 1);
            g.SetClip(new Rectangle(rPl.X + 32, y, rPl.Width - 92, 17)); Tx(g, tk.Artist + " - " + tk.Title, F, col, rPl.X + 34, y + 1); g.ResetClip();
            Tx(g, Fm(tk.Dur), F, DM, rPl.Right - 50, y + 1);
        }

        // status + taskbar
        using (var b = new SolidBrush(Color.FromArgb(3, 17, 32))) g.FillRectangle(b, rSt);
        using (var p = new Pen(LN)) g.DrawRectangle(p, rSt);
        if (T?.Art != null) g.DrawImage(T.Art, 9, 569, 20, 20);
        else using (var b = new SolidBrush(Color.FromArgb(11, 74, 120))) g.FillRectangle(b, 9, 569, 20, 20);
        Tx(g, status, F, DM, 38, 572);
        using (var b = new SolidBrush(Color.FromArgb(79, 200, 248))) for (int k = 0; k < 40; k++) { float h = Math.Max(1, bars[k] * 18); g.FillRectangle(b, 820 + k * 4, 589 - h, 3, h); }
        using (var lb = new LinearGradientBrush(new Rectangle(0, 596, 1000, 24), Color.FromArgb(11, 53, 88), Color.FromArgb(5, 35, 59), 90f)) g.FillRectangle(lb, 0, 596, 1000, 24);
        using (var b = new SolidBrush(Color.FromArgb(13, 74, 120))) g.FillRectangle(b, 6, 598, 150, 20);
        using (var p = new Pen(HI)) g.DrawRectangle(p, 6, 598, 150, 20);
        Tx(g, "THE WIRED MUSIC", F, Color.White, 20, 601);
        var tg = "WHERE MUSIC MEETS THE WIRED"; var sz = g.MeasureString(tg, F); Tx(g, tg, F, DM, 500 - sz.Width / 2, 601);
        Tx(g, DateTime.Now.ToString("HH:mm"), F, TX, 950, 601);

        if (crt) using (var p = new Pen(Color.FromArgb(46, 0, 0, 0))) for (int y = 0; y < 620; y += 3) g.DrawLine(p, 0, y, 1000, y);
    }

    void Btn(Graphics g, int i)
    {
        int cx = bx[i], cy = 258, r = br[i]; bool on = (i == 3 && rep) || (i == 4 && shuf) || (i == 5 && mute);
        var rc = new Rectangle(cx - r, cy - r, 2 * r, 2 * r);
        using (var gp = new GraphicsPath()) { gp.AddEllipse(rc); using var pb = new PathGradientBrush(gp) { CenterColor = Color.FromArgb(13, 74, 120), SurroundColors = new[] { Color.FromArgb(5, 35, 59) } }; g.FillEllipse(pb, rc); }
        using (var p = new Pen(on ? Color.White : HI, on ? 2.5f : 1f)) g.DrawEllipse(p, rc);
        var c = on ? Color.White : TX; using var b = new SolidBrush(c); using var ip = new Pen(c, 1.8f); float s = r * .45f;
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
                if (mute) { g.DrawLine(ip, cx + s * .7f, cy - s * .6f, cx + s * 1.4f, cy + s * .6f); } else g.DrawArc(ip, cx, cy - s * .6f, s * 1.2f, s * 1.2f, -60, 120); break;
        }
    }

    // ---------- input ----------
    int MenuX(int i) => new[] { 10, 56, 100, 175, 240 }[i];
    void Seek(int x) { if (rd == null) return; var f = Math.Clamp((x - rSeek.X) / (double)rSeek.Width, 0, .999); rd.CurrentTime = TimeSpan.FromSeconds(rd.TotalTime.TotalSeconds * f); }
    void SetVol(int x) { vol = Math.Clamp((x - rVol.X) / (float)rVol.Width, 0, 1); Vol(); }

    protected override void OnMouseDown(MouseEventArgs e)
    {
        var p = e.Location; if (e.Button != MouseButtons.Left) return;
        if (p.Y < 28)
        {
            if (new Rectangle(970, 6, 18, 16).Contains(p)) Close();
            else if (new Rectangle(926, 6, 18, 16).Contains(p)) WindowState = FormWindowState.Minimized;
            else { ReleaseCapture(); SendMessage(Handle, 0xA1, 2, 0); }
            return;
        }
        if (p.Y < 54) { for (int i = 4; i >= 0; i--) if (p.X >= MenuX(i) - 4) { ShowMenu(i); break; } return; }
        if (new Rectangle(rSeek.X, rSeek.Y - 6, rSeek.Width, rSeek.Height + 12).Contains(p)) { dragSeek = true; Seek(p.X); return; }
        if (new Rectangle(rVol.X - 6, rVol.Y - 8, rVol.Width + 12, 22).Contains(p)) { dragVol = true; SetVol(p.X); return; }
        for (int i = 0; i < 6; i++)
            if ((p.X - bx[i]) * (p.X - bx[i]) + (p.Y - 258) * (p.Y - 258) <= br[i] * br[i])
            { if (i == 0) Prev(); else if (i == 1) Toggle(); else if (i == 2) Next(); else if (i == 3) rep = !rep; else if (i == 4) shuf = !shuf; else { mute = !mute; Vol(); } return; }
        if (rPl.Contains(p) && p.Y > rPl.Y + 26) { int k = scroll + (p.Y - rPl.Y - 26) / 17; if (k < pl.Count) Play(k); }
    }
    protected override void OnMouseMove(MouseEventArgs e) { if (dragSeek) Seek(e.X); if (dragVol) SetVol(e.X); }
    protected override void OnMouseUp(MouseEventArgs e) { dragSeek = dragVol = false; }
    protected override void OnMouseWheel(MouseEventArgs e) { if (rPl.Contains(e.Location)) scroll = Math.Clamp(scroll - Math.Sign(e.Delta) * 3, 0, Math.Max(0, pl.Count - 1)); }
    protected override void OnKeyDown(KeyEventArgs e)
    {
        if (e.Control && e.KeyCode == Keys.V && Clipboard.ContainsText() && Clipboard.GetText().Contains("youtu")) AddYt(Clipboard.GetText().Trim()); else if (e.KeyCode == Keys.Space) Toggle(); else if (e.KeyCode == Keys.Right) Next(); else if (e.KeyCode == Keys.Left) Prev();
    }

    void ShowMenu(int i)
    {
        var m = new ContextMenuStrip { BackColor = PN, ForeColor = TX, Font = F };
        void A(string t, Action a) => m.Items.Add(t, null, (s, e) => a());
        void OpenFiles() { using var d = new OpenFileDialog { Multiselect = true, Filter = "Audio|*.mp3;*.flac;*.wav;*.ogg;*.m4a;*.aac;*.wma" }; if (d.ShowDialog() == DialogResult.OK) Add(d.FileNames); }
        void OpenDir() { using var d = new FolderBrowserDialog(); if (d.ShowDialog() == DialogResult.OK) Add(new[] { d.SelectedPath }); }
        switch (i)
        {
            case 0: A("Open files...", OpenFiles); A("Open folder...", OpenDir); A("Open YouTube link...", OpenYt); A("Exit", Close); break;
            case 1: A(crt ? "CRT scanlines: on" : "CRT scanlines: off", () => crt = !crt); break;
            case 2: A("Play / Pause", Toggle); A("Previous", Prev); A("Next", Next); A("Shuffle", () => shuf = !shuf); A("Repeat", () => rep = !rep); break;
            case 3: A("Add folder...", OpenDir); A("Add YouTube link...", OpenYt); A("Clear playlist", () => { Stop(); pl.Clear(); cur = -1; scroll = 0; status = "NOT CONNECTED"; }); break;
            case 4: A("About THE WIRED MUSIC", () => MessageBox.Show("THE WIRED MUSIC.exe\nwired.exe  build 1999.12\n\nWHERE MUSIC MEETS THE WIRED\n\nNO MATTER WHERE YOU ARE,\nEVERYONE IS ALWAYS CONNECTED.", "THE WIRED MUSIC", MessageBoxButtons.OK, MessageBoxIcon.Information)); break;
        }
        m.Show(this, new Point(MenuX(i) - 4, 52));
    }
}
