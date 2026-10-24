using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Imaging;
using System.Runtime.InteropServices;
using System.Text.Json;
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

// Decodes ahead on its own thread so network/UI hiccups never reach the sound card (fixes audio stutter)
class Buffered : ISampleProvider, IDisposable
{
    readonly ISampleProvider src; readonly WaveStream rs; readonly float[] ring; readonly int rate, ch; int rp, wp, count; long consumed; double baseS;
    readonly object l = new(), rdl = new(); volatile bool stop, eof; readonly Thread th;
    public Buffered(WaveStream rs)
    {
        this.rs = rs; src = rs.ToSampleProvider(); rate = src.WaveFormat.SampleRate; ch = src.WaveFormat.Channels; ring = new float[rate * ch * 8];
        th = new Thread(Fill) { IsBackground = true, Priority = ThreadPriority.AboveNormal }; th.Start();
    }
    public WaveFormat WaveFormat => src.WaveFormat;
    public double PositionSeconds { get { lock (l) return baseS + consumed / (double)(rate * ch); } }
    void Fill()
    {
        var tmp = new float[Math.Max(4096, rate * ch / 4)];
        while (!stop)
        {
            bool room; lock (l) room = ring.Length - count >= tmp.Length;
            if (!room || eof) { Thread.Sleep(15); continue; }
            lock (rdl)
            {
                if (stop) break;
                int n; try { n = src.Read(tmp, 0, tmp.Length); } catch { n = 0; }
                if (n <= 0) { eof = true; continue; }
                lock (l) { for (int i = 0; i < n; i++) { ring[wp] = tmp[i]; if (++wp == ring.Length) wp = 0; } count += n; }
            }
        }
    }
    public int Read(float[] b, int o, int c)
    {
        int n;
        lock (l)
        {
            n = Math.Min(c, count);
            for (int i = 0; i < n; i++) { b[o + i] = ring[rp]; if (++rp == ring.Length) rp = 0; }
            count -= n; consumed += n;
        }
        if (n < c)
        {
            if (eof && n == 0) return 0;
            if (eof) return n;
            Array.Clear(b, o + n, c - n); return c; // buffer ran dry: play silence instead of stalling
        }
        return n;
    }
    public void Seek(double sec)
    {
        Task.Run(() => { lock (rdl) { try { rs.CurrentTime = TimeSpan.FromSeconds(sec); } catch { } lock (l) { rp = wp = count = 0; consumed = 0; baseS = sec; } eof = false; } });
    }
    public void Dispose() { stop = true; try { th.Join(800); } catch { } }
}

class PersistTrack { public string Url { get; set; } public string Path { get; set; } public string Title { get; set; } public string Artist { get; set; } public string Album { get; set; } public string Year { get; set; } public double Dur { get; set; } public bool Saved { get; set; } public string ArtUrl { get; set; } public bool Spot { get; set; } }
class PersistData { public List<PersistTrack> Tracks { get; set; } = new(); public int Cur { get; set; } = -1; public float Vol { get; set; } = .6f; public bool Shuf { get; set; } public bool Rep { get; set; } }

class Track { public string Url, Path, Artist, Title, Album, Year = "", Lyr; public double Dur; public Bitmap Art; public bool Saved, HadTitle, Real, Thumbing, Spot, LyrOff; public string ArtUrl; public List<(double t, string s)> Sync; public int LyrSt; /* 0 idle, 1 searching, 3 not found */ }
class LyData { public string Plain { get; set; } public string Synced { get; set; } }
class SpInfo { public string Kind, Name, Art; public List<Track> Tracks = new(); }

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
    static readonly Font fLyrBig = Fn("Segoe UI Semibold", 24), fLyrM = Fn("Segoe UI", 17);
    static readonly StringFormat sfWC = new() { Alignment = StringAlignment.Center, Trimming = StringTrimming.None };

    // ---------- state ----------
    readonly List<Track> pl = new(); int cur = -1, scroll, lyrY; float lyPos;
    WaveOutEvent wo; WaveStream rd; Buffered buf; VolumeSampleProvider vsp; Tap tap; int gen;
    bool playing, shuf, rep, mute, dragSeek, dragVol; float vol = .6f, seekFrac;
    readonly float[] bars = new float[48], spec = new float[48], snap = new float[1024], win = new float[1024];
    readonly Complex[] cpx = new Complex[1024];
    string status = ""; int statusEnd;
    readonly Random R = new(); bool dlBusy, dlCancel; System.Diagnostics.Process dlProc;
    double posS, durS; int last = Environment.TickCount, tickN; static bool ytUpdated;

    // ---------- layout (logical units; scaled by DPI) ----------
    float U => Math.Max(1f, DeviceDpi / 96f);
    int W = 1000, H = 620; const int RowH = 40, HdrH = 44;
    Rectangle rHdr, rMenu, rSearch, rClr, rMin, rMax, rClose, rNow, rVis, rLyr, rLyBtn, rPl, rList, rArt, rSeek, rVol, rTime, rBF, rBY, rBS, rDT, rDA;
    readonly Rectangle[] rb = new Rectangle[6]; // 0 prev 1 play 2 next 3 repeat 4 shuffle 5 mute
    int clrArm, colX, colR, hid; Point mp = new(-1, -1);
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
        DragDrop += (s, e) =>
        {
            if (e.Data.GetDataPresent(DataFormats.FileDrop)) Add((string[])e.Data.GetData(DataFormats.FileDrop));
            else if (e.Data.GetDataPresent(DataFormats.Text)) { var tx = ((string)e.Data.GetData(DataFormats.Text) ?? "").Trim(); if (IsSpotify(tx)) AddSpotify(tx); else if (tx.Contains("youtu")) AddYt(tx); }
        };
        var t = new System.Windows.Forms.Timer { Interval = 16 };
        t.Tick += (s, e) => Tick(); t.Start();
        FormClosed += (s, e) => Stop();
        FormClosing += (s, e) => SaveState();
        try { System.Runtime.GCSettings.LatencyMode = System.Runtime.GCLatencyMode.SustainedLowLatency; } catch { }
        try { System.Diagnostics.Process.GetCurrentProcess().PriorityClass = System.Diagnostics.ProcessPriorityClass.AboveNormal; } catch { }
        LoadState();
        Shown += (s, e) => { ReloadMeta(); UpdateYtdlp(); };
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
                var t = new Track { Path = f, Title = System.IO.Path.GetFileNameWithoutExtension(f), Artist = null };
                try
                {
                    using var tf = TagLib.File.Create(f);
                    if (!string.IsNullOrWhiteSpace(tf.Tag.Title)) { t.Title = tf.Tag.Title; t.HadTitle = true; }
                    t.Artist = tf.Tag.Performers.FirstOrDefault(x => !Unk(x)) ?? tf.Tag.AlbumArtists.FirstOrDefault(x => !Unk(x)) ?? tf.Tag.Composers.FirstOrDefault(x => !Unk(x));
                    t.Album = tf.Tag.Album ?? ""; t.Year = tf.Tag.Year > 0 ? tf.Tag.Year.ToString() : "";
                    t.Dur = tf.Properties.Duration.TotalSeconds; SetLyrics(t, tf.Tag.Lyrics);
                    if (tf.Tag.Pictures.Length > 0) { using var ms = new MemoryStream(tf.Tag.Pictures[0].Data.Data); using var im = Image.FromStream(ms); t.Art = Square(im, 320); }
                }
                catch { }
                if (t.Art == null) t.Art = FolderArt(f); t.Real = t.Art != null;
                Fix(t, f);
                try
                {
                    var lrc = System.IO.Path.ChangeExtension(f, ".lrc");
                    if (string.IsNullOrWhiteSpace(t.Lyr) && System.IO.File.Exists(lrc)) SetLyrics(t, System.IO.File.ReadAllText(lrc));
                }
                catch { }
                made.Add(t);
            }
            try
            {
                BeginInvoke(new Action(() =>
                {
                    Sibling(made); foreach (var t in made) { if (Unk(t.Artist)) t.Artist = "Unknown"; t.Art ??= RandomCover(); }
                    pl.AddRange(made); SaveState(); St(made.Count == 0 ? "No audio files found" : "", made.Count == 0 ? 4000 : 0);
                    if (cur < 0 && pl.Count > 0) Play(0); else Invalidate();
                }));
            }
            catch { }
        });
    }

    // ---------- artist recognition (works offline: tags, file name, folders, siblings, your corrections) ----------
    static readonly string[] Generic = { "music", "downloads", "download", "songs", "desktop", "documents", "mp3", "audio", "new folder", "users", "media", "my music", "playlist", "playlists", "itunes", "sounds", "tracks", "unknown", "favorites", "favourites", "windows", "temp", "videos" };
    static string OvFile => System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "TheWiredMusic", "artists.txt");
    static readonly Dictionary<string, string> ov = LoadOv();
    static Dictionary<string, string> LoadOv()
    {
        var d = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
        try { foreach (var l in System.IO.File.ReadAllLines(OvFile)) { var i = l.IndexOf('\t'); if (i > 0) d[l.Substring(0, i)] = l.Substring(i + 1); } } catch { }
        return d;
    }
    static bool Unk(string a) => string.IsNullOrWhiteSpace(a) || Regex.IsMatch(a.Trim(), @"^(unknown( artist)?|<unknown>|various( artists)?|va|n/?a|none|-)$", RegexOptions.IgnoreCase);
    static string CleanName(string n)
    {
        n = n.Replace('_', ' ');
        n = Regex.Replace(n, @"[\(\[\{][^\)\]\}]*(official|lyric|video|audio|hd|hq|4k|visuali[sz]er|remaster|clip|www\.|\.com|free download|explicit)[^\)\]\}]*[\)\]\}]", "", RegexOptions.IgnoreCase);
        n = Regex.Replace(n, @"^\s*\d{1,3}\s*[-\.\)]\s*", "");
        return Regex.Replace(n, @"\s{2,}", " ").Trim(' ', '-', '.');
    }
    static void Fix(Track t, string f)
    {
        lock (ov) if (ov.TryGetValue(f, out var o)) { t.Artist = o; return; }
        var n = CleanName(System.IO.Path.GetFileNameWithoutExtension(f)); var p = Regex.Split(n, @"\s+[-–—]\s+");
        if (p.Length >= 2 && p[0].Length > 0 && p[0].Length <= 50 && !Regex.IsMatch(p[0], @"^\d+$"))
        {
            if (Unk(t.Artist)) t.Artist = p[0].Trim();
            if (!t.HadTitle) t.Title = string.Join(" - ", p.Skip(1)).Trim();
        }
        else if (!t.HadTitle && n.Length > 0) t.Title = n;
    }
    static string FolderArtist(string dir, string album)
    {
        if (string.IsNullOrEmpty(dir)) return null;
        string Nm(string d) => string.IsNullOrEmpty(d) ? null : System.IO.Path.GetFileName(d.TrimEnd('\\', '/'));
        bool Gen(string n) => string.IsNullOrWhiteSpace(n) || Generic.Contains(n.Trim().ToLower());
        var name = Nm(dir); var pn = Nm(System.IO.Path.GetDirectoryName(dir));
        if (!string.IsNullOrWhiteSpace(album) && name != null && name.Equals(album.Trim(), StringComparison.OrdinalIgnoreCase) && !Gen(pn)) return pn.Replace('_', ' ').Trim();
        if (Gen(name)) return null;
        var m = Regex.Split(name, @"\s+[-–—]\s+"); return (m.Length >= 2 ? m[0] : name).Replace('_', ' ').Trim();
    }
    static void Sibling(List<Track> made)
    {
        foreach (var g in made.Where(x => x.Path != null).GroupBy(x => System.IO.Path.GetDirectoryName(x.Path) ?? ""))
        {
            var known = g.Where(x => !Unk(x.Artist)).Select(x => x.Artist).ToList(); string guess = null;
            if (known.Count > 0 && known.Distinct(StringComparer.OrdinalIgnoreCase).Count() == 1) guess = known[0];
            else if (known.Count == 0) guess = FolderArtist(g.Key, g.Select(x => x.Album).FirstOrDefault(a => !string.IsNullOrWhiteSpace(a)));
            if (guess != null) foreach (var x in g) if (Unk(x.Artist)) x.Artist = guess;
        }
    }
    static Track YtFix(Track t)
    {
        var title = Regex.Replace(t.Title ?? "", @"[\(\[][^\)\]]*(official|lyric|video|audio|visuali[sz]er|hd|hq|4k)[^\)\]]*[\)\]]", "", RegexOptions.IgnoreCase).Trim();
        var ch = Regex.Replace(t.Artist ?? "", @"\s*-\s*Topic$|VEVO$|\s*Official$", "", RegexOptions.IgnoreCase).Trim();
        var p = Regex.Split(title, @"\s+[-–—]\s+");
        if (p.Length >= 2 && p[0].Length <= 50) { t.Artist = p[0].Trim(); t.Title = string.Join(" - ", p.Skip(1)).Trim(); }
        else { t.Artist = ch.Length > 0 ? ch : "YouTube"; if (title.Length > 0) t.Title = title; }
        return t;
    }
    void SetArtist(int k)
    {
        if (k < 0 || k >= pl.Count) return; var t = pl[k];
        var a = Ask("Artist for: " + t.Title, Unk(t.Artist) ? "" : t.Artist); if (string.IsNullOrWhiteSpace(a)) return;
        t.Artist = a;
        if (t.Path != null) { lock (ov) { ov[t.Path] = a; try { System.IO.File.WriteAllLines(OvFile, ov.Select(x => x.Key + "\t" + x.Value)); } catch { } } }
        Invalidate();
    }

    // ---------- real cover art: embedded tag > image in the song's folder > YouTube thumbnail > your default covers ----------
    static readonly SemaphoreSlim thumbSem = new(4, 4);
    static Bitmap FolderArt(string f)
    {
        try
        {
            var dir = System.IO.Path.GetDirectoryName(f); if (dir == null) return null;
            var names = new List<string> { System.IO.Path.GetFileNameWithoutExtension(f), "cover", "folder", "front", "album", "albumart", "artwork", "thumb" };
            foreach (var n in names) foreach (var e in new[] { ".jpg", ".jpeg", ".png" })
            {
                var p = System.IO.Path.Combine(dir, n + e);
                if (System.IO.File.Exists(p)) { using var im = Image.FromFile(p); return Square(im, 320); }
            }
        }
        catch { }
        return null;
    }
    static Bitmap LoadThumb(string url)
    {
        var id = IdOf(url); if (id == null) return null;
        thumbSem.Wait();
        try
        {
            var f = System.IO.Path.Combine(CacheDir(), id + ".jpg");
            if (!System.IO.File.Exists(f))
            {
                using var h = new HttpClient { Timeout = TimeSpan.FromSeconds(15) };
                System.IO.File.WriteAllBytes(f, h.GetByteArrayAsync("https://i.ytimg.com/vi/" + id + "/hqdefault.jpg").GetAwaiter().GetResult());
            }
            using var im = Image.FromFile(f); int sq = (int)(im.Height * .75f); // cut off the black bars of the 4:3 thumbnail
            var b = new Bitmap(320, 320, PixelFormat.Format32bppPArgb); using var g = Graphics.FromImage(b); g.InterpolationMode = InterpolationMode.HighQualityBicubic;
            g.DrawImage(im, new Rectangle(0, 0, 320, 320), (im.Width - sq) / 2, (im.Height - sq) / 2, sq, sq, GraphicsUnit.Pixel); return b;
        }
        catch { return null; }
        finally { thumbSem.Release(); }
    }
    static Bitmap LoadArt(string url)
    {
        thumbSem.Wait();
        try
        {
            var f = System.IO.Path.Combine(CacheDir(), "sp_" + Convert.ToHexString(System.Security.Cryptography.SHA1.HashData(System.Text.Encoding.UTF8.GetBytes(url))).Substring(0, 16) + ".jpg");
            if (!System.IO.File.Exists(f))
            {
                using var h = new HttpClient { Timeout = TimeSpan.FromSeconds(15) };
                System.IO.File.WriteAllBytes(f, h.GetByteArrayAsync(url).GetAwaiter().GetResult());
            }
            using var im = Image.FromFile(f); return Square(im, 320);
        }
        catch { return null; }
        finally { thumbSem.Release(); }
    }
    void Thumb(Track t)
    {
        if (t.Real || t.Thumbing || t.Url == null) return; t.Thumbing = true;
        Task.Run(() =>
        {
            var bm = (t.ArtUrl != null ? LoadArt(t.ArtUrl) : null) ?? LoadThumb(t.Url);
            try { BeginInvoke(new Action(() => { t.Thumbing = false; if (bm != null) { t.Art = bm; t.Real = true; if (artFor == t) artFor = null; Invalidate(); } })); } catch { }
        });
    }

    // ---------- playback ----------
    void EnsureVisible() { int v = Rows; if (cur < scroll) scroll = cur; if (cur >= scroll + v) scroll = cur - v + 1; scroll = Math.Clamp(scroll, 0, Math.Max(0, pl.Count - v)); }
    void Play(int i)
    {
        if (i < 0 || i >= pl.Count) return;
        Stop(); cur = i; ++gen; Text = $"{pl[i].Artist} - {pl[i].Title}"; lyrY = 0; lyPos = 0; posS = 0; LoadLyCache(pl[i]); EnsureVisible(); Relayout();
        if (pl[i].Url != null) { Tune(i, gen); return; }
        try
        {
            rd = Rd(pl[i].Path); vsp = new VolumeSampleProvider(buf = new Buffered(rd)) { Volume = mute ? 0 : vol }; tap = new Tap(vsp);
            wo = new WaveOutEvent { DesiredLatency = 250, NumberOfBuffers = 3 }; wo.Init(tap.ToWaveProvider()); wo.Play(); playing = true; St("");
        }
        catch (Exception ex) { St("Couldn't play: " + ex.Message, 6000); playing = false; }
    }
    // dispose off the UI thread so switching tracks never stalls
    void Stop()
    {
        var w = wo; var r = rd; var bf = buf; wo = null; rd = null; buf = null; vsp = null; tap = null; playing = false;
        if (w != null || r != null) Task.Run(() => { try { bf?.Dispose(); } catch { } try { w?.Dispose(); } catch { } try { r?.Dispose(); } catch { } });
    }
    void Toggle()
    {
        if (wo == null) { Play(cur < 0 ? 0 : cur); return; }
        if (playing) wo.Pause(); else wo.Play(); playing = !playing;
    }
    void Next() { if (pl.Count == 0) return; Play(shuf ? R.Next(pl.Count) : (cur + 1) % pl.Count); }
    void Prev() { if (pl.Count == 0) return; if (buf != null && posS > 3) buf.Seek(0); else Play((cur - 1 + pl.Count) % pl.Count); }
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
    // one-time ffmpeg download (needed to convert to MP3)
    static readonly SemaphoreSlim ffLock = new(1, 1);
    static async Task<string> Ffmpeg(Action<string> say = null)
    {
        var dir = System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "TheWiredMusic"); Directory.CreateDirectory(dir);
        var exe = System.IO.Path.Combine(dir, "ffmpeg.exe");
        if (System.IO.File.Exists(exe)) return dir;
        await ffLock.WaitAsync(); // only one download at a time, others wait and reuse it
        try
        {
            if (System.IO.File.Exists(exe)) return dir;
            say?.Invoke("One-time setup: getting MP3 converter...");
            var zip = System.IO.Path.Combine(dir, "ffmpeg-" + Guid.NewGuid().ToString("N") + ".zip"); var tmp = exe + ".tmp";
            try
            {
                using (var h = new HttpClient { Timeout = TimeSpan.FromMinutes(20) })
                using (var rs = await h.GetStreamAsync("https://github.com/yt-dlp/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip"))
                using (var fs = System.IO.File.Create(zip)) await rs.CopyToAsync(fs);
                using (var za = System.IO.Compression.ZipFile.OpenRead(zip))
                {
                    var en = za.Entries.First(x => x.FullName.EndsWith("/bin/ffmpeg.exe"));
                    System.IO.Compression.ZipFileExtensions.ExtractToFile(en, tmp, true);
                }
                System.IO.File.Move(tmp, exe, true);
            }
            finally { try { System.IO.File.Delete(zip); } catch { } try { System.IO.File.Delete(tmp); } catch { } }
            try { foreach (var old in Directory.GetFiles(dir, "ffmpeg*.zip")) System.IO.File.Delete(old); } catch { }
            return dir;
        }
        finally { ffLock.Release(); }
    }
    static Button Flat(string t, int x, int y, Color c)
    {
        var b = new Button { Text = t, Left = x, Top = y, Width = 110, Height = 30, FlatStyle = FlatStyle.Flat, BackColor = Color.FromArgb(16, 26, 34), ForeColor = c, Font = new Font("Segoe UI", 9f), UseVisualStyleBackColor = false, Cursor = Cursors.Hand };
        b.FlatAppearance.BorderColor = Color.FromArgb(70, c.R, c.G, c.B); b.FlatAppearance.MouseOverBackColor = Color.FromArgb(26, 44, 56); return b;
    }
    static string Ask(string title, string init = "", string kind = null, string okText = "Add")
    {
        using var f = new Form { FormBorderStyle = FormBorderStyle.None, Size = new Size(580, 132), StartPosition = FormStartPosition.CenterParent, BackColor = Color.FromArgb(10, 16, 22), ShowInTaskbar = false };
        f.Paint += (s, e) => { e.Graphics.DrawRectangle(Pe(Al(ICE, 60), 1), 0, 0, f.Width - 1, f.Height - 1); using var fn = new Font("Segoe UI", 9.5f); e.Graphics.DrawString(title, fn, Br(DM), 16, 14); };
        var tb = new TextBox { Left = 16, Top = 44, Width = 548, BorderStyle = BorderStyle.FixedSingle, BackColor = BG, ForeColor = ICE2, Font = new Font("Segoe UI", 10.5f) };
        tb.Text = init; if (init.Length == 0 && Clipboard.ContainsText() && (kind == null ? (Clipboard.GetText().Contains("youtu") || Clipboard.GetText().Contains("spotify")) : Clipboard.GetText().Contains(kind))) tb.Text = Clipboard.GetText().Trim();
        var ok = Flat(okText, 340, 86, ICE); ok.DialogResult = DialogResult.OK; var no = Flat("Cancel", 456, 86, TX); no.DialogResult = DialogResult.Cancel;
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
        if (list.Count == 0) { St("Add an online song first", 4000); return; }
        if (dlBusy) { St("A download is already running", 4000); return; }
        using var d = new FolderBrowserDialog { Description = "Choose where to save the music" };
        if (d.ShowDialog() != DialogResult.OK) return;
        dlBusy = true; dlCancel = false; var t0 = DateTime.Now; int ok = 0; var tpl = System.IO.Path.Combine(d.SelectedPath, "%(title)s.%(ext)s");
        for (int i = 0; i < list.Count; i++)
        {
            if (dlCancel) break;
            var t = list[i]; St($"Downloading {i + 1}/{list.Count}: {t.Title}");
            if (t.Spot) { try { await RealUrl(t); } catch { continue; } if (dlCancel) break; }
            var nm = SafeName(t.Spot ? t.Artist + " - " + t.Title : t.Title);
            var cf = CachedFile(t.Url);
            if (cf != null)
            {
                try
                {
                    var dst = System.IO.Path.Combine(d.SelectedPath, nm + ".mp3");
                    System.IO.File.Copy(cf, dst, true); if (t.Spot) await Task.Run(() => TagSpotify(dst, t)); ok++; t.Saved = true; continue;
                }
                catch { }
            }
            try
            {
                var ff = await Ffmpeg(msg => St(msg));
                var tp2 = t.Spot ? System.IO.Path.Combine(d.SelectedPath, nm.Replace("%", "%%") + ".%(ext)s") : tpl;
                var o = await Ytdlp($"-f bestaudio -x --audio-format mp3 --audio-quality 0 --ffmpeg-location \"{ff}\" --no-playlist --no-warnings --no-simulate --print after_move:filepath -o \"{tp2}\" \"{t.Url}\"", p => dlProc = p);
                var path = o.Trim().Split('\n').Last().Trim();
                if (System.IO.File.Exists(path)) { if (t.Spot) await Task.Run(() => TagSpotify(path, t)); ok++; t.Saved = true; }
            }
            catch { }
        }
        if (dlCancel) { try { foreach (var f in Directory.GetFiles(d.SelectedPath)) if ((f.EndsWith(".part") || f.EndsWith(".ytdl")) && System.IO.File.GetLastWriteTime(f) >= t0.AddSeconds(-2)) System.IO.File.Delete(f); } catch { } }
        dlBusy = false; dlProc = null; St(dlCancel ? $"Stopped - {ok} song(s) kept" : $"Downloaded {ok}/{list.Count}", 6000); Invalidate();
    }
    void OpenYt() { var u = Ask("Paste a YouTube video or playlist link", "", "youtu"); if (string.IsNullOrEmpty(u)) return; if (IsSpotify(u)) St("That is a Spotify link - use the Spotify button", 5000); else AddYt(u); }
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
                pl.Add(YtFix(new Track { Url = "https://www.youtube.com/watch?v=" + id, Title = title ?? "Untitled", Artist = S(e, "channel") ?? S(e, "uploader") ?? ch ?? "YouTube", Album = "YouTube", Art = RandomCover(),
                    Dur = e.TryGetProperty("duration", out var du) && du.ValueKind == System.Text.Json.JsonValueKind.Number ? du.GetDouble() : 0 })); n++;
            }
            if (root.TryGetProperty("entries", out var en)) { var pc2 = S(root, "uploader") ?? S(root, "channel"); foreach (var e in en.EnumerateArray()) One(e, pc2); }
            else One(root, null);
            foreach (var y in pl.Where(x => x.Url != null).ToList()) Thumb(y); SaveState(); St($"Added {n} tracks", 4000); if (cur < 0 && pl.Count > 0) Play(0); else Invalidate();
        }
        catch (Exception ex) { St("Couldn't connect: " + ex.Message, 6000); }
    }
    // ---------- Spotify ----------
    // Spotify streams are DRM-protected, so (like spotDL) we read the song list from Spotify and play/download the matching audio from YouTube.
    static readonly Regex SpRx = new(@"(?:spotify\.com/(?:[^\s?#]*/)?|spotify:(?:user:[^:\s]+:)?)(track|album|playlist)[/:]([A-Za-z0-9]{22})", RegexOptions.IgnoreCase);
    static bool IsSpotify(string s) { s = s?.Trim() ?? ""; return s.Length < 400 && !s.Contains('\n') && (s.Contains("spotify.com/") || s.Contains("spotify.link/") || s.StartsWith("spotify:")); }
    static HttpClient SpHttp()
    {
        var h = new HttpClient { Timeout = TimeSpan.FromSeconds(20) };
        h.DefaultRequestHeaders.UserAgent.ParseAdd("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36");
        h.DefaultRequestHeaders.AcceptLanguage.ParseAdd("en-US,en;q=0.9"); return h;
    }
    static string JStr(JsonElement e, string k) => e.ValueKind == JsonValueKind.Object && e.TryGetProperty(k, out var v) && v.ValueKind == JsonValueKind.String ? v.GetString() : null;
    static double JNum(JsonElement e, string k) => e.ValueKind == JsonValueKind.Object && e.TryGetProperty(k, out var v) && v.ValueKind == JsonValueKind.Number ? v.GetDouble() : 0;
    static string SafeName(string s) { s = string.Concat((s ?? "").Select(c => System.IO.Path.GetInvalidFileNameChars().Contains(c) ? '_' : c)).Trim(); return s.Length == 0 ? "track" : s; }

    static Track SpTrack(string title, string artist, string album, double sec, string art)
    {
        title = (title ?? "").Trim(); artist = (artist ?? "").Replace('\u00a0', ' ').Trim();
        var q = (artist + " - " + title).Replace("\"", "").Replace("\\", "").Trim();
        return new Track { Spot = true, Url = "ytsearch1:" + q, Title = title, Artist = artist.Length > 0 ? artist : "Spotify", Album = string.IsNullOrEmpty(album) ? "Spotify" : album, Dur = sec, ArtUrl = art };
    }
    static string BestImg(JsonElement e)
    {
        string best = null; double bw = -1;
        void Scan(JsonElement arr)
        {
            if (arr.ValueKind != JsonValueKind.Array) return;
            foreach (var x in arr.EnumerateArray()) { var u = JStr(x, "url"); if (u == null) continue; double w = Math.Max(JNum(x, "width"), JNum(x, "maxWidth")); if (w >= bw) { bw = w; best = u; } }
        }
        if (e.TryGetProperty("coverArt", out var ca) && ca.ValueKind == JsonValueKind.Object && ca.TryGetProperty("sources", out var cs)) Scan(cs);
        if (best == null && e.TryGetProperty("visualIdentity", out var vi) && vi.ValueKind == JsonValueKind.Object && vi.TryGetProperty("image", out var im)) Scan(im);
        return best;
    }
    static void ParseEmbed(string json, SpInfo info)
    {
        using var d = JsonDocument.Parse(json);
        var ent = d.RootElement.GetProperty("props").GetProperty("pageProps").GetProperty("state").GetProperty("data").GetProperty("entity");
        info.Name = JStr(ent, "name") ?? JStr(ent, "title"); info.Art = BestImg(ent);
        if (info.Kind != "track" && ent.TryGetProperty("trackList", out var tl) && tl.ValueKind == JsonValueKind.Array)
        {
            foreach (var e in tl.EnumerateArray())
            {
                var title = JStr(e, "title"); if (string.IsNullOrWhiteSpace(title)) continue;
                info.Tracks.Add(SpTrack(title, JStr(e, "subtitle"), info.Kind == "album" ? info.Name : null, JNum(e, "duration") / 1000.0, info.Kind == "album" ? info.Art : null));
            }
        }
        else
        {
            string artists = null;
            if (ent.TryGetProperty("artists", out var ar) && ar.ValueKind == JsonValueKind.Array) artists = string.Join(", ", ar.EnumerateArray().Select(x => JStr(x, "name")).Where(x => !string.IsNullOrWhiteSpace(x)));
            artists ??= JStr(ent, "subtitle");
            var title = JStr(ent, "name") ?? JStr(ent, "title");
            if (!string.IsNullOrWhiteSpace(title)) info.Tracks.Add(SpTrack(title, artists, null, JNum(ent, "duration") / 1000.0, info.Art));
        }
    }
    // reads a Spotify song / album / playlist link (no account or keys needed)
    static async Task<SpInfo> SpFetch(string input)
    {
        input = input.Trim(); var m = SpRx.Match(input);
        using var http = SpHttp();
        if (!m.Success && input.Contains("spotify.link/")) // short share link: follow the redirect
        {
            var r = await http.GetAsync(input); m = SpRx.Match(r.RequestMessage.RequestUri.ToString());
            if (!m.Success) m = SpRx.Match(await r.Content.ReadAsStringAsync());
        }
        if (!m.Success) throw new Exception("that isn't a Spotify song, album or playlist link");
        string kind = m.Groups[1].Value.ToLower(), id = m.Groups[2].Value; var info = new SpInfo { Kind = kind };
        try
        {
            var html = await http.GetStringAsync($"https://open.spotify.com/embed/{kind}/{id}");
            var nd = Regex.Match(html, @"<script id=""__NEXT_DATA__""[^>]*>(.*?)</script>", RegexOptions.Singleline);
            if (nd.Success) ParseEmbed(nd.Groups[1].Value, info);
        }
        catch { info.Tracks.Clear(); }
        if (info.Tracks.Count == 0 && kind == "track") // fallback: the public page's meta tags
        {
            try
            {
                var page = await http.GetStringAsync($"https://open.spotify.com/track/{id}");
                string Og(string pr) { var x = Regex.Match(page, "<meta[^>]+property=\"" + pr + "\"[^>]+content=\"([^\"]*)\""); return x.Success ? System.Net.WebUtility.HtmlDecode(x.Groups[1].Value) : null; }
                var title = Og("og:title"); var parts = (Og("og:description") ?? "").Split('·').Select(x => x.Trim()).Where(x => x.Length > 0).ToList();
                if (!string.IsNullOrWhiteSpace(title) && parts.Count > 0) info.Tracks.Add(SpTrack(title, parts[0], parts.Count >= 4 ? parts[1] : null, 0, Og("og:image")));
            }
            catch { }
        }
        if (info.Tracks.Count == 0) throw new Exception("couldn't read it (is the playlist private?)");
        return info;
    }

    // finds the YouTube video that matches a Spotify song (closest length wins), then remembers it
    static string SpMapFile => System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "TheWiredMusic", "spmap.json");
    static readonly Dictionary<string, string> spMap = LoadSpMap();
    static Dictionary<string, string> LoadSpMap() { try { return JsonSerializer.Deserialize<Dictionary<string, string>>(System.IO.File.ReadAllText(SpMapFile)) ?? new(); } catch { return new(); } }
    static void SaveSpMap() { try { Dictionary<string, string> c; lock (spMap) c = new(spMap); Directory.CreateDirectory(System.IO.Path.GetDirectoryName(SpMapFile)); System.IO.File.WriteAllText(SpMapFile, JsonSerializer.Serialize(c)); } catch { } }
    // fast YouTube search straight over HTTP (about 0.3 s) - no yt-dlp process needed just to find the video
    static readonly HttpClient ytH = MakeYtHttp();
    static HttpClient MakeYtHttp()
    {
        var h = new HttpClient { Timeout = TimeSpan.FromSeconds(8) };
        h.DefaultRequestHeaders.UserAgent.ParseAdd("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36");
        h.DefaultRequestHeaders.AcceptLanguage.ParseAdd("en-US,en;q=0.9"); return h;
    }
    static async Task<List<(string id, double dur, string title, string ch)>> YtQuickSearch(string q)
    {
        var body = JsonSerializer.Serialize(new { context = new { client = new { clientName = "WEB", clientVersion = "2.20240620.05.00", hl = "en", gl = "US" } }, query = q, @params = "EgIQAQ==" });
        using var r = await ytH.PostAsync("https://www.youtube.com/youtubei/v1/search?prettyPrint=false", new StringContent(body, System.Text.Encoding.UTF8, "application/json"));
        r.EnsureSuccessStatusCode();
        using var d = JsonDocument.Parse(await r.Content.ReadAsStringAsync()); var res = new List<(string, double, string, string)>();
        void Walk(JsonElement e)
        {
            if (res.Count >= 8) return;
            if (e.ValueKind == JsonValueKind.Object)
            {
                if (e.TryGetProperty("videoRenderer", out var vr) && vr.ValueKind == JsonValueKind.Object)
                {
                    var id = JStr(vr, "videoId"); double du = 0;
                    if (vr.TryGetProperty("lengthText", out var lt) && lt.ValueKind == JsonValueKind.Object)
                    {
                        var tx = JStr(lt, "simpleText");
                        if (tx != null) foreach (var part in tx.Split(':')) { if (!int.TryParse(part, out var n)) { du = 0; break; } du = du * 60 + n; }
                    }
                    string Runs(string k) { if (vr.TryGetProperty(k, out var o) && o.ValueKind == JsonValueKind.Object && o.TryGetProperty("runs", out var rs) && rs.ValueKind == JsonValueKind.Array && rs.GetArrayLength() > 0) return JStr(rs[0], "text"); return null; }
                    if (id != null) res.Add((id, du, Runs("title"), Runs("ownerText") ?? Runs("longBylineText"))); return;
                }
                foreach (var pr in e.EnumerateObject()) Walk(pr.Value);
            }
            else if (e.ValueKind == JsonValueKind.Array) foreach (var x in e.EnumerateArray()) Walk(x);
        }
        Walk(d.RootElement); return res;
    }
    // while a lookup is running, anyone else asking for the same thing (play + background warm-up) shares it instead of starting another yt-dlp
    static readonly Dictionary<string, Task<string>> spJobs = new(), rsJobs = new();
    static Task<string> Once(Dictionary<string, Task<string>> d, string key, Func<Task<string>> f)
    {
        lock (d)
        {
            if (d.TryGetValue(key, out var t0)) return t0;
            var nt = f(); d[key] = nt;
            nt.ContinueWith(_ => { lock (d) if (d.TryGetValue(key, out var x) && x == nt) d.Remove(key); }, TaskScheduler.Default);
            return nt;
        }
    }
    static Task<string> RealUrl(Track t)
    {
        var u = t.Url; if (u == null || !u.StartsWith("ytsearch")) return Task.FromResult(u);
        lock (spMap) if (spMap.TryGetValue(u, out var c)) { t.Url = c; return Task.FromResult(c); }
        return Once(spJobs, u, () => RealUrlCore(t));
    }
    // scores each search result: length close to the Spotify length, official "Topic" audio, and not a live / cover / remix version unless the song itself is one
    static string PickYt(List<(string id, double dur, string title, string ch)> r, Track t)
    {
        string want = ((t.Title ?? "") + " " + (t.Artist ?? "")).ToLowerInvariant(), art = LyFirstArtist(t.Artist ?? "").ToLowerInvariant();
        string[] bad = { "live", "cover", "remix", "karaoke", "instrumental", "slowed", "sped up", "reverb", "nightcore", "8d", "acoustic", "reaction", "tutorial", "mashup", "loop", "hour" };
        string best = null; double bs = double.MinValue;
        for (int i = 0; i < r.Count; i++)
        {
            var x = r[i]; double sc = -i * 0.6;
            if (t.Dur > 0 && x.dur > 0) { var df = Math.Abs(x.dur - t.Dur); sc += df <= 2 ? 10 : df <= 5 ? 6 : df <= 10 ? 0 : -Math.Min(30, df); }
            var tl = (x.title ?? "").ToLowerInvariant(); var ch = (x.ch ?? "").ToLowerInvariant();
            if (ch.EndsWith("- topic")) sc += 6; else if (ch.Contains("vevo") || tl.Contains("official audio")) sc += 2;
            if (art.Length > 1 && (ch.Contains(art) || tl.Contains(art))) sc += 3;
            foreach (var b in bad) { var rx = @"\b" + Regex.Escape(b) + @"\b"; if (Regex.IsMatch(tl, rx) && !Regex.IsMatch(want, rx)) sc -= 12; }
            if (sc > bs) { bs = sc; best = x.id; }
        }
        return best;
    }
    static async Task<string> RealUrlCore(Track t)
    {
        var u = t.Url;
        var q = u.Substring(u.IndexOf(':') + 1).Replace("\"", "").Replace("\\", ""); string best = null;
        try
        {
            var ch = PickYt(await YtQuickSearch(q), t); if (ch != null) best = "https://www.youtube.com/watch?v=" + ch;
        }
        catch { }
        for (int attempt = 0; attempt < 2 && best == null; attempt++)
        {
            try
            {
                var j = await Ytdlp($"-J --flat-playlist --no-warnings \"ytsearch6:{q}\"");
                using var d = JsonDocument.Parse(j);
                if (d.RootElement.TryGetProperty("entries", out var en))
                {
                    string first = null, pick = null; double bd = 1e9;
                    foreach (var e in en.EnumerateArray())
                    {
                        var id = JStr(e, "id"); if (id == null) continue; first ??= id;
                        double du = JNum(e, "duration"); if (t.Dur > 0 && du > 0) { var df = Math.Abs(du - t.Dur); if (df < bd) { bd = df; pick = id; } }
                    }
                    var ch = pick != null && bd <= 8 ? pick : first;
                    if (ch != null) best = "https://www.youtube.com/watch?v=" + ch;
                }
            }
            catch { }
            if (best == null && attempt == 0 && !ytUpdated) { ytUpdated = true; try { await Ytdlp("-U"); } catch { } }
        }
        if (best == null) throw new Exception("couldn't find this song - check your internet");
        lock (spMap) spMap[u] = best; SaveSpMap(); t.Url = best; return best;
    }
    // writes title / artist / album / cover into the downloaded MP3
    static void TagSpotify(string path, Track t)
    {
        try
        {
            using var tf = TagLib.File.Create(path);
            tf.Tag.Title = t.Title; tf.Tag.Performers = new[] { t.Artist };
            if (!string.IsNullOrEmpty(t.Album) && t.Album != "Spotify") tf.Tag.Album = t.Album;
            if (t.ArtUrl != null)
            {
                using var h = new HttpClient { Timeout = TimeSpan.FromSeconds(15) };
                tf.Tag.Pictures = new TagLib.IPicture[] { new TagLib.Picture(new TagLib.ByteVector(h.GetByteArrayAsync(t.ArtUrl).GetAwaiter().GetResult())) };
            }
            tf.Save();
        }
        catch { }
    }
    void OpenSpotify()
    {
        var u = Ask("Paste a Spotify song, album or playlist link", "", "spotify", "Add");
        if (!string.IsNullOrEmpty(u)) AddSpotify(u);
    }
    // looks up the YouTube audio for the first songs in the background, so pressing play is (almost) instant
    void WarmSpotify(List<Track> ts)
    {
        var list = ts.Where(x => x.Spot && x.Url != null && x.Url.StartsWith("ytsearch")).Take(12).ToList(); if (list.Count == 0) return;
        int idx = -1;
        for (int w = 0; w < 2; w++)
            Task.Run(async () =>
            {
                while (true)
                {
                    int i = Interlocked.Increment(ref idx); if (i >= list.Count) break;
                    try { var yu = await RealUrl(list[i]); await Resolve(yu); } catch { }
                }
            });
    }
    async void AddSpotify(string url, bool dl = false)
    {
        St("Reading Spotify link...");
        try
        {
            var info = await SpFetch(url); int n = 0;
            foreach (var t in info.Tracks) { t.Art = RandomCover(); pl.Add(t); n++; }
            foreach (var t in info.Tracks) Thumb(t);
            WarmSpotify(info.Tracks); SaveState();
            St(info.Kind == "track" ? "Added 1 song" : $"Added {n} songs from {info.Name}" + (info.Kind == "playlist" && n >= 100 ? " (Spotify only shows the first 100)" : ""), 6000);
            if (cur < 0 && pl.Count > 0) Play(0); else Invalidate();
            if (dl) Download(info.Tracks);
        }
        catch (Exception ex) { St("Couldn't add Spotify link: " + (ex.Message ?? "").Split('\n')[0], 7000); }
    }

    // ---------- instant YouTube playback: stream now, build the MP3 cache in the background ----------
    static string CacheDir() { var d = System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "TheWiredMusic", "cache"); Directory.CreateDirectory(d); return d; }
    static string IdOf(string url) { var m = Regex.Match(url ?? "", @"v=([\w-]+)"); return m.Success ? m.Groups[1].Value : null; }
    static string CachedFile(string url) { var id = IdOf(url); if (id == null) return null; var f = System.IO.Path.Combine(CacheDir(), id + ".mp3"); return System.IO.File.Exists(f) ? f : null; }
    static readonly Dictionary<string, (string u, int t)> sc = new();
    static Task<string> Resolve(string url)
    {
        lock (sc) if (sc.TryGetValue(url, out var c) && Environment.TickCount - c.t < 1200000) return Task.FromResult(c.u);
        return Once(rsJobs, url, () => ResolveCore(url));
    }
    static async Task<string> ResolveCore(string url)
    {
        string u = null;
        for (int attempt = 0; attempt < 2; attempt++)
        {
            try { u = (await Ytdlp($"-f \"bestaudio[ext=m4a]/bestaudio\" -g --no-playlist --no-warnings \"{url}\"")).Trim().Split('\n')[0].Trim(); } catch { u = null; }
            if (u != null && u.StartsWith("http")) break;
            if (attempt == 0 && !ytUpdated) { ytUpdated = true; try { await Ytdlp("-U"); } catch { } } else break;
        }
        if (u == null || !u.StartsWith("http")) throw new Exception("couldn't get the song - check your internet");
        lock (sc) sc[url] = (u, Environment.TickCount); return u;
    }
    static readonly SemaphoreSlim cvLock = new(1, 1);
    static async Task CacheMp3(string url)
    {
        var id = IdOf(url); if (id == null || CachedFile(url) != null) return;
        await cvLock.WaitAsync();
        try
        {
            if (CachedFile(url) != null) return; var dir = CacheDir(); var ff = await Ffmpeg();
            await Ytdlp($"-f bestaudio -x --audio-format mp3 --audio-quality 0 --ffmpeg-location \"{ff}\" --no-playlist --no-warnings -o \"{System.IO.Path.Combine(dir, id)}.%(ext)s\" \"{url}\"");
        }
        catch { }
        finally { cvLock.Release(); }
    }
    void Prefetch()
    {
        if (shuf || pl.Count < 2 || cur < 0) return;
        for (int k = 1; k <= 3 && k < pl.Count; k++)
        {
            var n = pl[(cur + k) % pl.Count]; if (n.Url == null || CachedFile(n.Url) != null) continue;
            Task.Run(async () => { try { if (n.Spot) await RealUrl(n); await Resolve(n.Url); } catch { } });
        }
    }
    void StartStream(string src)
    {
        try
        {
            rd = Rd(src); vsp = new VolumeSampleProvider(buf = new Buffered(rd)) { Volume = mute ? 0 : vol }; tap = new Tap(vsp);
            wo = new WaveOutEvent { DesiredLatency = 250, NumberOfBuffers = 3 }; wo.Init(tap.ToWaveProvider()); wo.Play(); playing = true; St(""); Prefetch();
        }
        catch (Exception ex) { St("Couldn't play: " + ex.Message, 6000); }
    }
    void Tune(int i, int my)
    {
        var t = pl[i];
        if (t.Spot && t.Url.StartsWith("ytsearch")) // Spotify song: find the matching audio first, then play it
        {
            St("Loading...");
            Task.Run(async () =>
            {
                try { var yu = await RealUrl(t); try { await Resolve(yu); } catch { } BeginInvoke(new Action(() => { if (my == gen && i < pl.Count && pl[i] == t) Tune(i, my); })); }
                catch (Exception ex) { BeginInvoke(new Action(() => { if (my == gen) St("Couldn't play: " + ex.Message, 6000); })); }
            });
            return;
        }
        var local = CachedFile(t.Url);
        if (local != null) { StartStream(local); return; } // already converted: plays instantly from disk
        St("Loading...");
        Task.Run(async () =>
        {
            try
            {
                var u = await Resolve(t.Url);
                BeginInvoke(new Action(() => { if (my != gen) return; StartStream(u); _ = CacheMp3(t.Url); }));
            }
            catch (Exception ex) { BeginInvoke(new Action(() => { if (my == gen) St("Couldn't play: " + ex.Message, 6000); })); }
        });
    }

    // ---------- frame tick: audio analysis + animation only ----------
    void Tick()
    {
        // song ended? advance even when minimized or hidden (this must run before the drawing early-outs below)
        if (wo != null && playing && wo.PlaybackState == PlaybackState.Stopped) { if (rep) Play(cur); else Next(); return; }
        if (WindowState == FormWindowState.Minimized || ClientSize.Width <= 0) return;
        int now = Environment.TickCount; tickN++;
        if (statusEnd != 0 && now - statusEnd >= 0) { status = ""; statusEnd = 0; Inv(rHdr); }
        if (clrArm != 0 && now - clrArm >= 3000) { clrArm = 0; Inv(rClr); }
        // save CPU: animate slower when the window is in the background or nothing is playing
        if (ActiveForm != this) { if (tickN % 3 != 0) return; } else if (!playing && tickN % 2 != 0) return;
        float dt = Math.Clamp((now - last) / 1000f, .001f, .05f); last = now;
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
        try { posS = buf?.PositionSeconds ?? 0; durS = rd?.TotalTime.TotalSeconds ?? 0; } catch { }
        if (cur >= 0 && cur < pl.Count)
        {
            var ct0 = pl[cur];
            if (ct0.Url != null && ct0.Dur > 0) durS = ct0.Dur;             // online song: the real length from Spotify / YouTube
            else if (durS <= 0) durS = ct0.Dur;
            if (ct0.Dur <= 0 && durS > 0 && playing) { ct0.Dur = durS; Inv(rPl); } // length unknown until now: remember it for the list
        }
        Vis(dt); Inv(rVis); if (playing || dragSeek) Inv(rTime);
    }

    // ---------- visualiser state ----------
    float[] wave; float bassAvg, flash, beatCd, avg; int shI;
    readonly float[] shR = new float[6], shA = new float[6];
    readonly float[] bx = new float[48], by = new float[48], bv = new float[48], bsz = new float[48], bph = new float[48];
    readonly PointF[] surfP = new PointF[96];
    readonly float[] liq = new float[48], lvel = new float[48];
    void Vis(float dt)
    {
        if (!playing) wave = null;
        float bass = 0; for (int k = 0; k < 5; k++) bass += bars[k]; bass /= 5;
        if (beatCd > 0) beatCd -= dt;
        if (playing && beatCd <= 0 && bass > bassAvg * 1.3f + .06f) { beatCd = .22f; flash = 1; shR[shI] = 0; shA[shI] = 1; shI = (shI + 1) % shR.Length; for (int k = 0; k < 12; k++) lvel[k] += 3f * (1 - k / 12f); }
        bassAvg += (bass - bassAvg) * Math.Min(1, dt * 1.8f); flash *= (float)Math.Pow(.86, dt * 30);
        for (int k = 0; k < shR.Length; k++) if (shA[k] > 0) { shR[k] += dt * 150; shA[k] -= dt * 1.1f; }
        for (int k = 0; k < 48; k++) { float acc = (bars[k] - liq[k]) * 110f - lvel[k] * 9f; lvel[k] += acc * dt; liq[k] = Math.Clamp(liq[k] + lvel[k] * dt, -.15f, 1.4f); }
        float s = 0; for (int k = 0; k < 48; k++) s += bars[k]; avg = s / 48;
        for (int i = 0; i < bx.Length; i++) { by[i] -= bv[i] * dt * (.03f + avg * .3f + flash * .1f); if (by[i] < -.05f) { by[i] = 1.05f; bx[i] = (float)R.NextDouble(); } }
    }

    // ---------- layout ----------
    void Relayout()
    {
        float u = U; W = Math.Max(1, (int)(ClientSize.Width / u)); H = Math.Max(1, (int)(ClientSize.Height / u));
        rHdr = new Rectangle(0, 0, W, HdrH);
        rMenu = new Rectangle(10, 6, 32, 32); rSearch = new Rectangle(46, 6, 32, 32); rClose = new Rectangle(W - 44, 6, 32, 32); rMax = new Rectangle(W - 80, 6, 32, 32); rMin = new Rectangle(W - 116, 6, 32, 32);
        int pad = 20, top = 52, plw = Math.Clamp((int)(W * .3f), 320, 380);
        rPl = new Rectangle(W - pad - plw, top, plw, Math.Max(100, H - top - pad));
        int lw = rPl.X - 16 - pad;
        rNow = new Rectangle(pad, top, lw, 182);
        int vy = rNow.Bottom + 16, vh = Math.Max(80, H - pad - vy);
        rVis = new Rectangle(pad, vy, lw, vh); rLyr = Rectangle.Empty; rLyBtn = new Rectangle(rVis.Right - 16 - 156, rVis.Y + 14, 156, 28);
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
        int by0 = rPl.Bottom - 16 - 32, gap = 5, spw = 46, bw = (rPl.Width - 32 - spw - 4 * gap) / 4, bx0 = rPl.X + 16;
        rBF = new Rectangle(bx0, by0, bw, 32); rBY = new Rectangle(bx0 + (bw + gap), by0, bw, 32); rBS = new Rectangle(bx0 + 2 * (bw + gap), by0, spw, 32);
        rDT = new Rectangle(bx0 + 2 * (bw + gap) + spw + gap, by0, bw, 32); rDA = new Rectangle(bx0 + 3 * (bw + gap) + spw + gap, by0, bw, 32);
        rClr = new Rectangle(rPl.Right - 16 - 64, rPl.Y + 10, 64, 24);
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

    const int I_PREV = 0, I_PLAY = 1, I_PAUSE = 2, I_NEXT = 3, I_REP = 4, I_SHUF = 5, I_VOL = 6, I_MUTE = 7, I_MENU = 8, I_MIN = 9, I_MAX = 10, I_CLOSE = 11, I_DOWN = 12, I_CHECK = 13, I_SEARCH = 14;
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
            case I_SEARCH: g.DrawEllipse(p, cx - s * .85f, cy - s * .85f, s * 1.4f, s * 1.4f); g.DrawLine(p, cx + s * .3f, cy + s * .3f, cx + s * .9f, cy + s * .9f); break;
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
        Hov(g, rSearch, hid == 5, false); Ico(g, I_SEARCH, rSearch.X + 15, rSearch.Y + 15, 7.5f, hid == 5 ? WH : TX);
        Txt(g, "THE WIRED MUSIC", fHdr, DM, 92, 15, 200);
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

    float LiqAt(float idx)
    {
        idx = Math.Clamp(idx, 0, 46.999f); int i = (int)idx; float f = idx - i; return liq[i] * (1 - f) + liq[i + 1] * f;
    }
    void DrawVis(Graphics g)
    {
        var r = rVis; float t = Environment.TickCount / 1000f;
        var st = g.Save(); using (var cp = RR(new RectangleF(r.X + 1, r.Y + 1, r.Width - 2, r.Height - 2), 34)) g.SetClip(cp);
        float y0 = r.Y + r.Height * .56f, amp = r.Height * .36f, calm = 3f + avg * 9f;
        int N = Math.Min(95, Math.Max(24, r.Width / 12)); float tilt = (float)Math.Sin(t * .4f) * r.Height * .025f;
        float[] offs = { 0, 12, 26 }, fac = { 1f, .72f, .5f }; int[] alp = { 40, 32, 26 };
        for (int L = 2; L >= 0; L--)
        {
            for (int i = 0; i < N; i++)
            {
                float u = i / (float)(N - 1), d = Math.Abs(u - .5f) * 2f;
                float y = y0 + offs[L] * (r.Height / 350f) - LiqAt(d * 47f) * amp * fac[L] + tilt * (u - .5f) * 2f
                    + (float)Math.Sin(u * 8.2f + t * (.9f + L * .3f) + L * 2f) * calm + (float)Math.Sin(u * 17f - t * (1.4f + L * .2f) + L) * calm * .45f;
                surfP[i] = new PointF(r.X + u * r.Width, y);
            }
            using (var path = new GraphicsPath())
            {
                path.AddCurve(surfP, 0, N - 1, .4f); path.AddLine(surfP[N - 1].X, surfP[N - 1].Y, r.Right, r.Bottom + 2); path.AddLine(r.Right, r.Bottom + 2, r.X, r.Bottom + 2); path.CloseFigure();
                g.FillPath(Br(Al(L == 0 ? ICE : ICE2, alp[L] + (int)(flash * 14))), path);
            }
            if (L == 0) { g.DrawCurve(Pe(Al(ICE, 34), 7f), surfP, 0, N - 1, .4f); g.DrawCurve(Pe(Al(ICE2, 235), 1.8f), surfP, 0, N - 1, .4f); }
            else g.DrawCurve(Pe(Al(ICE, 70 - L * 18), 1.1f), surfP, 0, N - 1, .4f);
        }
        int ba = 36 + (int)(avg * 90);
        for (int i = 0; i < bx.Length; i++) { float x = r.X + bx[i] * r.Width + (float)Math.Sin(t * .7f + bph[i]) * 6, y = r.Y + by[i] * r.Height; if (y > y0 + 6) g.DrawEllipse(Pe(Al(ICE2, ba), 1f), x, y, bsz[i], bsz[i]); }
        DrawLyrics(g, r);
        g.Restore(st);
        DrawLyBtn(g);
    }

    // ---------- lyrics (searched only when you press "Search lyrics"; free LRCLIB database, no login) ----------
    static readonly Regex LrcTag = new(@"\[(\d{1,3}):(\d{1,2}(?:[.:]\d{1,3})?)\]");
    static List<(double t, string s)> ParseLrc(string lrc)
    {
        var res = new List<(double t, string s)>();
        foreach (var raw in (lrc ?? "").Split('\n'))
        {
            var line = raw.Trim('\r', ' '); var ms = LrcTag.Matches(line); if (ms.Count == 0) continue;
            var text = LrcTag.Replace(line, "").Trim();
            foreach (Match m in ms) res.Add((int.Parse(m.Groups[1].Value) * 60 + double.Parse(m.Groups[2].Value.Replace(':', '.'), System.Globalization.CultureInfo.InvariantCulture), text));
        }
        res.Sort((x, y) => x.t.CompareTo(y.t)); return res;
    }
    static void SetLyrics(Track t, string text)
    {
        if (string.IsNullOrWhiteSpace(text)) return;
        var sy = ParseLrc(text);
        if (sy.Count >= 3) { t.Sync = sy; t.Lyr = string.Join("\n", sy.Select(x => x.s)); }
        else t.Lyr = Regex.Replace(text, @"\[[^\]]*\]", "").Trim();
    }
    static void ApplyLyrics(Track t, string plain, string synced)
    {
        if (!string.IsNullOrWhiteSpace(synced)) SetLyrics(t, synced);
        if (t.Sync == null && !string.IsNullOrWhiteSpace(plain)) t.Lyr = plain.Trim();
    }
    static int LS(Track t) => (!string.IsNullOrWhiteSpace(t.Lyr) || t.Sync != null) ? 2 : t.LyrSt;
    static bool LyrShown(Track t) => LS(t) == 2 && !t.LyrOff;
    static string LyCache(Track t) => System.IO.Path.Combine(CacheDir(), "ly_" + Convert.ToHexString(System.Security.Cryptography.SHA1.HashData(System.Text.Encoding.UTF8.GetBytes(((t.Artist ?? "") + "|" + (t.Title ?? "")).ToLowerInvariant()))).Substring(0, 16) + ".json");
    static void LoadLyCache(Track t)
    {
        if (LS(t) == 2) return;
        try
        {
            var f = LyCache(t); if (!System.IO.File.Exists(f)) return;
            var d = JsonSerializer.Deserialize<LyData>(System.IO.File.ReadAllText(f)); if (d != null) ApplyLyrics(t, d.Plain, d.Synced);
        }
        catch { }
    }
    static string LyClean(string s)
    {
        s = Regex.Replace(s ?? "", @"\s*[\(\[][^\)\]]*(feat|ft\.|with|remaster|live|version|edit|mix|official|lyric|audio|video)[^\)\]]*[\)\]]", "", RegexOptions.IgnoreCase);
        s = Regex.Replace(s, @"\s+-\s+(remaster|live|.*version|.*mix|.*edit).*$", "", RegexOptions.IgnoreCase);
        return s.Trim();
    }
    static (string p, string s) BestLy(JsonElement arr, double dur, double maxDiff)
    {
        (string p, string s) best = (null, null); int bs = -1;
        if (arr.ValueKind != JsonValueKind.Array) return best;
        foreach (var e in arr.EnumerateArray())
        {
            string p = JStr(e, "plainLyrics"), s = JStr(e, "syncedLyrics"); if (string.IsNullOrWhiteSpace(p) && string.IsNullOrWhiteSpace(s)) continue;
            double du = JNum(e, "duration"); if (dur > 0 && du > 0 && Math.Abs(du - dur) > maxDiff) continue;
            int sc2 = (string.IsNullOrWhiteSpace(s) ? 0 : 2) + (dur > 0 && du > 0 && Math.Abs(du - dur) <= 3 ? 1 : 0);
            if (sc2 > bs) { bs = sc2; best = (p, s); }
        }
        return best;
    }
    static string LyFirstArtist(string a)
    {
        a = Regex.Replace(a ?? "", @"\s*-\s*topic$|\s*vevo$|\s*official$", "", RegexOptions.IgnoreCase).Trim();
        var parts = Regex.Split(a, @"\s*(?:,|;|&|\sfeat\.?\s|\sft\.?\s|\sx\s|\swith\s)\s*", RegexOptions.IgnoreCase);
        return parts.Length > 0 ? parts[0].Trim() : a;
    }
    static async Task<(string plain, string synced)> FetchLyrics(Track t)
    {
        using var h = new HttpClient { Timeout = TimeSpan.FromSeconds(12) };
        h.DefaultRequestHeaders.UserAgent.ParseAdd("TheWiredMusic/1.1 (https://github.com/thewiredmusic)"); h.DefaultRequestHeaders.Add("Lrclib-Client", "TheWiredMusic v1.1");
        string artist = (t.Artist ?? "").Trim(), title = (t.Title ?? "").Trim();
        if (Unk(artist) || artist == "YouTube" || artist == "Spotify") artist = "";
        bool alb = !string.IsNullOrWhiteSpace(t.Album) && t.Album != "YouTube" && t.Album != "Spotify";
        string E(string v) => Uri.EscapeDataString(v);
        int responses = 0; var sw = System.Diagnostics.Stopwatch.StartNew();
        async Task<JsonDocument> Get(string url) // retries once on network errors / server errors
        {
            for (int i = 0; i < 2 && sw.Elapsed.TotalSeconds < 35; i++)
            {
                try
                {
                    using var r = await h.GetAsync(url); responses++;
                    if (r.IsSuccessStatusCode) return JsonDocument.Parse(await r.Content.ReadAsStringAsync());
                    if ((int)r.StatusCode < 500 && (int)r.StatusCode != 429) return null;
                }
                catch { }
                await Task.Delay(400);
            }
            return null;
        }
        // every sensible way to read "artist + title": as given, cleaned, first artist only, "Artist - Title" split out of the title, title alone
        var cands = new List<(string a, string ti)>();
        void Cand(string a, string ti) { a = (a ?? "").Trim(); ti = (ti ?? "").Trim(); if (ti.Length == 0) return; if (!cands.Any(c => c.a.Equals(a, StringComparison.OrdinalIgnoreCase) && c.ti.Equals(ti, StringComparison.OrdinalIgnoreCase))) cands.Add((a, ti)); }
        var ct = LyClean(title); var fa = LyFirstArtist(artist);
        Cand(artist, title); Cand(artist, ct); Cand(fa, ct);
        var dm = Regex.Match(ct, @"^(.{2,60}?)\s+[-–—]\s+(.+)$");
        if (dm.Success) { Cand(dm.Groups[1].Value, dm.Groups[2].Value); Cand(LyFirstArtist(dm.Groups[1].Value), LyClean(dm.Groups[2].Value)); }
        if (t.Dur > 0) Cand("", ct);
        bool first = true;
        foreach (var (a, ti) in cands)
        {
            if (!first && responses == 0) break; first = false; // can't reach the server at all - no point trying more
            if (a.Length > 0)
            {
                using var d1 = await Get("https://lrclib.net/api/get?artist_name=" + E(a) + "&track_name=" + E(ti) + (alb ? "&album_name=" + E(t.Album) : "") + (t.Dur > 0 ? "&duration=" + (int)Math.Round(t.Dur) : ""));
                if (d1 != null) { var p1 = JStr(d1.RootElement, "plainLyrics"); var s1 = JStr(d1.RootElement, "syncedLyrics"); if (!string.IsNullOrWhiteSpace(p1) || !string.IsNullOrWhiteSpace(s1)) return (p1, s1); }
                using var d2 = await Get("https://lrclib.net/api/search?track_name=" + E(ti) + "&artist_name=" + E(a));
                if (d2 != null) { var b2 = BestLy(d2.RootElement, t.Dur, 30); if (!string.IsNullOrWhiteSpace(b2.p) || !string.IsNullOrWhiteSpace(b2.s)) return b2; }
                using var d3 = await Get("https://lrclib.net/api/search?q=" + E(a + " " + ti));
                if (d3 != null) { var b3 = BestLy(d3.RootElement, t.Dur, 12); if (!string.IsNullOrWhiteSpace(b3.p) || !string.IsNullOrWhiteSpace(b3.s)) return b3; }
            }
            else if (t.Dur > 0)
            {
                using var d4 = await Get("https://lrclib.net/api/search?q=" + E(ti));
                if (d4 != null) { var b4 = BestLy(d4.RootElement, t.Dur, 5); if (!string.IsNullOrWhiteSpace(b4.p) || !string.IsNullOrWhiteSpace(b4.s)) return b4; }
            }
        }
        // second source (plain text only) in case LRCLIB doesn't have the song
        foreach (var (a, ti) in cands.Where(c => c.a.Length > 0).Take(3))
        {
            using var d5 = await Get("https://api.lyrics.ovh/v1/" + E(a) + "/" + E(ti));
            var ly = d5 != null ? JStr(d5.RootElement, "lyrics") : null; if (!string.IsNullOrWhiteSpace(ly)) return (ly.Trim(), null);
        }
        if (responses == 0) throw new Exception("offline");
        return (null, null);
    }
    async void SearchLyrics(Track t)
    {
        if (t.LyrSt == 1) return; t.LyrSt = 1; t.LyrOff = false; Inv(rVis);
        try
        {
            var (p, sy) = await FetchLyrics(t);
            if (string.IsNullOrWhiteSpace(p) && string.IsNullOrWhiteSpace(sy)) t.LyrSt = 3;
            else
            {
                ApplyLyrics(t, p, sy); t.LyrSt = 2; lyrY = 0; lyPos = 0;
                try { System.IO.File.WriteAllText(LyCache(t), JsonSerializer.Serialize(new LyData { Plain = p, Synced = sy })); } catch { }
            }
        }
        catch { t.LyrSt = 4; }
        Inv(rVis);
    }
    void LyrClick()
    {
        if (cur < 0 || cur >= pl.Count) return; var t = pl[cur]; int st = LS(t);
        if (st == 2) { t.LyrOff = !t.LyrOff; lyrY = 0; } else if (st != 1) SearchLyrics(t);
        Inv(rVis);
    }
    void DrawLyBtn(Graphics g)
    {
        if (cur < 0 || cur >= pl.Count || rLyBtn.IsEmpty) return; var T = pl[cur]; int st = LS(T);
        Pill(g, rLyBtn, st == 1 ? "Searching..." : st == 2 ? (T.LyrOff ? "Show lyrics" : "Hide lyrics") : st == 3 ? "Not found - retry" : st == 4 ? "No connection - retry" : "Search lyrics", hid == 30, st == 2 && !T.LyrOff);
    }
    // drawn on top of the visualiser, inside its clip
    void DrawLyrics(Graphics g, Rectangle r)
    {
        var T = cur >= 0 && cur < pl.Count ? pl[cur] : null; if (T == null || !LyrShown(T)) return;
        g.FillRectangle(Br(Al(BG, 150)), r);
        if (T.Sync != null && T.Sync.Count > 0)
        {
            var sy = T.Sync; int idx = -1; double ps = posS + .1;
            for (int i = 0; i < sy.Count; i++) { if (sy[i].t <= ps) idx = i; else break; }
            lyPos += (idx - lyPos) * .16f; if (Math.Abs(idx - lyPos) < .002f) lyPos = idx;
            float cy = r.Y + r.Height * .5f, step = 40, rw = r.Width - 60;
            for (int k = Math.Max(0, (int)Math.Floor(lyPos) - 4); k <= Math.Min(sy.Count - 1, (int)Math.Ceiling(lyPos) + 4); k++)
            {
                float y = cy + (k - lyPos) * step, dist = Math.Abs(k - lyPos); if (y < r.Y - 20 || y > r.Bottom + 20) continue;
                bool on = k == idx; var txt = string.IsNullOrWhiteSpace(sy[k].s) ? "♪" : sy[k].s;
                int a = on ? 255 : (int)Math.Clamp(190 - dist * 55, 0, 190);
                var f = on && g.MeasureString(txt, fLyrBig).Width <= rw ? fLyrBig : fLyrM;
                var rc = new RectangleF(r.X + 30, y - 20, rw, 40);
                if (on) TxtIn(g, txt, f, Al(BG, 200), new RectangleF(rc.X + 1, rc.Y + 2, rc.Width, rc.Height), sfCC);
                TxtIn(g, txt, f, on ? Al(WH, a) : Al(TX, a), rc, sfCC);
            }
        }
        else
        {
            var st2 = g.Save(); g.SetClip(new Rectangle(r.X + 2, r.Y + 48, r.Width - 4, r.Height - 50), CombineMode.Intersect);
            g.DrawString(T.Lyr, fLyrM, Br(Al(TX, 230)), new RectangleF(r.X + 30, r.Y + 56 - lyrY, r.Width - 60, 6000), sfWC); g.Restore(st2);
        }
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
        if (pl.Count > 0)
        {
            Txt(g, pl.Count + (pl.Count == 1 ? " track" : " tracks"), fXs, DM, rPl.X + 18, rPl.Y + 16, rPl.Width - 100);
            bool arm = clrArm != 0 && Environment.TickCount - clrArm < 3000; Pill(g, rClr, arm ? "Sure?" : "Clear", hid == 24, arm);
        }
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
        Pill(g, rBF, "+ Files", hid == 20, false); Pill(g, rBY, "+ Link", hid == 21, true); DrawSpBtn(g); Pill(g, rDT, "↓ Song", hid == 22, false);
        Pill(g, rDA, dlBusy ? "■ Stop" : "↓ All", hid == 23, dlBusy);
    }
    // Spotify logo with a small link badge merged into its corner (adds a Spotify song / album / playlist by link)
    void DrawSpBtn(Graphics g)
    {
        bool hot = hid == 25; var G = Color.FromArgb(30, 215, 96); var r = rBS;
        FillRR(g, Br(Al(G, hot ? 64 : 30)), r, 16);
        DrawRR(g, Pe(Al(G, hot ? 190 : 120), 1f), new RectangleF(r.X + .5f, r.Y + .5f, r.Width - 1, r.Height - 1), 16);
        float x0 = r.X + r.Width / 2f - 5, y0 = r.Y + r.Height / 2f - 1.5f, R = 9.5f;
        g.FillEllipse(Br(G), x0 - R, y0 - R, R * 2, R * 2);
        var dk = Pe(Color.FromArgb(8, 22, 14), 1.9f);
        float[] rr = { 6.6f, 5.0f, 3.4f }, dy = { 3.4f, 4.4f, 5.4f };
        for (int i = 0; i < 3; i++) g.DrawArc(dk, x0 - rr[i], y0 + dy[i] - rr[i], rr[i] * 2, rr[i] * 2, 222, 96);
        float bx = x0 + 9.5f, by = y0 + 7.5f, BR = 7.2f;           // link badge, bottom-right of the logo
        g.FillEllipse(Br(Color.FromArgb(10, 16, 22)), bx - BR, by - BR, BR * 2, BR * 2);
        g.DrawEllipse(Pe(G, 1.1f), bx - BR, by - BR, BR * 2, BR * 2);
        var st = g.Save(); g.TranslateTransform(bx, by); g.RotateTransform(-45);
        var lp = Pe(hot ? WH : ICE2, 1.4f);
        DrawRR(g, lp, new RectangleF(-5.2f, -1.9f, 5.6f, 3.8f), 3.8f); DrawRR(g, lp, new RectangleF(-0.4f, -1.9f, 5.6f, 3.8f), 3.8f);
        g.Restore(st);
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
        if (rClose.Contains(p)) return 3; if (rMax.Contains(p)) return 2; if (rMin.Contains(p)) return 1; if (rMenu.Contains(p)) return 4; if (rSearch.Contains(p)) return 5;
        if (p.Y < HdrH) return 0;
        if (Rectangle.Inflate(rSeek, 0, 10).Contains(p)) return 17;
        if (rVol.Width > 0 && Rectangle.Inflate(rVol, 8, 10).Contains(p)) return 16;
        for (int i = 0; i < 6; i++) if (rb[i].Contains(p)) return 10 + i;
        if (rBF.Contains(p)) return 20; if (rBY.Contains(p)) return 21; if (rBS.Contains(p)) return 25; if (rDT.Contains(p)) return 22; if (rDA.Contains(p)) return 23;
        if (pl.Count > 0 && rClr.Contains(p)) return 24;
        if (cur >= 0 && cur < pl.Count && rLyBtn.Contains(p)) return 30;
        if (rList.Contains(p)) { int k = scroll + (p.Y - rList.Y) / RowH; if (k < pl.Count) return (pl[k].Url != null && p.X > rList.Right - 12 - 40 - 28 && p.X < rList.Right - 12 - 40) ? 200000 + k : 100000 + k; }
        return 0;
    }
    void SeekTo(int x) { seekFrac = (float)Math.Clamp((x - rSeek.X) / (double)rSeek.Width, 0, .999); }
    void ApplySeek() { if (rd == null || buf == null) return; try { double total = rd.TotalTime.TotalSeconds, d = durS > 0 ? durS : total; buf.Seek(Math.Max(0, Math.Min(total - 1, d * seekFrac))); } catch { } }
    void SetVol(int x) { vol = Math.Clamp((x - rVol.X) / (float)Math.Max(1, rVol.Width), 0, 1); mute = false; Vol(); }
    void PickFiles() { using var d = new OpenFileDialog { Multiselect = true, Filter = "Audio|*.mp3;*.flac;*.wav;*.ogg;*.m4a;*.aac;*.wma" }; if (d.ShowDialog() == DialogResult.OK) Add(d.FileNames); }

    protected override void OnMouseDoubleClick(MouseEventArgs e) { var p = V(e.Location); if (p.Y < HdrH && Hit(p) == 0) Max(); }
    protected override void OnMouseDown(MouseEventArgs e)
    {
        var p = V(e.Location); int id = Hit(p);
        if (e.Button == MouseButtons.Right) { if (id >= 100000) RowMenu(id % 100000); return; }
        if (e.Button != MouseButtons.Left) return;
        if (p.Y < HdrH && id == 0) { ReleaseCapture(); SendMessage(Handle, 0xA1, 2, 0); return; }
        switch (id)
        {
            case 1: WindowState = FormWindowState.Minimized; return;
            case 2: Max(); return;
            case 3: Close(); return;
            case 4: ShowMenu(); return;
            case 5: OpenSearch(); return;
            case 30: LyrClick(); return;
            case 24: if (clrArm != 0 && Environment.TickCount - clrArm < 3000) { clrArm = 0; ClearAll(); } else clrArm = Environment.TickCount; Invalidate(); return;
            case 17: dragSeek = true; SeekTo(p.X); Inv(rNow); return;
            case 16: dragVol = true; SetVol(p.X); Inv(rNow); return;
            case 10: Prev(); break; case 11: Toggle(); break; case 12: Next(); break;
            case 13: rep = !rep; break; case 14: shuf = !shuf; break; case 15: mute = !mute; Vol(); break;
            case 20: PickFiles(); return; case 21: OpenYt(); return; case 25: OpenSpotify(); return;
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
        else if (rVis.Contains(p) && cur >= 0 && cur < pl.Count && LyrShown(pl[cur]) && pl[cur].Sync == null)
        {
            using var gg = CreateGraphics(); gg.ScaleTransform(U, U); float need = gg.MeasureString(pl[cur].Lyr ?? "", fLyrM, rVis.Width - 60, sfWC).Height;
            lyrY = (int)Math.Clamp(lyrY - Math.Sign(e.Delta) * 50, 0, Math.Max(0, need - (rVis.Height - 70) + 24)); Inv(rVis);
        }
    }
    protected override void OnKeyDown(KeyEventArgs e)
    {
        if (e.Control && e.KeyCode == Keys.F) { OpenSearch(); e.SuppressKeyPress = true; }
        else if (e.Control && e.KeyCode == Keys.V && Clipboard.ContainsText() && IsSpotify(Clipboard.GetText())) AddSpotify(Clipboard.GetText().Trim());
        else if (e.Control && e.KeyCode == Keys.V && Clipboard.ContainsText() && Clipboard.GetText().Contains("youtu")) AddYt(Clipboard.GetText().Trim());
        else if (e.KeyCode == Keys.Space) { Toggle(); e.Handled = true; } else if (e.KeyCode == Keys.Right) { if (e.Control) Next(); else SeekBy(5); }
        else if (e.KeyCode == Keys.Left) { if (e.Control) Prev(); else SeekBy(-5); }
        else if (e.KeyCode == Keys.L) LyrClick(); else if (e.KeyCode == Keys.N) Next(); else if (e.KeyCode == Keys.P) Prev();
        else if (e.KeyCode == Keys.Up) { vol = Math.Min(1, vol + .05f); mute = false; Vol(); }
        else if (e.KeyCode == Keys.Down) { vol = Math.Max(0, vol - .05f); Vol(); }
        else if (e.KeyCode == Keys.M) { mute = !mute; Vol(); } else if (e.KeyCode == Keys.S) shuf = !shuf; else if (e.KeyCode == Keys.R) rep = !rep;
        Invalidate();
    }

    // ---------- online search (YouTube via yt-dlp) ----------
    void OpenSearch()
    {
        // logical layout (scaled by DPI, same approach as the main window)
        const int DW = 680, DH = 520, PX = 20, PY = 108, PW = 640, PH = 344, RowS = 56, VY = PY + 4, VH = PH - 8;
        float u = U;
        using var f = new Form { FormBorderStyle = FormBorderStyle.None, AutoScaleMode = AutoScaleMode.None, StartPosition = FormStartPosition.CenterParent, BackColor = BG, ShowInTaskbar = false, KeyPreview = true, ClientSize = new Size((int)(DW * u), (int)(DH * u)) };
        var surf = new DBuf { Dock = DockStyle.Fill, BackColor = BG };
        f.Controls.Add(surf);
        using var fIn = Fn("Segoe UI", 15 * u);
        var fieldBg = Color.FromArgb(15, 25, 33);

        var rClose2 = new Rectangle(DW - 44, 6, 32, 32);
        var rField = new Rectangle(PX, 52, PW, 44);
        var rGo = new Rectangle(rField.Right - 8 - 92, rField.Y + 7, 92, 30);
        var rClr2 = new Rectangle(rGo.X - 34, rField.Y + 11, 22, 22);
        var rBDl = new Rectangle(PX + PW - 140, 468, 140, 32);
        var rBQ = new Rectangle(rBDl.X - 8 - 100, 468, 100, 32);
        var rBPlay = new Rectangle(rBQ.X - 8 - 92, 468, 92, 32);

        var tb = new TextBox
        {
            BorderStyle = BorderStyle.None, BackColor = fieldBg, ForeColor = ICE2, Font = fIn, MaxLength = 120, PlaceholderText = "Search YouTube songs, artists…",
            Left = (int)((PX + 46) * u), Width = (int)((rClr2.X - 6 - (PX + 46)) * u)
        };
        tb.Top = (int)((rField.Y + rField.Height / 2f) * u) - tb.Height / 2;
        surf.Controls.Add(tb);

        var results = new List<Track>(); var thumbs = new Dictionary<string, Bitmap>();
        Action after = null; Bitmap bgB = null; var anim = new System.Windows.Forms.Timer { Interval = 33 };
        string note = "", lastQ = "", eT = "Find something to play", eS = "Type a song or an artist, then press Enter"; bool busy = false, closed = false, eErr = false;
        int sel = -1, hv = 0, sgen = 0; float scrollY = 0;

        float MaxS() => Math.Max(0, results.Count * RowS - VH);
        void EnsVis() { float top = sel * RowS, bot = top + RowS; if (top < scrollY) scrollY = top; else if (bot > scrollY + VH) scrollY = bot - VH; scrollY = Math.Clamp(scrollY, 0, MaxS()); }
        Track Pick() => sel >= 0 && sel < results.Count ? results[sel] : null;

        int HitT(Point p)
        {
            if (rClose2.Contains(p)) return 1;
            if (!busy && rGo.Contains(p)) return 2;
            if (tb.Text.Length > 0 && rClr2.Contains(p)) return 3;
            if (sel >= 0 && rBPlay.Contains(p)) return 4;
            if (sel >= 0 && rBQ.Contains(p)) return 5;
            if (sel >= 0 && rBDl.Contains(p)) return 6;
            if (!busy && p.X >= PX && p.X < PX + PW && p.Y >= VY && p.Y < VY + VH)
            {
                int k = (int)((p.Y - VY + scrollY) / RowS);
                if (k >= 0 && k < results.Count) return (p.X >= PX + 16 && p.X < PX + 56 ? 1000 : 100) + k;
            }
            return 0;
        }

        // pill button, same look as the playlist pills (dimmed when disabled)
        void Btn(Graphics g, Rectangle r, string txt, int ico, bool hot, bool acc, bool en)
        {
            float k = en ? 1f : .4f; var bc2 = acc ? ICE : WH;
            FillRR(g, Br(Al(bc2, (int)((hot && en ? (acc ? 50 : 28) : (acc ? 26 : 12)) * k))), r, 16);
            DrawRR(g, Pe(Al(bc2, (int)((acc ? 90 : 28) * k)), 1f), new RectangleF(r.X + .5f, r.Y + .5f, r.Width - 1, r.Height - 1), 16);
            var col = en ? (acc ? ICE2 : TX) : DM;
            if (ico >= 0) { Ico(g, ico, r.X + 22, r.Y + r.Height / 2f, 5.5f, col, 1.5f); TxtIn(g, txt, fBtn, col, new RectangleF(r.X + 32, r.Y, r.Width - 32, r.Height), sfCC); }
            else TxtIn(g, txt, fBtn, col, r, sfCC);
        }

        // ---------- painting ----------
        surf.Paint += (s, e) =>
        {
            var g = e.Graphics; int pw = surf.ClientSize.Width, ph = surf.ClientSize.Height; if (pw <= 0 || ph <= 0) return;
            if (bgB == null || bgB.Width != pw || bgB.Height != ph)
            {
                bgB?.Dispose(); bgB = new Bitmap(pw, ph, PixelFormat.Format32bppPArgb);
                using var bg2 = Graphics.FromImage(bgB); bg2.SmoothingMode = SmoothingMode.AntiAlias;
                using (var lb = new LinearGradientBrush(new Rectangle(0, 0, pw, ph), Color.FromArgb(10, 18, 26), Color.FromArgb(4, 7, 11), 90f)) bg2.FillRectangle(lb, 0, 0, pw, ph);
                using var gp = new GraphicsPath(); gp.AddEllipse(pw * .05f, -ph * .55f, pw * .9f, ph * 1.2f);
                using var pb = new PathGradientBrush(gp) { CenterColor = Al(ICE, 30), SurroundColors = new[] { Al(ICE, 0) } }; bg2.FillPath(pb, gp);
            }
            g.DrawImage(bgB, 0, 0, pw, ph);
            g.DrawRectangle(Pe(Al(ICE, 60), 1), 0, 0, pw - 1, ph - 1);
            g.SmoothingMode = SmoothingMode.AntiAlias; g.InterpolationMode = InterpolationMode.HighQualityBicubic; g.PixelOffsetMode = PixelOffsetMode.HighQuality;
            g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.ClearTypeGridFit; g.ScaleTransform(u, u);

            // header
            Txt(g, "SEARCH YOUTUBE", fHdr, DM, PX, 15, 300);
            Hov(g, rClose2, hv == 1, true); Ico(g, I_CLOSE, rClose2.X + 16, rClose2.Y + 16, 6, hv == 1 ? WH : TX);

            // search field
            bool foc = tb.Focused;
            if (foc) DrawRR(g, Pe(Al(ICE, 26), 4f), new RectangleF(rField.X - 1, rField.Y - 1, rField.Width + 2, rField.Height + 2), 26);
            FillRR(g, Br(fieldBg), rField, 24);
            DrawRR(g, Pe(foc ? Al(ICE, 140) : Al(WH, 28), 1f), new RectangleF(rField.X + .5f, rField.Y + .5f, rField.Width - 1, rField.Height - 1), 24);
            Ico(g, I_SEARCH, rField.X + 25, rField.Y + 21, 7.5f, foc ? ICE : DM);
            if (tb.Text.Length > 0) { Hov(g, rClr2, hv == 3, false); Ico(g, I_CLOSE, rClr2.X + 11, rClr2.Y + 11, 4.5f, hv == 3 ? WH : DM, 1.5f); }
            Btn(g, rGo, "Search", -1, hv == 2, true, !busy);

            // results panel (glass, like the playlist)
            var pr = new RectangleF(PX, PY, PW, PH);
            using (var gb = new LinearGradientBrush(pr, Al(WH, 15), Al(WH, 4), 90f)) FillRR(g, gb, pr, 28);
            DrawRR(g, Pe(Al(WH, 22), 1f), new RectangleF(PX + .5f, PY + .5f, PW - 1, PH - 1), 28);

            var st = g.Save(); using (var cp = RR(new RectangleF(PX + 1, PY + 1, PW - 2, PH - 2), 27)) g.SetClip(cp);
            if (busy)
            {
                float wave = Environment.TickCount / 380f;
                for (int i = 0; i < 6; i++)
                {
                    float y = VY + i * RowS; int a = 9 + (int)(7 * (Math.Sin(wave - i * .6f) + 1));
                    FillRR(g, Br(Al(WH, a)), new RectangleF(PX + 16, y + 8, 40, 40), 10);
                    FillRR(g, Br(Al(WH, a)), new RectangleF(PX + 68, y + 14, 230 - (i % 3) * 36, 10), 10);
                    FillRR(g, Br(Al(WH, a * 3 / 4)), new RectangleF(PX + 68, y + 32, 120 + (i % 2) * 34, 8), 8);
                    FillRR(g, Br(Al(WH, a * 3 / 4)), new RectangleF(PX + PW - 66, y + 24, 34, 8), 8);
                }
            }
            else if (results.Count == 0)
            {
                float cx = PX + PW / 2f, cy = PY + PH / 2f - 26;
                g.FillEllipse(Br(Al(eErr ? Color.FromArgb(255, 120, 130) : ICE, 14)), cx - 34, cy - 34, 68, 68);
                g.DrawEllipse(Pe(Al(eErr ? Color.FromArgb(255, 120, 130) : ICE, 55), 1f), cx - 34, cy - 34, 68, 68);
                if (eErr) Ico(g, I_CLOSE, cx, cy, 10, Color.FromArgb(255, 140, 150), 1.8f); else Ico(g, I_SEARCH, cx, cy, 13, ICE, 1.8f);
                TxtIn(g, eT, fRow, TX, new RectangleF(PX + 20, cy + 46, PW - 40, 20), sfCC);
                TxtIn(g, eS, fS, DM, new RectangleF(PX + 20, cy + 68, PW - 40, 18), sfCC);
            }
            else
            {
                int hr = hv >= 1000 ? hv - 1000 : hv >= 100 ? hv - 100 : -1;
                int first = Math.Max(0, (int)(scrollY / RowS)), last = Math.Min(results.Count - 1, (int)((scrollY + VH) / RowS));
                for (int k = first; k <= last; k++)
                {
                    float y = VY + k * RowS - scrollY; var tk = results[k]; bool isSel = k == sel, isHot = k == hr, inPl = pl.Contains(tk);
                    var rr = new RectangleF(PX + 6, y + 2, PW - 12 - 8, RowS - 4);
                    if (isSel) FillRR(g, Br(Al(ICE, 28)), rr, 20); else if (isHot) FillRR(g, Br(Al(WH, 12)), rr, 20);

                    // thumbnail (rounded), with a play overlay on hover
                    var tr = new RectangleF(PX + 16, y + 8, 40, 40); var st2 = g.Save();
                    using (var tp = RR(tr, 10))
                    {
                        g.SetClip(tp, CombineMode.Intersect);
                        if (thumbs.TryGetValue(tk.Url, out var tbm)) g.DrawImage(tbm, tr);
                        else { using var tlb = new LinearGradientBrush(tr, Color.FromArgb(22, 44, 58), Color.FromArgb(8, 14, 20), 90f); g.FillRectangle(tlb, tr); g.DrawEllipse(Pe(Al(ICE, 50), 1f), tr.X + 12, tr.Y + 12, 16, 16); }
                        if (isHot) g.FillRectangle(Br(Color.FromArgb(150, 6, 12, 18)), tr);
                    }
                    g.Restore(st2);
                    DrawRR(g, Pe(Al(WH, 30), 1f), new RectangleF(tr.X + .5f, tr.Y + .5f, tr.Width - 1, tr.Height - 1), 10);
                    if (isHot) Ico(g, I_PLAY, tr.X + 20, tr.Y + 20, 7, hv >= 1000 ? WH : ICE2);

                    float tx = PX + 68, right = rr.Right - 14 - 46 - (inPl ? 24 : 0);
                    Txt(g, tk.Title, fRow, isSel ? WH : TX, tx, y + 10, right - tx); Txt(g, tk.Artist, fXs, DM, tx, y + 29, right - tx);
                    if (tk.Dur > 0) TxtIn(g, Fm(tk.Dur), fXs, DM, new RectangleF(rr.Right - 14 - 46, y + 20, 46, 16), sfR);
                    if (inPl) Ico(g, I_CHECK, rr.Right - 14 - 46 - 12, y + RowS / 2f, 5.5f, ICE);
                }
                float mx = MaxS();
                if (mx > 0)
                {
                    float total = results.Count * RowS, th = Math.Max(28, VH * VH / total), ty = VY + (VH - th) * (scrollY / mx);
                    FillRR(g, Br(Al(WH, hv == 0 ? 34 : 46)), new RectangleF(PX + PW - 12, ty, 4, th), 4);
                }
            }
            g.Restore(st);

            // footer: status + actions
            string stx; var stc = DM;
            if (busy) stx = "Searching YouTube…";
            else if (note.Length > 0) { stx = note; stc = ICE; }
            else if (results.Count > 0) stx = results.Count + (results.Count == 1 ? " result" : " results") + "  ·  ↑ ↓ browse  ·  Enter plays";
            else stx = "Results from YouTube";
            Txt(g, stx, fXs, stc, PX + 4, 477, rBPlay.X - PX - 16);
            bool en = sel >= 0 && !busy;
            Btn(g, rBPlay, "Play", I_PLAY, hv == 4, true, en); Btn(g, rBQ, "+ Queue", -1, hv == 5, false, en); Btn(g, rBDl, "Download MP3", I_DOWN, hv == 6, false, en);
        };

        // ---------- actions ----------
        async Task Search()
        {
            var q = tb.Text.Trim().Replace("\"", "").Replace("\\", ""); if (q.Length == 0 || busy) return;
            if (IsSpotify(tb.Text)) { var raw = tb.Text.Trim(); after = () => AddSpotify(raw); f.Close(); return; }
            int my = ++sgen; busy = true; note = ""; lastQ = tb.Text.Trim(); anim.Start(); surf.Invalidate();
            try
            {
                var j = await Ytdlp($"-J --flat-playlist --no-warnings \"ytsearch12:{q}\"");
                if (closed || my != sgen) return;
                using var d = System.Text.Json.JsonDocument.Parse(j); results.Clear(); sel = -1; scrollY = 0; eErr = false;
                foreach (var tbm in thumbs.Values) tbm.Dispose(); thumbs.Clear();
                string S(System.Text.Json.JsonElement el, string key) => el.TryGetProperty(key, out var v) && v.ValueKind == System.Text.Json.JsonValueKind.String ? v.GetString() : null;
                if (d.RootElement.TryGetProperty("entries", out var en))
                    foreach (var el in en.EnumerateArray())
                    {
                        var id = S(el, "id"); if (id == null) continue;
                        results.Add(YtFix(new Track { Url = "https://www.youtube.com/watch?v=" + id, Title = S(el, "title") ?? "Untitled", Artist = S(el, "channel") ?? S(el, "uploader") ?? "YouTube", Album = "YouTube",
                            Dur = el.TryGetProperty("duration", out var du) && du.ValueKind == System.Text.Json.JsonValueKind.Number ? du.GetDouble() : 0 }));
                    }
                if (results.Count == 0) { eT = "No results"; eS = "Try different keywords"; } else sel = 0;
                foreach (var r0 in results.ToList())
                {
                    var tr0 = r0;
                    Task.Run(() =>
                    {
                        var bm = tr0.ArtUrl != null ? LoadArt(tr0.ArtUrl) : LoadThumb(tr0.Url); if (bm == null) return;
                        try { surf.BeginInvoke(new Action(() => { if (closed || my != sgen) { bm.Dispose(); return; } thumbs[tr0.Url] = bm; surf.Invalidate(); })); } catch { bm.Dispose(); }
                    });
                }
            }
            catch (Exception ex)
            {
                if (closed) return;
                results.Clear(); sel = -1; eErr = true; eT = "Search failed";
                var m = (ex.Message ?? "").Split('\n')[0].Trim(); eS = m.Length > 90 ? m.Substring(0, 90) + "…" : m;
            }
            finally { busy = false; if (!closed) { anim.Stop(); surf.Invalidate(); } }
        }
        void DoPlay()
        {
            var t = Pick(); if (t == null) return;
            after = () => { int ix = pl.IndexOf(t); if (ix >= 0) { Play(ix); return; } t.Art = RandomCover(); pl.Add(t); Thumb(t); SaveState(); Play(pl.Count - 1); };
            f.Close();
        }
        void DoQ()
        {
            var t = Pick(); if (t == null) return;
            if (pl.Contains(t)) { note = "Already in your playlist"; surf.Invalidate(); return; }
            t.Art = RandomCover(); pl.Add(t); Thumb(t); SaveState(); note = "Added to playlist"; if (cur < 0) Play(0); else Invalidate(); surf.Invalidate();
        }
        void DoDl() { var t = Pick(); if (t == null) return; after = () => Download(new List<Track> { t }); f.Close(); }

        // ---------- input ----------
        anim.Tick += (s, e) => surf.Invalidate();
        surf.MouseMove += (s, e) => { int h = HitT(V(e.Location)); if (h != hv) { hv = h; surf.Cursor = h != 0 ? Cursors.Hand : Cursors.Default; surf.Invalidate(); } };
        surf.MouseLeave += (s, e) => { if (hv != 0) { hv = 0; surf.Invalidate(); } };
        surf.MouseDown += (s, e) =>
        {
            if (e.Button != MouseButtons.Left) return; var p = V(e.Location); int h = HitT(p);
            if (h == 0 && p.Y < 46) { ReleaseCapture(); SendMessage(f.Handle, 0xA1, 2, 0); return; }
            if (h == 1) { f.Close(); return; }
            if (h == 2) _ = Search(); else if (h == 3) tb.Clear(); else if (h == 4) DoPlay(); else if (h == 5) DoQ(); else if (h == 6) DoDl();
            else if (h >= 1000) { sel = h - 1000; DoPlay(); }
            else if (h >= 100) { sel = h - 100; note = ""; }
            if (!closed) { tb.Focus(); surf.Invalidate(); }
        };
        surf.MouseDoubleClick += (s, e) => { int h = HitT(V(e.Location)); if (h >= 100 && h < 1000) { sel = h - 100; DoPlay(); } };
        MouseEventHandler wheel = (s, e) =>
        {
            if (MaxS() <= 0) return; scrollY = Math.Clamp(scrollY - e.Delta / 120f * RowS, 0, MaxS());
            hv = HitT(V(surf.PointToClient(Cursor.Position))); surf.Invalidate();
        };
        surf.MouseWheel += wheel; tb.MouseWheel += wheel;
        tb.TextChanged += (s, e) => surf.Invalidate();
        tb.Enter += (s, e) => surf.Invalidate(); tb.Leave += (s, e) => surf.Invalidate();
        tb.KeyDown += async (s, e) =>
        {
            if (e.KeyCode == Keys.Enter)
            {
                e.SuppressKeyPress = true;
                if (!busy && results.Count > 0 && sel >= 0 && tb.Text.Trim() == lastQ) DoPlay(); else await Search();
            }
            else if (e.KeyCode == Keys.Escape) { e.SuppressKeyPress = true; f.Close(); }
            else if (e.KeyCode == Keys.A && e.Control) { e.SuppressKeyPress = true; tb.SelectAll(); }
            else if ((e.KeyCode == Keys.Down || e.KeyCode == Keys.Up || e.KeyCode == Keys.PageDown || e.KeyCode == Keys.PageUp) && results.Count > 0 && !busy)
            {
                e.SuppressKeyPress = true; int d = e.KeyCode == Keys.Down ? 1 : e.KeyCode == Keys.Up ? -1 : e.KeyCode == Keys.PageDown ? 5 : -5;
                sel = Math.Clamp((sel < 0 ? 0 : sel) + d, 0, results.Count - 1); note = ""; EnsVis(); surf.Invalidate();
            }
        };
        f.FormClosed += (s, e) => { closed = true; anim.Stop(); anim.Dispose(); };
        f.Shown += (s, e) => tb.Focus();
        f.ShowDialog(this);
        foreach (var tz in thumbs.Values) tz.Dispose(); thumbs.Clear(); bgB?.Dispose();
        after?.Invoke();
    }

    // ---------- remember playlist + settings between launches ----------
    static string StateFile => System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "TheWiredMusic", "state.json");
    void SaveState()
    {
        try
        {
            var d = new PersistData { Cur = cur, Vol = vol, Shuf = shuf, Rep = rep };
            foreach (var t in pl) d.Tracks.Add(new PersistTrack { Url = t.Url, Path = t.Path, Title = t.Title, Artist = t.Artist, Album = t.Album, Year = t.Year, Dur = t.Dur, Saved = t.Saved, ArtUrl = t.ArtUrl, Spot = t.Spot });
            Directory.CreateDirectory(System.IO.Path.GetDirectoryName(StateFile)); System.IO.File.WriteAllText(StateFile, System.Text.Json.JsonSerializer.Serialize(d));
        }
        catch { }
    }
    void LoadState()
    {
        try
        {
            if (!System.IO.File.Exists(StateFile)) return;
            var d = System.Text.Json.JsonSerializer.Deserialize<PersistData>(System.IO.File.ReadAllText(StateFile)); if (d == null) return;
            vol = Math.Clamp(d.Vol, 0f, 1f); shuf = d.Shuf; rep = d.Rep; Track curT = null;
            for (int i = 0; i < d.Tracks.Count; i++)
            {
                var s = d.Tracks[i]; if (s.Path != null && !System.IO.File.Exists(s.Path)) continue;
                var t = new Track { Url = s.Url, Path = s.Path, Title = s.Title ?? "", Artist = s.Artist ?? "Unknown", Album = s.Album ?? "", Year = s.Year ?? "", Dur = s.Dur, Saved = s.Saved, ArtUrl = s.ArtUrl, Spot = s.Spot, Art = RandomCover() };
                pl.Add(t); if (i == d.Cur) curT = t;
            }
            cur = curT != null ? pl.IndexOf(curT) : -1;
            if (cur >= 0) Text = $"{pl[cur].Artist} - {pl[cur].Title}";
        }
        catch { }
    }
    // covers + lyrics of local songs are re-read in the background after launch
    void ReloadMeta()
    {
        foreach (var y in pl.Where(x => x.Url != null).ToList()) Thumb(y);
        var locals = pl.Where(t => t.Path != null).ToList();
        Task.Run(() =>
        {
            foreach (var t in locals)
            {
                try
                {
                    using var tf = TagLib.File.Create(t.Path); string ly = tf.Tag.Lyrics; Bitmap bm = null;
                    if (tf.Tag.Pictures.Length > 0) { using var ms = new MemoryStream(tf.Tag.Pictures[0].Data.Data); using var im = Image.FromStream(ms); bm = Square(im, 320); }
                    bm ??= FolderArt(t.Path); BeginInvoke(new Action(() => { if (!string.IsNullOrWhiteSpace(ly)) SetLyrics(t, ly); if (bm != null) { t.Art = bm; t.Real = true; if (artFor == t) artFor = null; } Invalidate(); }));
                }
                catch { }
            }
            try { BeginInvoke(new Action(() => Relayout())); } catch { }
        });
    }
    // keep yt-dlp fresh (YouTube changes often and old versions stop working)
    void UpdateYtdlp()
    {
        Task.Run(async () =>
        {
            try
            {
                var exe = System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "TheWiredMusic", "yt-dlp.exe");
                if (System.IO.File.Exists(exe) && (DateTime.Now - System.IO.File.GetLastWriteTime(exe)).TotalDays > 5) { ytUpdated = true; await Ytdlp("-U"); }
                if (System.IO.File.Exists(exe)) await Ytdlp("--version");
            }
            catch { }
        });
    }

    // ---------- media keys (work even when the browser is focused) ----------
    [DllImport("user32.dll")] static extern bool RegisterHotKey(IntPtr h, int id, uint mod, uint vk);
    [DllImport("user32.dll")] static extern bool UnregisterHotKey(IntPtr h, int id);
    protected override void OnHandleCreated(EventArgs e) { base.OnHandleCreated(e); RegisterHotKey(Handle, 1, 0, 0xB3); RegisterHotKey(Handle, 2, 0, 0xB0); RegisterHotKey(Handle, 3, 0, 0xB1); }
    protected override void OnHandleDestroyed(EventArgs e) { UnregisterHotKey(Handle, 1); UnregisterHotKey(Handle, 2); UnregisterHotKey(Handle, 3); base.OnHandleDestroyed(e); }
    protected override void WndProc(ref Message m)
    {
        if (m.Msg == 0x0312) { switch ((int)m.WParam) { case 1: Toggle(); break; case 2: Next(); break; case 3: Prev(); break; } Invalidate(); return; }
        base.WndProc(ref m);
    }
    void SeekBy(double sec)
    {
        if (rd == null) return;
        try { var t = posS + sec; if (t < 0) t = 0; if (buf != null && t < rd.TotalTime.TotalSeconds - 1) { buf.Seek(t); posS = t; } } catch { }
    }

    // ---------- right-click menu on a playlist row ----------
    ContextMenuStrip NewMenu() => new ContextMenuStrip { BackColor = Color.FromArgb(10, 16, 22), ForeColor = TX, Font = new Font("Segoe UI", 9.5f), ShowImageMargin = false, Renderer = new ToolStripProfessionalRenderer(new DarkColors()) { RoundedEdges = false } };
    void RowMenu(int k)
    {
        if (k < 0 || k >= pl.Count) return; var t = pl[k]; var m = NewMenu();
        void Item(string txt, Action a) { var it = new ToolStripMenuItem(txt) { ForeColor = TX }; it.Click += (s, e) => { a(); Invalidate(); }; m.Items.Add(it); }
        Item("Play", () => Play(k)); Item("Set artist...", () => SetArtist(k));
        if (t.Path != null) Item("Show in folder", () => { try { System.Diagnostics.Process.Start("explorer.exe", "/select,\"" + t.Path + "\""); } catch { } });
        Item("Remove from playlist", () => RemoveAt(k));
        m.Show(Cursor.Position);
    }
    void ClearAll() { Stop(); ++gen; pl.Clear(); cur = -1; scroll = 0; posS = durS = 0; Text = "THE WIRED MUSIC"; St(""); SaveState(); Relayout(); }
    void RemoveAt(int k)
    {
        if (k < 0 || k >= pl.Count) return; bool was = k == cur; if (was) Stop();
        pl.RemoveAt(k);
        if (was) { if (pl.Count > 0) Play(Math.Min(k, pl.Count - 1)); else { cur = -1; ++gen; Text = "THE WIRED MUSIC"; } } else if (k < cur) cur--;
        scroll = Math.Clamp(scroll, 0, Math.Max(0, pl.Count - Rows)); SaveState(); Relayout();
    }

    void ShowMenu()
    {
        var m = new ContextMenuStrip { BackColor = Color.FromArgb(10, 16, 22), ForeColor = TX, Font = new Font("Segoe UI", 9.5f), ShowImageMargin = false, Renderer = new ToolStripProfessionalRenderer(new DarkColors()) { RoundedEdges = false } };
        void Item(string t, Action a, bool chk = false) { var it = new ToolStripMenuItem(t) { Checked = chk, ForeColor = TX }; it.Click += (s, e) => { a(); Invalidate(); }; m.Items.Add(it); }
        void OpenDir() { using var d = new FolderBrowserDialog(); if (d.ShowDialog() == DialogResult.OK) Add(new[] { d.SelectedPath }); }
        Item("Open files...", PickFiles); Item("Open folder...", OpenDir);
        m.Items.Add(new ToolStripSeparator());
        Item("Search YouTube...", () => OpenSearch()); Item("Add YouTube link...", OpenYt);
        m.Items.Add(new ToolStripSeparator());
        Item("Download all online tracks...", () => Download(pl.ToList()));
        m.Items.Add(new ToolStripSeparator());
        Item("Shuffle", () => shuf = !shuf, shuf); Item("Repeat", () => rep = !rep, rep);
        m.Items.Add(new ToolStripSeparator());
        Item("Clear playlist", ClearAll);
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

// double-buffered surface for the custom-painted search dialog
class DBuf : Control
{
    public DBuf() { SetStyle(ControlStyles.AllPaintingInWmPaint | ControlStyles.UserPaint | ControlStyles.OptimizedDoubleBuffer | ControlStyles.ResizeRedraw, true); }
}
