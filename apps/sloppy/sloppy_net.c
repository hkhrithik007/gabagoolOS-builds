/* GabagoolOS networking. Plain POSIX on purpose: no Rockbox headers, so
 * open/read/write here are the C library's, not Rockbox's path-rewriting
 * wrappers, and nothing here touches the Rockbox kernel. Wi-Fi uses the
 * tools HiBy's own firmware uses (wpa_supplicant/wpa_cli, udhcpc, ntpdate,
 * thttpd with its upload CGIs, shairport). The DLNA renderer is ours. */
#define _GNU_SOURCE 1                   /* strcasestr */
#include <arpa/inet.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <ifaddrs.h>
#include <net/if.h>
#include <netdb.h>
#include <netinet/in.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include "sloppy_net.h"
#include "sloppy_ota.h"
#include "sloppy_png.h"

/* sloppy.c's log (sloppy.h, which this plain-POSIX file doesn't include):
 * the radio's HTTPS setup says there what it found */
void sl_log(const char *fmt, ...) __attribute__((format(printf, 1, 2)));

#if defined(SIMULATOR) || defined(SLOPPY_NET_TEST)
#define NET_DEMO 1                       /* no radio: a pretend one */
#endif
#ifdef __APPLE__
/* older macOS has no pipe2() (newer SDKs declare one): the simulator and
 * the UI tests build here, so use our own either way */
#define pipe2 sl_pipe2
static int pipe2(int fd[2], int flags)
{
    if (pipe(fd)) return -1;
    if (flags & O_CLOEXEC) { fcntl(fd[0], F_SETFD, FD_CLOEXEC); fcntl(fd[1], F_SETFD, FD_CLOEXEC); }
    return 0;
}
#endif

static uint32_t net_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint32_t)(ts.tv_sec * 1000u + ts.tv_nsec / 1000000u);
}

static void net_sleep_ms(int ms)
{
    struct timespec ts = { ms / 1000, (ms % 1000) * 1000000L };
    while (nanosleep(&ts, &ts) && errno == EINTR) {}
}

/* the card root as the C library sees it: Rockbox calls it "/". While the
 * card is a computer's (USB mode, from the handover until it is mounted
 * again) there is none: a root nothing can be made under, so no worker
 * writes to the card, nor under its empty mount point. */
#define NET_NO_CARD "/dev/null/card-away"
static const char *net_root(void)
{
#if defined(SLOPPY_NET_TEST)
    return getenv("SL_NET_ROOT");
#elif defined(SIMULATOR)
    extern const char *sim_root_dir;
    extern volatile bool sim_card_away;
    return sim_card_away ? NET_NO_CARD : sim_root_dir;
#else
    extern bool usb_card_away(void);      /* usb-hiby-gadget.c */
    return usb_card_away() ? NET_NO_CARD : "/data/mnt/sd_0";
#endif
}

/* the card root, for the other plain-POSIX files (sloppy_png.c) */
const char *sl_net_card_root(void) { return net_root(); }

/* The program's full path, found before fork(): the child of a threaded
 * process may only make async-signal-safe calls, and execvp's PATH search
 * can allocate, which deadlocks if another thread held the heap lock. */
static bool net_path(const char *name, char *path, size_t n)
{
    static const char *const dirs[] = { "/usr/sbin/", "/usr/bin/", "/sbin/", "/bin/" };
    if (strchr(name, '/')) { snprintf(path, n, "%s", name); return true; }
    for (unsigned i = 0; i < sizeof dirs / sizeof dirs[0]; i++)
    {
        snprintf(path, n, "%s%s", dirs[i], name);
        if (!access(path, X_OK)) return true;
    }
    return false;
}

/* Why the last program could not start, for the Wi-Fi error in the log. */
static char net_start_error[64];
static void net_start_failed(const char *name)
{
    snprintf(net_start_error, sizeof net_start_error, "%s: %s", name, strerror(errno));
}

/* Programs start with vfork(). fork() has to reserve a copy of the whole
 * Rockbox process, which on the R1 fails with ENOMEM once playback buffers
 * and the library are loaded, so the radio "failed" with nothing run. The
 * children below only make system calls before execv(), as vfork needs. */

/* Run a program, keep up to cap-1 bytes of what it prints. Returns its exit
 * status, or -1 when it could not run or took longer than timeout_ms. */
static int net_run(char *out, size_t cap, int timeout_ms, const char *const argv[])
{
    int fd[2];
    char path[128];
    if (out && cap) out[0] = '\0';
    if (!net_path(argv[0], path, sizeof path)) return -1;
    if (pipe2(fd, O_CLOEXEC)) { net_start_failed(argv[0]); return -1; }   /* no other child keeps it */
    pid_t pid = vfork();
    if (pid < 0) { net_start_failed(argv[0]); close(fd[0]); close(fd[1]); return -1; }
    if (pid == 0)
    {
        int null = open("/dev/null", O_RDWR);
        dup2(null, 0);
        dup2(fd[1], 1);
        dup2(null, 2);
        for (int i = 3; i < 256; i++) close(i);
        execv(path, (char *const *)argv);
        _exit(127);
    }
    close(fd[1]);
    size_t n = 0;
    bool timed_out = false;
    uint32_t until = net_ms() + (uint32_t)timeout_ms;
    for (;;)
    {
        int left = (int)(until - net_ms());
        if (left <= 0) { kill(pid, SIGKILL); timed_out = true; break; }
        struct pollfd p = { fd[0], POLLIN, 0 };
        if (poll(&p, 1, left) <= 0) continue;
        char buf[512];
        ssize_t r = read(fd[0], buf, sizeof buf);
        if (r <= 0) break;
        if (out && n + 1 < cap)
        {
            size_t take = (size_t)r < cap - 1 - n ? (size_t)r : cap - 1 - n;
            memcpy(out + n, buf, take);
            n += take;
            out[n] = '\0';
        }
    }
    close(fd[0]);
    int status;
    if (waitpid(pid, &status, 0) < 0) return -1;
    if (timed_out) return -1;
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

static __attribute__((unused)) int net_sh(char *out, size_t cap, int timeout_ms, const char *cmd)
{
    const char *argv[] = { "/bin/sh", "-c", cmd, NULL };
    return net_run(out, cap, timeout_ms, argv);
}

/* a program that keeps running on its own; returns its pid */
static __attribute__((unused)) pid_t net_spawn(const char *const argv[])
{
    char path[128];
    if (!net_path(argv[0], path, sizeof path)) return -1;
    pid_t pid = vfork();
    if (pid < 0) net_start_failed(argv[0]);
    if (pid == 0)
    {
        setsid();
        int null = open("/dev/null", O_RDWR);
        dup2(null, 0); dup2(null, 1); dup2(null, 2);
        for (int i = 3; i < 256; i++) close(i);
        execv(path, (char *const *)argv);
        _exit(127);
    }
    return pid;
}

static void net_reap(pid_t *pid)
{
    if (*pid <= 0) return;
    kill(*pid, SIGTERM);
    for (int i = 0; i < 20 && waitpid(*pid, NULL, WNOHANG) == 0; i++) net_sleep_ms(50);
    if (waitpid(*pid, NULL, WNOHANG) == 0) { kill(*pid, SIGKILL); waitpid(*pid, NULL, 0); }
    *pid = 0;
}

/* The first address that is not loopback, as text; empty when none. */
static void net_local_ip(char *ip, size_t n)
{
    ip[0] = '\0';
    struct ifaddrs *list, *a;
    if (getifaddrs(&list)) return;
    for (a = list; a; a = a->ifa_next)
    {
        if (!a->ifa_addr || a->ifa_addr->sa_family != AF_INET) continue;
        if ((a->ifa_flags & IFF_LOOPBACK) || !(a->ifa_flags & IFF_UP)) continue;
        inet_ntop(AF_INET, &((struct sockaddr_in *)a->ifa_addr)->sin_addr, ip, n);
        if (!strcmp(a->ifa_name, "wlan0")) break;          /* the radio wins */
    }
    freeifaddrs(list);
}

/* ------------------------------------------------------- the wireless chip */
/* HiBy's 2.0 picks its driver from the PMIC's note of the SoC
 * (/module_driver/r1_wireless_select.sh): X1600E has the Broadcom chip,
 * X1600EN and X1600HN an AIC8800D40. The 1.6 system has no AIC driver (and
 * its PMIC driver does not write the id); the boot menu built on 2.0 has
 * HiBy's own: aic8800_bsp and btlpm load at boot, and wifi_on.sh,
 * wifi_off.sh, bt_enable_aic.sh and bt_disable power each radio on demand
 * (the "power gate", /run/aic_combo_power_gate). The file is read as hex
 * whichever way it is written ("0x4a00", "4a00" or decimal 18944). */
int sl_net_soc_fake = -1;
int sl_net_soc_parse(const char *b)
{
    while (*b == ' ' || *b == '\t') b++;
    if (!*b || *b == '\n') return -1;
    char *end;
    if (b[0] == '0' && (b[1] == 'x' || b[1] == 'X')) return (int)strtol(b + 2, NULL, 16);
    long d = strtol(b, &end, 10);
    if (end != b && (*end == '\0' || *end == '\n' || *end == ' ') && (d == 0x0a00 || d == 0x4a00 || d == 0x4900)) return (int)d;
    return (int)strtol(b, NULL, 16);
}
int sl_net_soc_id(void)
{
    static int id = -2;
    if (sl_net_soc_fake >= 0) return sl_net_soc_fake;
    if (id != -2) return id;
    id = -1;
#ifndef NET_DEMO
    FILE *f = fopen("/sys/module/axp2101/parameters/detected_soc_id", "r");
    if (f)
    {
        char b[32];
        if (fgets(b, sizeof b, f)) id = sl_net_soc_parse(b);
        fclose(f);
    }
#endif
    return id;
}
const char *sl_net_soc_name(int id)
{
    return id == 0x0a00 ? "X1600E" : id == 0x4a00 ? "X1600EN" : id == 0x4900 ? "X1600HN" : "unknown";
}
int sl_net_aic_fake = -2;
bool sl_net_wireless_aic(void)
{
    int id = sl_net_soc_id();
    if (id == 0x4a00 || id == 0x4900) return true;
    if (id >= 0 || sl_net_soc_fake >= 0) return false;
#ifndef NET_DEMO
    /* no id (the 1.6 PMIC driver): an AIC chip on the SDIO bus says so too */
    static int sdio = -1;
    if (sdio < 0)
    {
        sdio = 0;
        FILE *f = popen("cat /sys/bus/sdio/devices/*/vendor 2>/dev/null", "r");
        if (f)
        {
            char b[16];
            while (fgets(b, sizeof b, f)) if (strtol(b, NULL, 16) == 0xc8a1) sdio = 1;
            pclose(f);
        }
    }
    return sdio == 1;
#else
    return false;
#endif
}
/* HiBy 2.0's AIC power gate is on this system and its base driver loaded:
 * 1 yes, 0 the scripts are missing (a boot menu built on 1.6), -1 they are
 * here but aic8800_bsp failed to load at boot. */
int sl_net_aic_state(void)
{
    if (sl_net_aic_fake != -2) return sl_net_aic_fake;
#ifdef NET_DEMO
    return 0;
#else
    if (access("/usr/bin/aic_radio.sh", R_OK) || access("/usr/bin/bt_enable_aic.sh", R_OK) ||
        access("/module_driver/aic8800_fdrv.load", R_OK)) return 0;
    char b[16] = "";
    FILE *f = fopen("/run/r1_wireless_loaded", "r");   /* written by aic8800_bsp.r1 when it is done */
    if (f) { if (!fgets(b, sizeof b, f)) b[0] = '\0'; fclose(f); }
    return strncmp(b, "fail", 4) ? 1 : -1;
#endif
}
bool sl_net_wireless_unsupported(void)
{
    return sl_net_wireless_aic() && sl_net_aic_state() != 1;
}
void sl_net_wireless_probe(char *out, size_t n)
{
    int id = sl_net_soc_id();
    char drivers[160] = "";
#ifndef NET_DEMO
    size_t used = 0;
    static const char *const mods[] = { "cywdhd", "bcmdhd", "aic8800_bsp", "aic8800_fdrv", "aic8800_btlpm" };
    for (unsigned i = 0; i < sizeof mods / sizeof mods[0]; i++)
    {
        char p[64];
        snprintf(p, sizeof p, "/sys/module/%s", mods[i]);
        if (!access(p, F_OK) && used + strlen(mods[i]) + 2 < sizeof drivers)
            used += (size_t)snprintf(drivers + used, sizeof drivers - used, "%s%s", used ? " " : "", mods[i]);
    }
#endif
    char sid[16] = "not reported";
    if (id >= 0) snprintf(sid, sizeof sid, "0x%04x", id);
    snprintf(out, n, "soc id %s (%s), %s chip; driver modules: %s", sid, sl_net_soc_name(id),
             !sl_net_wireless_aic() ? (id < 0 ? "an unknown" : "the Broadcom") :
             sl_net_aic_state() == 1 ? "an AIC8800D40 (HiBy 2.0 drivers)" :
             sl_net_aic_state() == 0 ? "an AIC8800D40 (no driver: needs the 2.0 boot menu)" :
             "an AIC8800D40 (its driver failed to load)",
             drivers[0] ? drivers : "none loaded");
}

/* ---------------------------------------------------------------- Wi-Fi */
static const char *wifi_last_error;
const char *sl_net_wifi_last_error(void)
{
    static char both[128];
    if (!net_start_error[0]) return wifi_last_error ? wifi_last_error : "";
    snprintf(both, sizeof both, "%s (%s)", wifi_last_error ? wifi_last_error : "failed",
             net_start_error);
    return both;
}
/* What the kernel said when the radio would not attach: the bind error,
 * which driver holds the chip, the rfkill switches and the driver's last
 * kernel lines. Read on the UI side once the job is done. */
static char wifi_detail[320];
const char *sl_net_wifi_detail(void) { return wifi_detail; }
#ifdef NET_DEMO
static bool demo_on, demo_connected = true;   /* joins "Home network" when on */
static char demo_ssid[33] = "Home network";
static const struct sl_wifi_ap demo_aps[] = {
    { "Home network", -48, true, true }, { "Coffee shop", -67, false, false },
    { "Neighbours 5G", -79, true, false },
};
bool sl_net_wifi_power(bool on)
{
    if (on && sl_net_wireless_unsupported()) { wifi_last_error = "this R1's AIC8800 wireless chip is not supported yet"; return false; }
    demo_on = on; if (!on) demo_connected = false; return true;
}
bool sl_net_wifi_radio_missing(void) { return false; }
void sl_net_wifi_status(struct sl_wifi_status *s)
{
    memset(s, 0, sizeof *s);
    s->on = demo_on;
    s->connected = demo_on && demo_connected;
    if (s->connected)
    {
        strncpy(s->ssid, demo_ssid, sizeof s->ssid - 1);
        net_local_ip(s->ip, sizeof s->ip);
        if (!s->ip[0]) strcpy(s->ip, "192.168.1.42");
    }
}
int sl_net_wifi_scan(struct sl_wifi_ap *aps, int max)
{
    int n = 0;
    if (!demo_on) return 0;
    for (; n < max && n < (int)(sizeof demo_aps / sizeof demo_aps[0]); n++) aps[n] = demo_aps[n];
    return n;
}
bool sl_net_wifi_connect(const char *ssid, const char *psk) { return sl_net_wifi_connect_ex(ssid, psk, false); }
bool sl_net_wifi_connect_ex(const char *ssid, const char *psk, bool hidden)
{
    (void)psk; (void)hidden;
    if (!demo_on) return false;
    strncpy(demo_ssid, ssid, sizeof demo_ssid - 1);
    demo_connected = true;
    return true;
}
bool sl_net_wifi_forget(const char *ssid)
{
    if (!strcmp(ssid, demo_ssid)) demo_connected = false;
    return true;
}
bool sl_net_ntp(void) { return false; }
/* the pretend internet: an AutoEq index with one pair of headphones, and their profile */
char sl_net_demo_url[512];                /* the last address asked for, for the tests */
const char *sl_net_demo_fail;            /* an address with this in it does not answer */
int sl_net_get(const char *url, char *out, size_t cap)
{
    snprintf(sl_net_demo_url, sizeof sl_net_demo_url, "%s", url);
    if (sl_net_demo_fail && strstr(url, sl_net_demo_fail)) return -1;
    const char *body = strstr(url, "ip-api.com") ? "gb\n" : strstr(url, "name=nothing") ? "[]" : strstr(url, "lrclib.net/api/search") ?
        "[{\"id\":1,\"trackName\":\"Night Drive\",\"artistName\":\"Mira Sol\",\"albumName\":\"Blue Hours\",\"duration\":240.0,"
        "\"instrumental\":false,\"plainLyrics\":\"Streetlights hum\\nThe harbor holds its breath\",\"syncedLyrics\":\"[00:01.00]Streetlights hum\\n[00:05.00]The harbor holds its breath\"},"
        "{\"id\":2,\"trackName\":\"Night Drive (Live)\",\"artistName\":\"Mira Sol\",\"albumName\":\"Live at the Harbor\",\"duration\":262.0,"
        "\"instrumental\":false,\"plainLyrics\":\"Streetlights hum\",\"syncedLyrics\":\"[00:02.00]Streetlights hum\"},"
        "{\"id\":3,\"trackName\":\"Night Drive\",\"artistName\":\"Mira Sol\",\"albumName\":null,\"duration\":241.0,"
        "\"instrumental\":false,\"plainLyrics\":\"Streetlights hum, the words alone\",\"syncedLyrics\":null}]" :
        strstr(url, "INDEX.md") ?
        "# Index\n\n- [Other Phones](./src/over-ear/Other%20Phones) by src\n"
        "- [Test Phones](./oratory1990/over-ear/Test%20Phones) by oratory1990\n" :
        strstr(url, "radio-browser") ?
        "[{\"changeuuid\":\"a\",\"name\":\"Test FM\",\"url\":\"x\",\"url_resolved\":\"/tmp/sloppy-radio-test.mp2\","
        "\"tags\":\"jazz,soul\",\"countrycode\":\"GB\",\"bitrate\":32},"
        "{\"changeuuid\":\"b\",\"name\":\"Caf\\u00e9 \\\"Noir\\\"\",\"url_resolved\":\"nowhere\",\"tags\":\"\",\"countrycode\":\"FR\",\"bitrate\":0},"
        "{\"changeuuid\":\"c\",\"name\":\"Backup FM\",\"url\":\"/tmp/sloppy-radio-test.mp2\",\"url_resolved\":\"https://nowhere\",\"bitrate\":64},"
        "{\"changeuuid\":\"d\",\"name\":\"AAC FM\",\"url_resolved\":\"/tmp/sloppy-radio-test.aac\",\"codec\":\"AAC\",\"bitrate\":64}]" :
        strstr(url, "Test%20Phones%20ParametricEQ.txt") ?
        "Preamp: -3.0 dB\nFilter 1: ON LSC Fc 105 Hz Gain 3.0 dB Q 0.70\nFilter 2: ON PK Fc 2000 Hz Gain -2.0 dB Q 1.00\n" : NULL;
    if (!body) return -1;
    snprintf(out, cap, "%s", body);
    return (int)strlen(out);
}
bool sl_net_share_start(void) { return true; }
void sl_net_share_stop(void) {}
#else
static int wpa(char *out, size_t cap, const char *a1, const char *a2, const char *a3, const char *a4)
{
    const char *argv[] = { "wpa_cli", "-i", "wlan0", a1, a2, a3, a4, NULL };
    return net_run(out, cap, 8000, argv);
}

static bool wpa_ready(void)
{
    char out[32];
    const char *argv[] = { "wpa_cli", "-i", "wlan0", "ping", NULL };
    return net_run(out, sizeof out, 1500, argv) == 0 && !strncmp(out, "PONG", 4);
}

static bool wpa_ok(const char *a1, const char *a2, const char *a3, const char *a4)
{
    char out[256];
    return wpa(out, sizeof out, a1, a2, a3, a4) == 0 && !strncmp(out, "OK", 2);
}

/* wpa_cli expects a quoted string, with embedded quotes and backslashes
 * escaped. SSIDs and passwords are user input, so do not build a shell line. */
static bool wpa_quote(char *dst, size_t cap, const char *src)
{
    size_t n = 0;
    if (cap < 3) return false;
    dst[n++] = '"';
    for (; *src; src++)
    {
        if (n + 3 >= cap) return false;
        if (*src == '"' || *src == '\\') dst[n++] = '\\';
        dst[n++] = *src;
    }
    dst[n++] = '"';
    dst[n] = '\0';
    return true;
}

/* wpa_cli prints SSIDs with \xNN, \\ and \" escapes */
static void wpa_unescape(char *dst, size_t n, const char *src, size_t len)
{
    size_t o = 0;
    for (size_t i = 0; i < len && o + 1 < n; i++)
    {
        if (src[i] == '\\' && i + 1 < len)
        {
            if (src[i + 1] == 'x' && i + 3 < len)
            {
                char hex[3] = { src[i + 2], src[i + 3], 0 };
                dst[o++] = (char)strtol(hex, NULL, 16);
                i += 3;
                continue;
            }
            i++;
        }
        dst[o++] = src[i];
    }
    dst[o] = '\0';
}

/* the saved network with this name: its id, or -1 */
static int wpa_saved_id(const char *ssid)
{
    static char out[4096];
    if (wpa(out, sizeof out, "list_networks", NULL, NULL, NULL)) return -1;
    char *line = strchr(out, '\n');           /* skip the header */
    while (line && *++line)
    {
        char *end = strchr(line, '\n');
        size_t len = end ? (size_t)(end - line) : strlen(line);
        char *tab = memchr(line, '\t', len);
        if (tab)
        {
            char *tab2 = memchr(tab + 1, '\t', len - (size_t)(tab + 1 - line));
            char name[33];
            wpa_unescape(name, sizeof name, tab + 1, tab2 ? (size_t)(tab2 - tab - 1) : len - (size_t)(tab + 1 - line));
            if (!strcmp(name, ssid)) return atoi(line);
        }
        line = end;
    }
    return -1;
}

/* An AIC8800 unit on the 2.0 system: HiBy's own power gate. wifi_on.sh
 * loads aic8800_fdrv, sets the MAC, starts the supplicant and DHCP;
 * wifi_off.sh stops them and unloads the driver, so the chip draws
 * nothing. No SDIO bind here: that is the Broadcom driver's. */
static bool aic_wifi_power(bool on)
{
    if (on)
    {
        /* wifi_on.sh copies /etc/wpa_supplicant_default.conf, which 2.0
         * does not ship, when the saved one is missing; write the file
         * HiBy's S52wifi_aic_init_config would */
        net_sh(NULL, 0, 3000,
               "[ -s /usr/data/wpa_supplicant.conf ] || printf 'ctrl_interface=/var/run/wpa_supplicant\\n"
               "update_config=1\\ncountry=GB\\n' > /usr/data/wpa_supplicant.conf");
        /* it waits up to 10 s for the boot-time driver, 5 s for wlan0 and
         * 5 s for the supplicant; DHCP goes on in the background */
        if (net_sh(NULL, 0, 30000, "/usr/bin/wifi_on.sh >/dev/null 2>&1"))
        {
            wifi_last_error = "stock wifi_on.sh failed (AIC8800)";
            net_sh(wifi_detail, sizeof wifi_detail, 3000,
                   "echo \"base $(cat /run/r1_wireless_loaded 2>/dev/null); gate $(ls /run 2>/dev/null | grep aic_ | tr '\\n' ' ')\";"
                   "dmesg 2>/dev/null | grep -i -E 'aic|wlan|sdio' | tail -n 3");
            return false;
        }
        for (int i = 0; i < 20; i++)
        {
            if (wpa_ready()) return true;
            net_sleep_ms(500);
        }
        wifi_last_error = "wpa_supplicant did not answer";
        return false;
    }
    const char *off[] = { "/usr/bin/wifi_off.sh", NULL };
    int rc = net_run(NULL, 0, 15000, off);
    if (rc || wpa_ready()) {
        wifi_last_error = "stock wifi_off.sh failed or service stayed up";
        return false;
    }
    return true;
}

bool sl_net_wifi_power(bool on)
{
    wifi_last_error = NULL;
    net_start_error[0] = '\0';
    wifi_detail[0] = '\0';
    /* an AIC8800 unit without HiBy 2.0's driver: bind nothing */
    if (on && sl_net_wireless_unsupported()) { wifi_last_error = "this R1's AIC8800 wireless chip is not supported yet"; return false; }
    if (sl_net_wireless_aic()) return aic_wifi_power(on);
    if (on)
    {
        /* Shut down a supplicant left by HiBy or an earlier Rockbox run
         * before binding the radio. wifi_down.sh may itself unbind SDIO;
         * doing this after the bind can remove wlan0 again. */
        const char *down[] = { "wifi_down.sh", NULL };
        net_run(NULL, 0, 5000, down);

        /* Boot menus older than the one in bootloader/hibyos_linux.c
         * unbind SDIO; the bind below is the only way back, and it has
         * failed on every R1 log so far. Run the stock init step first:
         * on some boots its bind node does not exist until it runs. */
        const char *init[] = { "/etc/init.d/S43wifi_bcm_init_config", "start", NULL };
        net_run(NULL, 0, 5000, init);
        /* wifi_down.sh ends with "rfkill block wifi", which powers the
         * radio off; only wifi_up.sh unblocks it, and that runs after the
         * bind. The bootloader runs wifi_down.sh too, so unblock first and
         * give the chip a moment to come back on the SDIO bus. */
        net_sh(NULL, 0, 3000, "rfkill unblock wifi");
        for (int i = 0; i < 30 && access("/sys/bus/sdio/devices/mmc0:0001:2", F_OK); i++)
            net_sleep_ms(100);
        if (access("/sys/class/net/wlan0", F_OK))
        {
            if (access("/sys/bus/sdio/drivers/bcmsdh_sdmmc/bind", W_OK)) {
                wifi_last_error = "Wi-Fi driver bind node missing";
                return false;
            }
            if (net_sh(NULL, 0, 3000,
                       "echo mmc0:0001:2 > /sys/bus/sdio/drivers/bcmsdh_sdmmc/bind")) {
                wifi_last_error = access("/sys/bus/sdio/devices/mmc0:0001:2", F_OK) ?
                                  "SDIO radio bind failed: radio not on the bus" :
                                  "SDIO radio bind failed";
                net_sh(wifi_detail, sizeof wifi_detail, 3000,
                       "{ echo mmc0:0001:2 > /sys/bus/sdio/drivers/bcmsdh_sdmmc/bind; } 2>&1 | tail -n 1;"
                       "d=$(readlink /sys/bus/sdio/devices/mmc0:0001:2/driver 2>/dev/null);"
                       "echo \"driver ${d##*/}; rfkill $(cat /sys/class/rfkill/*/state 2>/dev/null | tr '\\n' ' ')\";"
                       "dmesg 2>/dev/null | grep -i -E 'dhd|bcm|sdio|wlan|wifi' | tail -n 3");
                return false;
            }
        }
        for (int i = 0; i < 40 && access("/sys/class/net/wlan0", F_OK); i++) net_sleep_ms(250);
        if (access("/sys/class/net/wlan0", F_OK)) {
            wifi_last_error = "radio missing after SDIO bind";
            return false;
        }

        /* Assign the hardware MAC after the rebind. The stock R1 1.6 image
         * uses wifi_up.sh with /usr/data/wpa_supplicant.conf; wifi_on.sh
         * references a nonexistent default config. */
        net_run(NULL, 0, 5000, init);
        /* The stock script backgrounds DHCP. Redirect its output before
         * launching it, so the background child cannot hold net_run's pipe
         * open and make a successful start look like a timeout. */
        if (net_sh(NULL, 0, 5000,
                   "/usr/bin/wifi_up.sh /usr/data/wpa_supplicant.conf >/dev/null 2>&1")) {
            wifi_last_error = "stock wifi_up.sh failed";
            return false;
        }
        for (int i = 0; i < 20; i++)
        {
            if (wpa_ready()) return true;
            net_sleep_ms(500);
        }
        wifi_last_error = "wpa_supplicant did not answer";
        return false;
    }
    /* Off is HiBy's own off: no supplicant, interface down, radio blocked.
     * The radio stays bound to its driver. A bind after an unbind fails
     * on the R1 every time, so unbinding here lost Wi-Fi until a reboot. */
    const char *down[] = { "wifi_down.sh", NULL };
    int rc = net_run(NULL, 0, 5000, down);
    if (rc || wpa_ready()) {
        wifi_last_error = "stock wifi_down.sh failed or service stayed up";
        return false;
    }
    return true;
}

bool sl_net_wifi_radio_missing(void)
{
    /* AIC: wlan0 exists only while Wi-Fi is on (the driver loads on demand) */
    if (sl_net_wireless_aic()) return false;
    return access("/sys/class/net/wlan0", F_OK) != 0;
}

/* The status, and the supplicant's wpa_state (COMPLETED, SCANNING, ...)
 * into state when it is not NULL; empty when the supplicant is not up. */
static void wifi_status(struct sl_wifi_status *s, char *state, size_t n)
{
    static char out[2048];
    memset(s, 0, sizeof *s);
    if (state) state[0] = '\0';
    if (access("/sys/class/net/wlan0", F_OK)) return;
    if (wpa(out, sizeof out, "status", NULL, NULL, NULL)) return;
    if (!strstr(out, "wpa_state=")) return;
    s->on = true;
    bool complete = false;
    for (char *line = out; line && *line; )
    {
        char *end = strchr(line, '\n');
        size_t len = end ? (size_t)(end - line) : strlen(line);
        if (!strncmp(line, "wpa_state=", 10))
        {
            complete = len == 19 && !strncmp(line + 10, "COMPLETED", 9);
            if (state) snprintf(state, n, "%.*s", (int)(len - 10), line + 10);
        }
        else if (!strncmp(line, "ssid=", 5)) wpa_unescape(s->ssid, sizeof s->ssid, line + 5, len - 5);
        else if (!strncmp(line, "ip_address=", 11) && len - 11 < sizeof s->ip)
        { memcpy(s->ip, line + 11, len - 11); s->ip[len - 11] = '\0'; }
        line = end ? end + 1 : NULL;
    }
    if (complete && !s->ip[0])
    {
        struct ifaddrs *list, *a;
        if (!getifaddrs(&list))
        {
            for (a = list; a; a = a->ifa_next)
                if (a->ifa_addr && a->ifa_addr->sa_family == AF_INET &&
                    !strcmp(a->ifa_name, "wlan0"))
                    inet_ntop(AF_INET, &((struct sockaddr_in *)a->ifa_addr)->sin_addr,
                              s->ip, sizeof s->ip);
            freeifaddrs(list);
        }
        if (!strcmp(s->ip, "0.0.0.0")) s->ip[0] = '\0';
    }
    s->connected = complete && s->ip[0];
}

void sl_net_wifi_status(struct sl_wifi_status *s) { wifi_status(s, NULL, 0); }

static int ap_cmp(const void *a, const void *b)
{
    return ((const struct sl_wifi_ap *)b)->signal - ((const struct sl_wifi_ap *)a)->signal;
}

int sl_net_wifi_scan(struct sl_wifi_ap *aps, int max)
{
    static char out[8192];
    wifi_last_error = NULL;
    net_start_error[0] = '\0';
    /* FAIL-BUSY: the supplicant is already scanning (it does right after
     * it starts) or joining; its results are as good as ours */
    if (wpa(out, sizeof out, "scan", NULL, NULL, NULL) ||
        (strncmp(out, "OK", 2) && strncmp(out, "FAIL-BUSY", 9))) {
        wifi_last_error = "wpa_cli scan failed";
        return -1;
    }
    for (int tries = 0; ; tries++)
    {
        net_sleep_ms(3500);
        if (wpa(out, sizeof out, "scan_results", NULL, NULL, NULL) ||
            strncmp(out, "bssid", 5)) {
            wifi_last_error = "wpa_cli scan_results failed";
            return -1;
        }
        char *first = strchr(out, '\n');
        if (tries || (first && first[1])) break;    /* none yet: the scan may still run */
    }
    int n = 0;
    char *line = strchr(out, '\n');           /* bssid / frequency / signal / flags / ssid */
    while (line && *++line)
    {
        char *end = strchr(line, '\n');
        size_t len = end ? (size_t)(end - line) : strlen(line);
        char *f[5]; int k = 0;
        f[k++] = line;
        for (size_t i = 0; i < len && k < 5; i++) if (line[i] == '\t') f[k++] = line + i + 1;
        if (k == 5)
        {
            struct sl_wifi_ap ap;
            memset(&ap, 0, sizeof ap);
            wpa_unescape(ap.ssid, sizeof ap.ssid, f[4], len - (size_t)(f[4] - line));
            ap.signal = atoi(f[2]);
            char flags[160];
            size_t fl = (size_t)(f[4] - f[3]) < sizeof flags ? (size_t)(f[4] - f[3]) : sizeof flags - 1;
            memcpy(flags, f[3], fl);
            flags[fl] = '\0';
            ap.secure = strstr(flags, "WPA") || strstr(flags, "WEP") || strstr(flags, "RSN") || strstr(flags, "SAE");
            int dup = -1;
            for (int i = 0; i < n; i++) if (!strcmp(aps[i].ssid, ap.ssid)) dup = i;
            if (ap.ssid[0] && dup < 0 && n < max) aps[n++] = ap;
            else if (dup >= 0 && ap.signal > aps[dup].signal) aps[dup].signal = ap.signal;
        }
        line = end;
    }
    for (int i = 0; i < n; i++) aps[i].saved = wpa_saved_id(aps[i].ssid) >= 0;
    qsort(aps, (size_t)n, sizeof *aps, ap_cmp);
    return n;
}

/* true once the supplicant has set this network aside after failed
 * attempts, which after a handshake is nearly always the password */
static bool wpa_temp_disabled(const char *id)
{
    static char out[4096];
    size_t n = strlen(id);
    if (wpa(out, sizeof out, "list_networks", NULL, NULL, NULL)) return false;
    for (char *line = out; line; line = strchr(line, '\n'), line = line ? line + 1 : NULL)
    {
        if (strncmp(line, id, n) || line[n] != '\t') continue;
        char *end = strchr(line, '\n');
        if (end) *end = '\0';
        return strstr(line, "[TEMP-DISABLED]") != NULL;
    }
    return false;
}

bool sl_net_wifi_connect(const char *ssid, const char *psk) { return sl_net_wifi_connect_ex(ssid, psk, false); }
bool sl_net_wifi_connect_ex(const char *ssid, const char *psk, bool hidden)
{
    char out[256], id[16], quoted[140];
    wifi_last_error = "Could not join the network";
    net_start_error[0] = '\0';
    int saved = wpa_saved_id(ssid), nid = saved;
    bool added = false;
    if (saved < 0 || psk || hidden)
    {
        if (wpa(out, sizeof out, "add_network", NULL, NULL, NULL)) return false;
        char *end;
        long parsed = strtol(out, &end, 10);
        if (end == out || (*end != '\n' && *end != '\0') || parsed < 0 || parsed > 99999) return false;
        nid = (int)parsed;
        added = true;
        snprintf(id, sizeof id, "%d", nid);
        if (!wpa_quote(quoted, sizeof quoted, ssid) ||
            !wpa_ok("set_network", id, "ssid", quoted)) goto failed;
        if (hidden && !wpa_ok("set_network", id, "scan_ssid", "1")) goto failed;   /* ask for it by name */
        if (psk && *psk)
        {
            if (!wpa_quote(quoted, sizeof quoted, psk) ||
                !wpa_ok("set_network", id, "psk", quoted)) goto failed;
        }
        else if (!wpa_ok("set_network", id, "key_mgmt", "NONE")) goto failed;
    }
    snprintf(id, sizeof id, "%d", nid);
    if (!wpa_ok("select_network", id, NULL, NULL)) goto failed;
    /* What the supplicant got to says why a join failed. The udhcpc that
     * wifi_up.sh started may be resting up to 20 s between attempts, or
     * hold a lease from the last network: once the link is up, make it
     * drop that lease (USR2) and ask this network at once (USR1). */
    struct sl_wifi_status st;
    char state[24];
    bool dhcp_asked = false;
    wifi_last_error = "Network not found";
    for (int i = 0; i < 60; i++)              /* up to 30 s for the password and an address */
    {
        net_sleep_ms(500);
        wifi_status(&st, state, sizeof state);
        if (!strcmp(state, "COMPLETED") && !strcmp(st.ssid, ssid))
        {
            if (!dhcp_asked)
            {
                net_sh(NULL, 0, 3000, "killall -USR2 udhcpc && killall -USR1 udhcpc ||"
                       " { udhcpc -i wlan0 >/dev/null 2>&1 & }");
                dhcp_asked = true;
                wifi_last_error = "Joined, but the network gave no address";
                continue;
            }
            if (st.connected) break;
        }
        else if (!dhcp_asked)
        {
            /* a handshake only happens with a password, and only fails on it */
            if (!strcmp(state, "4WAY_HANDSHAKE") || !strcmp(state, "GROUP_HANDSHAKE"))
                wifi_last_error = "Wrong password";
            else if (!strcmp(wifi_last_error, "Network not found") &&
                     (!strcmp(state, "ASSOCIATING") || !strcmp(state, "ASSOCIATED") ||
                      !strcmp(state, "AUTHENTICATING")))
                wifi_last_error = "Could not join the network";
            if ((i & 3) == 3 && wpa_temp_disabled(id))   /* it gave up: no use waiting */
            {
                if (!strcmp(wifi_last_error, "Network not found"))
                    wifi_last_error = "Could not join the network";
                break;
            }
        }
    }
    bool ok = st.connected && !strcmp(st.ssid, ssid);
    if (!ok) goto failed;
    wifi_last_error = NULL;
    if (added && saved >= 0)
    {
        char old_id[16];
        snprintf(old_id, sizeof old_id, "%d", saved);
        wpa_ok("remove_network", old_id, NULL, NULL);
    }
    wpa_ok("enable_network", "all", NULL, NULL);
    wpa_ok("set", "update_config", "1", NULL);
    wpa_ok("save_config", NULL, NULL, NULL);
    return true;
failed:
    if (added) wpa_ok("remove_network", id, NULL, NULL);
    wpa_ok("enable_network", "all", NULL, NULL);
    return false;
}

bool sl_net_wifi_forget(const char *ssid)
{
    char id[16];
    int saved = wpa_saved_id(ssid);
    if (saved < 0) return false;
    snprintf(id, sizeof id, "%d", saved);
    if (!wpa_ok("remove_network", id, NULL, NULL)) return false;
    wpa_ok("set", "update_config", "1", NULL);
    return wpa_ok("save_config", NULL, NULL, NULL);
}

bool sl_net_ntp(void)
{
    /* what HiBy's player runs, then keep the hardware clock in step */
    return net_sh(NULL, 0, 30000, "ntpdate 0.pool.ntp.org time.windows.com >/dev/null 2>&1 &&"
                  " hwclock -w --utc >/dev/null 2>&1") == 0;
}

/* HiBy's transfer page: thttpd over /usr/share/web, whose CGIs write
 * straight to the card */
bool sl_net_share_start(void)
{
    net_sh(NULL, 0, 3000, "kill $(cat /tmp/sloppy-thttpd.pid 2>/dev/null) 2>/dev/null");
    const char *argv[] = { "thttpd", "-d", "/usr/share/web", "-p", "4399", "-c", "**.cgi",
                           "-u", "root", "-nos", "-l", "/dev/null", "-i", "/tmp/sloppy-thttpd.pid", NULL };
    return net_run(NULL, 0, 5000, argv) == 0;
}
void sl_net_share_stop(void)
{
    net_sh(NULL, 0, 3000, "kill $(cat /tmp/sloppy-thttpd.pid 2>/dev/null) 2>/dev/null;"
           " rm -f /tmp/sloppy-thttpd.pid");
}
#endif /* NET_DEMO */

/* -------------------------------------------------------------- AirPlay */
/* shairport writes raw PCM into a FIFO; a reader thread moves it into a
 * ring the mixer drains. One writer, one reader: the indices are enough. */
#define AP_FIFO "/tmp/sloppy-airplay"
#define AP_RING (1 << 15)                /* frames, about 0.74 s */
static int16_t ap_ring[AP_RING * 2];
static volatile uint32_t ap_head, ap_tail;   /* written by the thread / the mixer */
static volatile uint32_t ap_last_ms;
static volatile bool ap_run;
static pid_t ap_pid;
static pthread_t ap_thread;
static bool ap_thread_up;

static void *ap_reader(void *unused)
{
    (void)unused;
    static uint8_t buf[4096];
    size_t have = 0;
    while (ap_run)
    {
        int fd = open(AP_FIFO, O_RDONLY);    /* waits for shairport */
        if (fd < 0) { net_sleep_ms(200); continue; }
        for (;;)
        {
            ssize_t r = read(fd, buf + have, sizeof buf - have);
            if (r <= 0 || !ap_run) break;
            have += (size_t)r;
            size_t frames = have / 4;
            for (size_t i = 0; i < frames && ap_run; )
            {
                uint32_t space = AP_RING - (ap_head - ap_tail);
                if (!space) { net_sleep_ms(5); continue; }   /* playing at its own pace */
                uint32_t n = (uint32_t)(frames - i) < space ? (uint32_t)(frames - i) : space;
                for (uint32_t k = 0; k < n; k++, i++)
                {
                    uint32_t at = (ap_head + k) & (AP_RING - 1);
                    memcpy(&ap_ring[at * 2], buf + i * 4, 4);
                }
                __sync_synchronize();
                ap_head += n;
            }
            memmove(buf, buf + frames * 4, have - frames * 4);
            have -= frames * 4;
            ap_last_ms = net_ms();
        }
        close(fd);
        have = 0;
    }
    return NULL;
}

bool sl_net_airplay_start(const char *name)
{
    if (ap_run) return true;
    unlink(AP_FIFO);
    if (mkfifo(AP_FIFO, 0600)) return false;
    ap_head = ap_tail = 0;
    ap_last_ms = net_ms() - 60000;
    ap_run = true;
    ap_thread_up = pthread_create(&ap_thread, NULL, ap_reader, NULL) == 0;
    if (!ap_thread_up) { ap_run = false; return false; }
#ifdef NET_DEMO
    (void)name;                           /* write to the FIFO yourself to test */
    return true;
#else
    const char *argv[] = { "shairport", "-a", name, "-o", "pipe", "--", AP_FIFO, NULL };
    ap_pid = net_spawn(argv);
    net_sleep_ms(300);
    if (ap_pid > 0 && waitpid(ap_pid, NULL, WNOHANG) == 0) return true;
    ap_pid = 0;
    sl_net_airplay_stop();
    return false;
#endif
}

void sl_net_airplay_stop(void)
{
    if (!ap_thread_up) return;
    ap_run = false;
    net_reap(&ap_pid);
    int fd = open(AP_FIFO, O_WRONLY | O_NONBLOCK);   /* wakes a reader waiting in open() */
    if (fd >= 0) close(fd);
    pthread_join(ap_thread, NULL);
    ap_thread_up = false;
    unlink(AP_FIFO);
}

size_t sl_net_airplay_read(int16_t *dst, size_t frames)
{
    uint32_t have = ap_head - ap_tail;
    if (frames > have) frames = have;
    for (size_t k = 0; k < frames; k++)
    {
        uint32_t at = (ap_tail + (uint32_t)k) & (AP_RING - 1);
        dst[k * 2] = ap_ring[at * 2];
        dst[k * 2 + 1] = ap_ring[at * 2 + 1];
    }
    __sync_synchronize();
    ap_tail += (uint32_t)frames;
    return frames;
}

uint32_t sl_net_airplay_idle_ms(void) { return net_ms() - ap_last_ms; }

/* ----------------------------------------------------------------- DLNA */
/* A small UPnP MediaRenderer: SSDP discovery, a device description and the
 * three services, SOAP control. What a phone sends is downloaded to the card
 * and then played by Rockbox like any other file. */
#define DLNA_PORT 49494
#define DLNA_QUEUE 8

static pthread_mutex_t dl_lock = PTHREAD_MUTEX_INITIALIZER;
static struct sl_dlna_cmd dl_queue[DLNA_QUEUE];
static int dl_qhead, dl_qtail;
static struct sl_dlna_state dl_state;       /* from the Rockbox thread */
static char dl_uri[1024], dl_meta[2048], dl_file[128], dl_title[96];
static int dl_gen;                          /* bumps on every new URI */
static volatile bool net_card_held;         /* USB mode: no file on the card (sl_net_scrobble_hold) */
static bool dl_downloading, dl_want_play, dl_have_file;
static volatile bool dl_run;
static pthread_t dl_thread;
static bool dl_thread_up;
static char dl_name[64], dl_uuid[48];
static int dl_http = -1, dl_ssdp = -1;

static void dl_push(int type, long value, const char *path, const char *title)
{
    pthread_mutex_lock(&dl_lock);
    if ((dl_qtail + 1) % DLNA_QUEUE != dl_qhead)
    {
        struct sl_dlna_cmd *c = &dl_queue[dl_qtail];
        memset(c, 0, sizeof *c);
        c->type = type;
        c->value = value;
        if (path) strncpy(c->path, path, sizeof c->path - 1);
        if (title) strncpy(c->title, title, sizeof c->title - 1);
        dl_qtail = (dl_qtail + 1) % DLNA_QUEUE;
    }
    pthread_mutex_unlock(&dl_lock);
}

bool sl_net_dlna_poll(struct sl_dlna_cmd *cmd)
{
    bool got = false;
    pthread_mutex_lock(&dl_lock);
    if (dl_qhead != dl_qtail)
    {
        *cmd = dl_queue[dl_qhead];
        dl_qhead = (dl_qhead + 1) % DLNA_QUEUE;
        got = true;
    }
    pthread_mutex_unlock(&dl_lock);
    return got;
}

void sl_net_dlna_report(const struct sl_dlna_state *st)
{
    pthread_mutex_lock(&dl_lock);
    dl_state = *st;
    pthread_mutex_unlock(&dl_lock);
}

bool sl_net_dlna_busy(void) { return dl_downloading; }

/* text between <tag ...> and </tag>, tag given without a namespace */
static bool xml_arg(const char *xml, const char *tag, char *out, size_t n)
{
    char open1[64];
    const char *p = xml;
    out[0] = '\0';
    snprintf(open1, sizeof open1, "%s>", tag);
    while ((p = strstr(p, open1)))
    {
        /* the character before is '<' or ':' (a prefix) */
        if (p > xml && (p[-1] == '<' || p[-1] == ':'))
        {
            const char *start = p + strlen(open1);
            const char *end = strstr(start, "</");
            while (end)
            {
                const char *name = end + 2, *colon = strchr(name, ':'), *gt = strchr(name, '>');
                if (colon && gt && colon < gt) name = colon + 1;
                if (gt && !strncmp(name, tag, strlen(tag)) && name + strlen(tag) == gt) break;
                end = strstr(end + 2, "</");
            }
            if (!end) return false;
            size_t len = (size_t)(end - start) < n - 1 ? (size_t)(end - start) : n - 1;
            memcpy(out, start, len);
            out[len] = '\0';
            return true;
        }
        p += strlen(open1);
    }
    return false;
}

static void xml_unescape(char *s)
{
    static const struct { const char *e; char c; } map[] = {
        { "&lt;", '<' }, { "&gt;", '>' }, { "&quot;", '"' }, { "&apos;", '\'' }, { "&amp;", '&' } };
    char *o = s;
    for (char *i = s; *i; )
    {
        bool done = false;
        if (*i == '&')
            for (unsigned k = 0; k < sizeof map / sizeof map[0]; k++)
                if (!strncmp(i, map[k].e, strlen(map[k].e))) { *o++ = map[k].c; i += strlen(map[k].e); done = true; break; }
        if (!done) *o++ = *i++;
    }
    *o = '\0';
}

static size_t xml_escape(char *out, size_t n, const char *s)
{
    size_t o = 0;
    for (; s && *s && o + 7 < n; s++)
    {
        const char *r = *s == '<' ? "&lt;" : *s == '>' ? "&gt;" : *s == '&' ? "&amp;" : *s == '"' ? "&quot;" : NULL;
        if (r) { size_t l = strlen(r); memcpy(out + o, r, l); o += l; }
        else out[o++] = *s;
    }
    out[o] = '\0';
    return o;
}

static void hms(char *b, size_t n, long ms)
{
    long s = ms < 0 ? 0 : ms / 1000;
    snprintf(b, n, "%ld:%02ld:%02ld", s / 3600, s / 60 % 60, s % 60);
}

static long parse_hms(const char *t)
{
    long h = 0, m = 0; double s = 0;
    if (sscanf(t, "%ld:%ld:%lf", &h, &m, &s) == 3) return (long)((h * 3600 + m * 60 + s) * 1000);
    return -1;
}

/* ---- download: plain HTTP, redirects followed */
static const char *dl_ext_for(const char *url, const char *ctype)
{
    static const char *exts[] = { ".mp3", ".flac", ".ogg", ".opus", ".wav", ".m4a", ".aac", ".wma",
                                  ".ape", ".aiff", ".aif", ".dsf", ".dff", ".mpc", ".wv", NULL };
    char path[512];
    strncpy(path, url, sizeof path - 1);
    path[sizeof path - 1] = '\0';
    char *q = strpbrk(path, "?#");
    if (q) *q = '\0';
    size_t n = strlen(path);
    for (int i = 0; exts[i]; i++)
    {
        size_t e = strlen(exts[i]);
        if (n > e && !strcasecmp(path + n - e, exts[i])) return exts[i];
    }
    static const struct { const char *type, *ext; } types[] = {
        { "flac", ".flac" }, { "wav", ".wav" }, { "wave", ".wav" }, { "L16", ".wav" }, { "mp4", ".m4a" },
        { "m4a", ".m4a" }, { "aac", ".aac" }, { "ogg", ".ogg" }, { "opus", ".opus" }, { "wma", ".wma" },
        { "aiff", ".aiff" }, { "ape", ".ape" }, { "dsf", ".dsf" }, { "dff", ".dff" } };
    for (unsigned i = 0; ctype && i < sizeof types / sizeof types[0]; i++)
        if (strcasestr(ctype, types[i].type)) return types[i].ext;
    return ".mp3";
}

/* Download url into file (a real path). Returns true when complete. */
static bool dl_fetch(const char *url, const char *base, char *file, size_t filen, int gen)
{
    char cur[1024];
    strncpy(cur, url, sizeof cur - 1);
    cur[sizeof cur - 1] = '\0';
    for (int hop = 0; hop < 4; hop++)
    {
        if (strncasecmp(cur, "http://", 7)) return false;   /* https needs TLS; phones on a LAN use http */
        char host[256], port[8] = "80";
        const char *h = cur + 7, *slash = strchr(h, '/');
        size_t hl = slash ? (size_t)(slash - h) : strlen(h);
        if (hl >= sizeof host) return false;
        memcpy(host, h, hl); host[hl] = '\0';
        char *colon = strrchr(host, ':');
        if (colon && !strchr(host, ']')) { strncpy(port, colon + 1, sizeof port - 1); *colon = '\0'; }
        const char *path = slash ? slash : "/";
        struct addrinfo hints, *ai;
        memset(&hints, 0, sizeof hints);
        hints.ai_socktype = SOCK_STREAM;
        if (getaddrinfo(host, port, &hints, &ai)) return false;
        int s = socket(ai->ai_family, SOCK_STREAM, 0);
        struct timeval tv = { 15, 0 };
        setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
        /* 8 s to answer, and not past a newer song: a blocking connect to a
         * host that never answers held each SetAVTransportURI's thread two
         * minutes, and anyone on the network could pile them up */
        int r = -1, err = 0, ready = 0;
        socklen_t el = sizeof err;
        if (s >= 0)
        {
            fcntl(s, F_SETFL, O_NONBLOCK);
            r = connect(s, ai->ai_addr, ai->ai_addrlen);
            struct pollfd pw = { s, POLLOUT, 0 };
            for (int t = 0; r < 0 && errno == EINPROGRESS && t < 16 && gen == dl_gen && !ready; t++) ready = poll(&pw, 1, 500) == 1;
            if (r < 0 && ready && !getsockopt(s, SOL_SOCKET, SO_ERROR, &err, &el) && !err) r = 0;
            fcntl(s, F_SETFL, 0);
        }
        if (s < 0 || r) { if (s >= 0) close(s); freeaddrinfo(ai); return false; }
        freeaddrinfo(ai);
        char req[1400];
        int rl = snprintf(req, sizeof req, "GET %s HTTP/1.0\r\nHost: %s\r\nUser-Agent: GabagoolOS\r\n"
                          "Accept: */*\r\nConnection: close\r\n\r\n", path, host);
        if (rl <= 0 || rl >= (int)sizeof req || send(s, req, (size_t)rl, 0) != rl) { close(s); return false; }
        /* headers */
        static char head[8192];
        size_t hn = 0;
        char *body = NULL;
        while (hn < sizeof head - 1)
        {
            ssize_t r = recv(s, head + hn, sizeof head - 1 - hn, 0);
            if (r <= 0) break;
            hn += (size_t)r;
            head[hn] = '\0';
            if ((body = strstr(head, "\r\n\r\n"))) { body += 4; break; }
        }
        if (!body) { close(s); return false; }
        int code = 0;
        sscanf(head, "HTTP/%*s %d", &code);
        char ctype[128] = "", location[1024] = "";
        for (char *line = strstr(head, "\r\n"); line && line + 2 < body; line = strstr(line + 2, "\r\n"))
        {
            char *l = line + 2, *e = strstr(l, "\r\n");
            size_t len = e ? (size_t)(e - l) : 0;
            if (!strncasecmp(l, "Content-Type:", 13) && len - 13 < sizeof ctype)
            { memcpy(ctype, l + 13, len - 13); ctype[len - 13] = '\0'; }
            if (!strncasecmp(l, "Location:", 9) && len - 9 < sizeof location)
            { const char *v = l + 9; while (*v == ' ') v++; size_t vl = (size_t)(e - v); memcpy(location, v, vl); location[vl] = '\0'; }
        }
        if (code >= 300 && code < 400 && location[0])
        {
            close(s);
            if (location[0] == '/')
            {
                char tmp[1024];
                snprintf(tmp, sizeof tmp, "http://%s%s%s%s", host, strcmp(port, "80") ? ":" : "", strcmp(port, "80") ? port : "", location);
                strncpy(cur, tmp, sizeof cur - 1);
            }
            else strncpy(cur, location, sizeof cur - 1);
            continue;
        }
        if (code != 200) { close(s); return false; }
        snprintf(file, filen, "%s%s", base, dl_ext_for(url, ctype));
        char real[512];
        snprintf(real, sizeof real, "%s%s", net_root(), file);
        if (net_card_held) { close(s); return false; }   /* USB mode: the card is the computer's */
        int fd = open(real, O_WRONLY | O_CREAT | O_TRUNC, 0644);
        if (fd < 0) { close(s); return false; }
        bool ok = true;
        size_t first = hn - (size_t)(body - head), total = first;
        if (first && write(fd, body, first) != (ssize_t)first) ok = false;
        static char chunk[16384];
        while (ok && dl_run && gen == dl_gen && !net_card_held)
        {
            ssize_t r = recv(s, chunk, sizeof chunk, 0);
            if (r < 0) { ok = false; break; }
            if (r == 0) break;
            if (write(fd, chunk, (size_t)r) != r) ok = false;
            total += (size_t)r;
            if (total > (size_t)700 << 20) ok = false;          /* a runaway stream */
        }
        close(fd);
        close(s);
        if (gen != dl_gen || !dl_run || net_card_held) ok = false;
        if (!ok || !total) unlink(real);
        return ok && total;
    }
    return false;
}

static void *dl_download(void *arg)
{
    int gen = (int)(intptr_t)arg;
    char url[1024], meta[2048], title[96] = "", file[128];
    pthread_mutex_lock(&dl_lock);
    strcpy(url, dl_uri);
    strcpy(meta, dl_meta);
    pthread_mutex_unlock(&dl_lock);
    xml_unescape(meta);
    if (xml_arg(meta, "title", title, sizeof title)) xml_unescape(title);
    /* two names in turn, so the file playing now is never overwritten */
    char base[64];
    snprintf(base, sizeof base, SL_CAST_DIR "/cast-%d", gen & 1);
    bool ok = dl_fetch(url, base, file, sizeof file, gen);
    pthread_mutex_lock(&dl_lock);
    if (gen == dl_gen)
    {
        dl_downloading = false;
        dl_have_file = ok;
        if (ok) { strcpy(dl_file, file); strcpy(dl_title, title); }
    }
    bool play = dl_want_play;
    pthread_mutex_unlock(&dl_lock);
    if (gen == dl_gen)
    {
        if (ok && play) dl_push(SL_DLNA_LOAD, 1, file, title);   /* else wait for Play */
        else dl_push(SL_DLNA_STOP, 0, NULL, NULL);
    }
    return NULL;
}

/* ---- descriptions */
#define AVT "urn:schemas-upnp-org:service:AVTransport:1"
#define RCS "urn:schemas-upnp-org:service:RenderingControl:1"
#define CMS "urn:schemas-upnp-org:service:ConnectionManager:1"
#define RENDERER "urn:schemas-upnp-org:device:MediaRenderer:1"
#define SINK "http-get:*:audio/mpeg:*,http-get:*:audio/mp3:*,http-get:*:audio/flac:*,http-get:*:audio/x-flac:*," \
             "http-get:*:audio/wav:*,http-get:*:audio/x-wav:*,http-get:*:audio/wave:*,http-get:*:audio/mp4:*," \
             "http-get:*:audio/x-m4a:*,http-get:*:audio/aac:*,http-get:*:audio/ogg:*,http-get:*:audio/x-ms-wma:*," \
             "http-get:*:audio/aiff:*,http-get:*:audio/x-aiff:*,http-get:*:audio/ape:*,http-get:*:audio/dsf:*"

/* Actions as "Name:in Arg Var,out Arg Var;..." and variables as "Var:type,..." */
static const char avt_actions[] =
    "SetAVTransportURI:in InstanceID A_ARG_TYPE_InstanceID,in CurrentURI AVTransportURI,in CurrentURIMetaData AVTransportURIMetaData;"
    "GetMediaInfo:in InstanceID A_ARG_TYPE_InstanceID,out NrTracks NumberOfTracks,out MediaDuration CurrentMediaDuration,"
    "out CurrentURI AVTransportURI,out CurrentURIMetaData AVTransportURIMetaData,out NextURI NextAVTransportURI,"
    "out NextURIMetaData NextAVTransportURIMetaData,out PlayMedium PlaybackStorageMedium,out RecordMedium RecordStorageMedium,"
    "out WriteStatus RecordMediumWriteStatus;"
    "GetTransportInfo:in InstanceID A_ARG_TYPE_InstanceID,out CurrentTransportState TransportState,"
    "out CurrentTransportStatus TransportStatus,out CurrentSpeed TransportPlaySpeed;"
    "GetPositionInfo:in InstanceID A_ARG_TYPE_InstanceID,out Track CurrentTrack,out TrackDuration CurrentTrackDuration,"
    "out TrackMetaData CurrentTrackMetaData,out TrackURI CurrentTrackURI,out RelTime RelativeTimePosition,"
    "out AbsTime AbsoluteTimePosition,out RelCount RelativeCounterPosition,out AbsCount AbsoluteCounterPosition;"
    "GetDeviceCapabilities:in InstanceID A_ARG_TYPE_InstanceID,out PlayMedia PossiblePlaybackStorageMedia,"
    "out RecMedia PossibleRecordStorageMedia,out RecQualityModes PossibleRecordQualityModes;"
    "GetTransportSettings:in InstanceID A_ARG_TYPE_InstanceID,out PlayMode CurrentPlayMode,out RecQualityMode CurrentRecordQualityMode;"
    "Stop:in InstanceID A_ARG_TYPE_InstanceID;"
    "Play:in InstanceID A_ARG_TYPE_InstanceID,in Speed TransportPlaySpeed;"
    "Pause:in InstanceID A_ARG_TYPE_InstanceID;"
    "Seek:in InstanceID A_ARG_TYPE_InstanceID,in Unit A_ARG_TYPE_SeekMode,in Target A_ARG_TYPE_SeekTarget;"
    "Next:in InstanceID A_ARG_TYPE_InstanceID;"
    "Previous:in InstanceID A_ARG_TYPE_InstanceID;"
    "GetCurrentTransportActions:in InstanceID A_ARG_TYPE_InstanceID,out Actions CurrentTransportActions";
static const char avt_vars[] =
    "TransportState:string,TransportStatus:string,PlaybackStorageMedium:string,RecordStorageMedium:string,"
    "PossiblePlaybackStorageMedia:string,PossibleRecordStorageMedia:string,CurrentPlayMode:string,"
    "TransportPlaySpeed:string,RecordMediumWriteStatus:string,CurrentRecordQualityMode:string,"
    "PossibleRecordQualityModes:string,NumberOfTracks:ui4,CurrentTrack:ui4,CurrentTrackDuration:string,"
    "CurrentMediaDuration:string,CurrentTrackMetaData:string,CurrentTrackURI:string,AVTransportURI:string,"
    "AVTransportURIMetaData:string,NextAVTransportURI:string,NextAVTransportURIMetaData:string,"
    "RelativeTimePosition:string,AbsoluteTimePosition:string,RelativeCounterPosition:i4,AbsoluteCounterPosition:i4,"
    "CurrentTransportActions:string,LastChange:string,A_ARG_TYPE_SeekMode:string,A_ARG_TYPE_SeekTarget:string,"
    "A_ARG_TYPE_InstanceID:ui4";
static const char rcs_actions[] =
    "GetVolume:in InstanceID A_ARG_TYPE_InstanceID,in Channel A_ARG_TYPE_Channel,out CurrentVolume Volume;"
    "SetVolume:in InstanceID A_ARG_TYPE_InstanceID,in Channel A_ARG_TYPE_Channel,in DesiredVolume Volume;"
    "GetMute:in InstanceID A_ARG_TYPE_InstanceID,in Channel A_ARG_TYPE_Channel,out CurrentMute Mute;"
    "SetMute:in InstanceID A_ARG_TYPE_InstanceID,in Channel A_ARG_TYPE_Channel,in DesiredMute Mute;"
    "ListPresets:in InstanceID A_ARG_TYPE_InstanceID,out CurrentPresetNameList PresetNameList;"
    "SelectPreset:in InstanceID A_ARG_TYPE_InstanceID,in PresetName A_ARG_TYPE_PresetName";
static const char rcs_vars[] =
    "Volume:ui2,Mute:boolean,PresetNameList:string,LastChange:string,A_ARG_TYPE_Channel:string,"
    "A_ARG_TYPE_InstanceID:ui4,A_ARG_TYPE_PresetName:string";
static const char cms_actions[] =
    "GetProtocolInfo:out Source SourceProtocolInfo,out Sink SinkProtocolInfo;"
    "GetCurrentConnectionIDs:out ConnectionIDs CurrentConnectionIDs;"
    "GetCurrentConnectionInfo:in ConnectionID A_ARG_TYPE_ConnectionID,out RcsID A_ARG_TYPE_RcsID,"
    "out AVTransportID A_ARG_TYPE_AVTransportID,out ProtocolInfo A_ARG_TYPE_ProtocolInfo,"
    "out PeerConnectionManager A_ARG_TYPE_ConnectionManager,out PeerConnectionID A_ARG_TYPE_ConnectionID,"
    "out Direction A_ARG_TYPE_Direction,out Status A_ARG_TYPE_ConnectionStatus";
static const char cms_vars[] =
    "SourceProtocolInfo:string,SinkProtocolInfo:string,CurrentConnectionIDs:string,A_ARG_TYPE_ConnectionStatus:string,"
    "A_ARG_TYPE_ConnectionManager:string,A_ARG_TYPE_Direction:string,A_ARG_TYPE_ProtocolInfo:string,"
    "A_ARG_TYPE_ConnectionID:i4,A_ARG_TYPE_AVTransportID:i4,A_ARG_TYPE_RcsID:i4";

static size_t scpd(char *o, size_t n, const char *actions, const char *vars)
{
    size_t k = (size_t)snprintf(o, n, "<?xml version=\"1.0\"?><scpd xmlns=\"urn:schemas-upnp-org:service-1-0\">"
                                "<specVersion><major>1</major><minor>0</minor></specVersion><actionList>");
    char tmp[4096];
    strncpy(tmp, actions, sizeof tmp - 1);
    tmp[sizeof tmp - 1] = '\0';
    for (char *act = strtok(tmp, ";"); act && k < n; act = strtok(NULL, ";"))
    {
        char *colon = strchr(act, ':');
        if (colon) *colon = '\0';
        k += (size_t)snprintf(o + k, n - k, "<action><name>%s</name>", act);
        if (colon && colon[1])
        {
            k += (size_t)snprintf(o + k, n - k, "<argumentList>");
            for (char *arg = colon + 1; arg && *arg && k < n; )
            {
                char *next = strchr(arg, ',');
                if (next) *next = '\0';
                char dir[4], name[64], var[64];
                if (sscanf(arg, "%3s %63s %63s", dir, name, var) == 3)
                    k += (size_t)snprintf(o + k, n - k, "<argument><name>%s</name><direction>%s</direction>"
                                          "<relatedStateVariable>%s</relatedStateVariable></argument>",
                                          name, strcmp(dir, "in") ? "out" : "in", var);
                arg = next ? next + 1 : NULL;
            }
            k += (size_t)snprintf(o + k, n - k, "</argumentList>");
        }
        k += (size_t)snprintf(o + k, n - k, "</action>");
    }
    k += (size_t)snprintf(o + k, n - k, "</actionList><serviceStateTable>");
    strncpy(tmp, vars, sizeof tmp - 1);
    for (char *v = strtok(tmp, ","); v && k < n; v = strtok(NULL, ","))
    {
        char *colon = strchr(v, ':');
        if (!colon) continue;
        *colon = '\0';
        bool evented = !strcmp(v, "LastChange");
        k += (size_t)snprintf(o + k, n - k, "<stateVariable sendEvents=\"%s\"><name>%s</name><dataType>%s</dataType>"
                              "</stateVariable>", evented ? "yes" : "no", v, colon + 1);
    }
    k += (size_t)snprintf(o + k, n - k, "</serviceStateTable></scpd>");
    return k < n ? k : n - 1;
}

static size_t device_xml(char *o, size_t n)
{
    char name[128];
    xml_escape(name, sizeof name, dl_name);
    return (size_t)snprintf(o, n,
        "<?xml version=\"1.0\"?><root xmlns=\"urn:schemas-upnp-org:device-1-0\" xmlns:dlna=\"urn:schemas-dlna-org:device-1-0\">"
        "<specVersion><major>1</major><minor>0</minor></specVersion><device>"
        "<deviceType>" RENDERER "</deviceType><friendlyName>%s</friendlyName>"
        "<manufacturer>GabagoolOS</manufacturer><modelName>HiBy R1</modelName><modelNumber>1</modelNumber>"
        "<dlna:X_DLNADOC>DMR-1.50</dlna:X_DLNADOC><UDN>%s</UDN><serviceList>"
        "<service><serviceType>" AVT "</serviceType><serviceId>urn:upnp-org:serviceId:AVTransport</serviceId>"
        "<SCPDURL>/avt.xml</SCPDURL><controlURL>/ctl/avt</controlURL><eventSubURL>/evt/avt</eventSubURL></service>"
        "<service><serviceType>" RCS "</serviceType><serviceId>urn:upnp-org:serviceId:RenderingControl</serviceId>"
        "<SCPDURL>/rcs.xml</SCPDURL><controlURL>/ctl/rcs</controlURL><eventSubURL>/evt/rcs</eventSubURL></service>"
        "<service><serviceType>" CMS "</serviceType><serviceId>urn:upnp-org:serviceId:ConnectionManager</serviceId>"
        "<SCPDURL>/cms.xml</SCPDURL><controlURL>/ctl/cms</controlURL><eventSubURL>/evt/cms</eventSubURL></service>"
        "</serviceList></device></root>", name, dl_uuid);
}

/* ---- SOAP */
static const char *transport_state(void)
{
    if (dl_downloading) return "TRANSITIONING";
    if (!dl_have_file) return "NO_MEDIA_PRESENT";
    return dl_state.playing == 1 ? "PLAYING" : dl_state.playing == 2 ? "PAUSED_PLAYBACK" : "STOPPED";
}

/* Handle one action; the reply's arguments go into args. False = no such action. */
static bool soap_action(const char *service, const char *action, const char *body, char *args, size_t n)
{
    char v[1024], t1[16], t2[16], uri[1100];
    args[0] = '\0';
    pthread_mutex_lock(&dl_lock);
    struct sl_dlna_state st = dl_state;
    pthread_mutex_unlock(&dl_lock);
    if (!strcmp(service, AVT))
    {
        if (!strcmp(action, "SetAVTransportURI"))
        {
            char cur[1024], md[2048];
            xml_arg(body, "CurrentURI", cur, sizeof cur);
            xml_unescape(cur);
            xml_arg(body, "CurrentURIMetaData", md, sizeof md);
            pthread_mutex_lock(&dl_lock);
            strcpy(dl_uri, cur);
            strcpy(dl_meta, md);
            int gen = ++dl_gen;
            dl_downloading = true;
            dl_have_file = false;
            dl_want_play = false;
            pthread_mutex_unlock(&dl_lock);
            dl_push(SL_DLNA_STOP, 0, NULL, NULL);
            pthread_t t;
            if (pthread_create(&t, NULL, dl_download, (void *)(intptr_t)gen) == 0) pthread_detach(t);
            else dl_downloading = false;
        }
        else if (!strcmp(action, "Play"))
        {
            pthread_mutex_lock(&dl_lock);
            dl_want_play = true;
            bool ready = !dl_downloading && dl_have_file;
            char file[128], title[96];
            strcpy(file, dl_file);
            strcpy(title, dl_title);
            pthread_mutex_unlock(&dl_lock);
            if (ready && st.playing == 2) dl_push(SL_DLNA_PLAY, 0, NULL, NULL);
            else if (ready && st.playing == 0) dl_push(SL_DLNA_LOAD, 1, file, title);
        }
        else if (!strcmp(action, "Pause")) dl_push(SL_DLNA_PAUSE, 0, NULL, NULL);
        else if (!strcmp(action, "Stop")) { dl_want_play = false; dl_push(SL_DLNA_STOP, 0, NULL, NULL); }
        else if (!strcmp(action, "Seek"))
        {
            xml_arg(body, "Target", v, sizeof v);
            long ms = parse_hms(v);
            if (ms >= 0) dl_push(SL_DLNA_SEEK, ms, NULL, NULL);
        }
        else if (!strcmp(action, "Next") || !strcmp(action, "Previous")) {}
        else if (!strcmp(action, "GetTransportInfo"))
            snprintf(args, n, "<CurrentTransportState>%s</CurrentTransportState>"
                     "<CurrentTransportStatus>OK</CurrentTransportStatus><CurrentSpeed>1</CurrentSpeed>", transport_state());
        else if (!strcmp(action, "GetPositionInfo") || !strcmp(action, "GetMediaInfo"))
        {
            hms(t1, sizeof t1, st.length_ms);
            hms(t2, sizeof t2, st.elapsed_ms);
            pthread_mutex_lock(&dl_lock);
            xml_escape(uri, sizeof uri, dl_uri);
            pthread_mutex_unlock(&dl_lock);
            /* dl_meta is still escaped as it arrived, which is how it goes back */
            if (!strcmp(action, "GetPositionInfo"))
                snprintf(args, n, "<Track>%d</Track><TrackDuration>%s</TrackDuration><TrackMetaData>%s</TrackMetaData>"
                         "<TrackURI>%s</TrackURI><RelTime>%s</RelTime><AbsTime>%s</AbsTime>"
                         "<RelCount>2147483647</RelCount><AbsCount>2147483647</AbsCount>",
                         uri[0] ? 1 : 0, t1, dl_meta, uri, t2, t2);
            else
                snprintf(args, n, "<NrTracks>%d</NrTracks><MediaDuration>%s</MediaDuration><CurrentURI>%s</CurrentURI>"
                         "<CurrentURIMetaData>%s</CurrentURIMetaData><NextURI></NextURI><NextURIMetaData></NextURIMetaData>"
                         "<PlayMedium>NETWORK</PlayMedium><RecordMedium>NOT_IMPLEMENTED</RecordMedium>"
                         "<WriteStatus>NOT_IMPLEMENTED</WriteStatus>", uri[0] ? 1 : 0, t1, uri, dl_meta);
        }
        else if (!strcmp(action, "GetDeviceCapabilities"))
            snprintf(args, n, "<PlayMedia>NETWORK</PlayMedia><RecMedia>NOT_IMPLEMENTED</RecMedia>"
                     "<RecQualityModes>NOT_IMPLEMENTED</RecQualityModes>");
        else if (!strcmp(action, "GetTransportSettings"))
            snprintf(args, n, "<PlayMode>NORMAL</PlayMode><RecQualityMode>NOT_IMPLEMENTED</RecQualityMode>");
        else if (!strcmp(action, "GetCurrentTransportActions"))
            snprintf(args, n, "<Actions>Play,Pause,Stop,Seek</Actions>");
        else return false;
        return true;
    }
    if (!strcmp(service, RCS))
    {
        if (!strcmp(action, "GetVolume")) snprintf(args, n, "<CurrentVolume>%d</CurrentVolume>", st.volume);
        else if (!strcmp(action, "SetVolume"))
        {
            xml_arg(body, "DesiredVolume", v, sizeof v);
            int vol = atoi(v);
            dl_push(SL_DLNA_VOLUME, vol < 0 ? 0 : vol > 100 ? 100 : vol, NULL, NULL);
        }
        else if (!strcmp(action, "GetMute")) snprintf(args, n, "<CurrentMute>0</CurrentMute>");
        else if (!strcmp(action, "SetMute")) {}
        else if (!strcmp(action, "ListPresets")) snprintf(args, n, "<CurrentPresetNameList>FactoryDefaults</CurrentPresetNameList>");
        else if (!strcmp(action, "SelectPreset")) {}
        else return false;
        return true;
    }
    if (!strcmp(service, CMS))
    {
        if (!strcmp(action, "GetProtocolInfo")) snprintf(args, n, "<Source></Source><Sink>" SINK "</Sink>");
        else if (!strcmp(action, "GetCurrentConnectionIDs")) snprintf(args, n, "<ConnectionIDs>0</ConnectionIDs>");
        else if (!strcmp(action, "GetCurrentConnectionInfo"))
            snprintf(args, n, "<RcsID>0</RcsID><AVTransportID>0</AVTransportID><ProtocolInfo></ProtocolInfo>"
                     "<PeerConnectionManager></PeerConnectionManager><PeerConnectionID>-1</PeerConnectionID>"
                     "<Direction>Input</Direction><Status>OK</Status>");
        else return false;
        return true;
    }
    return false;
}

static void http_send(int c, const char *status, const char *ctype, const char *body, size_t len, const char *extra)
{
    char head[512];
    int hl = snprintf(head, sizeof head, "HTTP/1.1 %s\r\nContent-Type: %s\r\nContent-Length: %zu\r\n"
                      "Server: Linux/1.0 UPnP/1.0 GabagoolOS/1.0\r\nConnection: close\r\n%s\r\n",
                      status, ctype, len, extra ? extra : "");
    send(c, head, (size_t)hl, 0);
    if (len) send(c, body, len, 0);
}

static void http_client(int c)
{
    static char req[32768], out[24576], args[8192];
    size_t n = 0;
    struct timeval tv = { 3, 0 };
    setsockopt(c, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    char *body = NULL;
    size_t want = 0;
    while (n < sizeof req - 1)
    {
        ssize_t r = recv(c, req + n, sizeof req - 1 - n, 0);
        if (r <= 0) break;
        n += (size_t)r;
        req[n] = '\0';
        if (!body && (body = strstr(req, "\r\n\r\n")))
        {
            body += 4;
            char *cl = strcasestr(req, "\r\nContent-Length:");
            want = (size_t)(body - req) + (cl && cl < body ? (size_t)atol(cl + 17) : 0);
        }
        if (body && n >= want) break;
    }
    if (!body) return;
    char method[16], path[256];
    if (sscanf(req, "%15s %255s", method, path) != 2) return;
    if (!strcmp(method, "GET") || !strcmp(method, "HEAD"))
    {
        size_t len;
        if (!strcmp(path, "/desc.xml")) len = device_xml(out, sizeof out);
        else if (!strcmp(path, "/avt.xml")) len = scpd(out, sizeof out, avt_actions, avt_vars);
        else if (!strcmp(path, "/rcs.xml")) len = scpd(out, sizeof out, rcs_actions, rcs_vars);
        else if (!strcmp(path, "/cms.xml")) len = scpd(out, sizeof out, cms_actions, cms_vars);
        else { http_send(c, "404 Not Found", "text/plain", "", 0, NULL); return; }
        http_send(c, "200 OK", "text/xml; charset=\"utf-8\"", out, strcmp(method, "HEAD") ? len : 0, NULL);
        return;
    }
    if (!strcmp(method, "SUBSCRIBE"))
    {
        http_send(c, "200 OK", "text/plain", "", 0, "SID: uuid:5c0995d1-5100-4000-8000-000000000001\r\nTIMEOUT: Second-1800\r\n");
        return;
    }
    if (!strcmp(method, "UNSUBSCRIBE")) { http_send(c, "200 OK", "text/plain", "", 0, NULL); return; }
    if (strcmp(method, "POST")) { http_send(c, "405 Method Not Allowed", "text/plain", "", 0, NULL); return; }
    /* SOAPACTION: "urn:...:service:X:1#Action" */
    char *sa = strcasestr(req, "\r\nSOAPACTION:");
    if (!sa || sa > body) { http_send(c, "400 Bad Request", "text/plain", "", 0, NULL); return; }
    sa += 13;
    while (*sa == ' ' || *sa == '"') sa++;
    char service[128] = "", action[64] = "";
    char *hash = strchr(sa, '#');
    if (hash && (size_t)(hash - sa) < sizeof service)
    {
        memcpy(service, sa, (size_t)(hash - sa));
        service[hash - sa] = '\0';
        sscanf(hash + 1, "%63[A-Za-z]", action);
    }
    const char *svc = strstr(path, "avt") ? AVT : strstr(path, "rcs") ? RCS : CMS;
    if (!strstr(service, "AVTransport") && !strstr(service, "RenderingControl") && !strstr(service, "ConnectionManager"))
        strcpy(service, svc);
    else strcpy(service, strstr(service, "AVTransport") ? AVT : strstr(service, "RenderingControl") ? RCS : CMS);
    size_t len;
    if (soap_action(service, action, body, args, sizeof args))
    {
        len = (size_t)snprintf(out, sizeof out,
            "<?xml version=\"1.0\"?><s:Envelope xmlns:s=\"http://schemas.xmlsoap.org/soap/envelope/\" "
            "s:encodingStyle=\"http://schemas.xmlsoap.org/soap/encoding/\"><s:Body><u:%sResponse xmlns:u=\"%s\">%s"
            "</u:%sResponse></s:Body></s:Envelope>", action, service, args, action);
        http_send(c, "200 OK", "text/xml; charset=\"utf-8\"", out, len < sizeof out ? len : sizeof out - 1, "EXT:\r\n");
    }
    else
    {
        len = (size_t)snprintf(out, sizeof out,
            "<?xml version=\"1.0\"?><s:Envelope xmlns:s=\"http://schemas.xmlsoap.org/soap/envelope/\" "
            "s:encodingStyle=\"http://schemas.xmlsoap.org/soap/encoding/\"><s:Body><s:Fault><faultcode>s:Client</faultcode>"
            "<faultstring>UPnPError</faultstring><detail><UPnPError xmlns=\"urn:schemas-upnp-org:control-1-0\">"
            "<errorCode>401</errorCode><errorDescription>Invalid Action</errorDescription></UPnPError></detail>"
            "</s:Fault></s:Body></s:Envelope>");
        http_send(c, "500 Internal Server Error", "text/xml; charset=\"utf-8\"", out, len, NULL);
    }
}

/* ---- SSDP */
static const char *const ssdp_types[] = { "upnp:rootdevice", "", RENDERER, AVT, RCS, CMS };

static void ssdp_usn(char *usn, size_t n, const char *type)
{
    if (!type[0]) snprintf(usn, n, "%s", dl_uuid);
    else snprintf(usn, n, "%s::%s", dl_uuid, type);
}

static void ssdp_notify(const char *nts)
{
    char ip[16], msg[768], usn[256];
    net_local_ip(ip, sizeof ip);
    if (!ip[0]) return;
    struct sockaddr_in to;
    memset(&to, 0, sizeof to);
    to.sin_family = AF_INET;
    to.sin_port = htons(1900);
    to.sin_addr.s_addr = inet_addr("239.255.255.250");
    for (unsigned i = 0; i < sizeof ssdp_types / sizeof ssdp_types[0]; i++)
    {
        const char *nt = ssdp_types[i][0] ? ssdp_types[i] : dl_uuid;
        ssdp_usn(usn, sizeof usn, ssdp_types[i]);
        int len = snprintf(msg, sizeof msg, "NOTIFY * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\n"
                           "CACHE-CONTROL: max-age=1800\r\nLOCATION: http://%s:%d/desc.xml\r\nNT: %s\r\nNTS: %s\r\n"
                           "SERVER: Linux/1.0 UPnP/1.0 GabagoolOS/1.0\r\nUSN: %s\r\n\r\n", ip, DLNA_PORT, nt, nts, usn);
        sendto(dl_ssdp, msg, (size_t)len, 0, (struct sockaddr *)&to, sizeof to);
    }
}

static void ssdp_answer(const char *req, const struct sockaddr_in *from)
{
    if (strncmp(req, "M-SEARCH", 8)) return;
    const char *st = strcasestr(req, "\r\nST:");
    if (!st) return;
    st += 5;
    while (*st == ' ') st++;
    char want[160];
    size_t l = strcspn(st, "\r\n");
    if (l >= sizeof want) return;
    memcpy(want, st, l);
    want[l] = '\0';
    char ip[16], msg[768], usn[256];
    net_local_ip(ip, sizeof ip);
    if (!ip[0]) return;
    for (unsigned i = 0; i < sizeof ssdp_types / sizeof ssdp_types[0]; i++)
    {
        const char *type = ssdp_types[i][0] ? ssdp_types[i] : dl_uuid;
        if (strcmp(want, "ssdp:all") && strcmp(want, type)) continue;
        ssdp_usn(usn, sizeof usn, ssdp_types[i]);
        int len = snprintf(msg, sizeof msg, "HTTP/1.1 200 OK\r\nCACHE-CONTROL: max-age=1800\r\nEXT:\r\n"
                           "LOCATION: http://%s:%d/desc.xml\r\nSERVER: Linux/1.0 UPnP/1.0 GabagoolOS/1.0\r\n"
                           "ST: %s\r\nUSN: %s\r\n\r\n", ip, DLNA_PORT, type, usn);
        sendto(dl_ssdp, msg, (size_t)len, 0, (const struct sockaddr *)from, sizeof *from);
    }
}

static void *dl_server(void *unused)
{
    (void)unused;
    uint32_t next_notify = 0;
    while (dl_run)
    {
        if ((int32_t)(net_ms() - next_notify) >= 0)
        {
            ssdp_notify("ssdp:alive");
            next_notify = net_ms() + 30000;
        }
        fd_set rd;
        FD_ZERO(&rd);
        FD_SET(dl_http, &rd);
        FD_SET(dl_ssdp, &rd);
        struct timeval tv = { 1, 0 };
        int top = dl_http > dl_ssdp ? dl_http : dl_ssdp;
        if (select(top + 1, &rd, NULL, NULL, &tv) <= 0) continue;
        if (FD_ISSET(dl_ssdp, &rd))
        {
            char buf[1500];
            struct sockaddr_in from;
            socklen_t fl = sizeof from;
            ssize_t r = recvfrom(dl_ssdp, buf, sizeof buf - 1, 0, (struct sockaddr *)&from, &fl);
            if (r > 0) { buf[r] = '\0'; ssdp_answer(buf, &from); }
        }
        if (FD_ISSET(dl_http, &rd))
        {
            int c = accept(dl_http, NULL, NULL);
            if (c >= 0) { http_client(c); close(c); }
        }
    }
    ssdp_notify("ssdp:byebye");
    return NULL;
}

bool sl_net_dlna_start(const char *name)
{
    if (dl_thread_up) return true;
    strncpy(dl_name, name, sizeof dl_name - 1);
    char host[64] = "gabagoolos";
    gethostname(host, sizeof host - 1);
    uint32_t h = 2166136261u;
    for (const char *p = host; *p; p++) h = (h ^ (uint8_t)*p) * 16777619u;
    snprintf(dl_uuid, sizeof dl_uuid, "uuid:5c0995d1-5100-4000-8000-%012x", h);
    int one = 1;
    dl_http = socket(AF_INET, SOCK_STREAM, 0);
    dl_ssdp = socket(AF_INET, SOCK_DGRAM, 0);
    if (dl_http < 0 || dl_ssdp < 0) goto fail;
    setsockopt(dl_http, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    setsockopt(dl_ssdp, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
#ifdef SO_REUSEPORT
    setsockopt(dl_ssdp, SOL_SOCKET, SO_REUSEPORT, &one, sizeof one);
#endif
    struct sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_ANY);
    a.sin_port = htons(DLNA_PORT);
    if (bind(dl_http, (struct sockaddr *)&a, sizeof a) || listen(dl_http, 4)) goto fail;
    a.sin_port = htons(1900);
    if (bind(dl_ssdp, (struct sockaddr *)&a, sizeof a)) goto fail;
    struct ip_mreq m;
    m.imr_multiaddr.s_addr = inet_addr("239.255.255.250");
    m.imr_interface.s_addr = htonl(INADDR_ANY);
    setsockopt(dl_ssdp, IPPROTO_IP, IP_ADD_MEMBERSHIP, &m, sizeof m);
    dl_run = true;
    dl_thread_up = pthread_create(&dl_thread, NULL, dl_server, NULL) == 0;
    if (dl_thread_up) return true;
fail:
    dl_run = false;
    if (dl_http >= 0) close(dl_http);
    if (dl_ssdp >= 0) close(dl_ssdp);
    dl_http = dl_ssdp = -1;
    return false;
}

void sl_net_dlna_stop(void)
{
    if (!dl_thread_up) return;
    dl_run = false;
    dl_gen++;                              /* abandons a download */
    pthread_join(dl_thread, NULL);
    dl_thread_up = false;
    close(dl_http);
    close(dl_ssdp);
    dl_http = dl_ssdp = -1;
    dl_downloading = false;
}

/* -------------------------------------------------------- internet radio */
/* wget writes the stream to a pipe; this thread decodes it with libmad and
 * fills a ring the mixer drains (sloppy_radio.inc), as AirPlay's does. When
 * the ring is full the thread waits, wget's pipe fills and TCP slows the
 * station down: nothing is dropped and nothing piles up. */
#include "mad/global.h"
#include "mad/stream.h"
#include "mad/frame.h"
#include "mad/synth.h"
#include "faad/common.h"                 /* AAC-LC, the in-tree libfaad copy */
#include "faad/structs.h"
#include "faad/decoder.h"
#include "flac/decoder.h"
#define RD_RING (1 << 16)                 /* frames, about 1.5 s */
#define RD_IN   16384
static int16_t rd_ring[RD_RING * 2];
static volatile uint32_t rd_head, rd_tail;
static volatile int rd_state = SL_RADIO_OFF;
static volatile unsigned rd_rate, rd_kib, rd_frames, rd_junk;
static size_t bytes_in;                  /* what came, for the log */
static volatile bool rd_run;
static pthread_t rd_thread;
static bool rd_up;
#ifndef NET_DEMO
static pid_t rd_pid;                     /* the stream's wget, reaped at stop */
#endif
static volatile int rd_fd = -1;
static char rd_url[512];                 /* plain HTTP: connected on the radio's own thread */
static struct mad_stream rd_stream;
static struct mad_frame rd_frame;
static struct mad_synth rd_synth;
static mad_fixed_t rd_sb[2][36][32], rd_sb_prev[2][36][32], rd_overlap[2][32][18];
static unsigned char rd_main[MAD_BUFFER_MDLEN];
static unsigned char rd_in[RD_IN + MAD_BUFFER_GUARD];
static int16_t rd_pcm[1152 * 2];
#define RD_ERR "/tmp/sloppy-radio.txt"

/* the stream's bytes: wget on the player; on the test build, a file */
static int rd_open(const char *url)
{
#ifdef NET_DEMO
    return url[0] == '/' ? open(url, O_RDONLY) : -1;
#else
    int fd[2];
    char path[128];
    /* -S: the server's answer goes with any error to RD_ERR, for the log */
    const char *argv[] = { "wget", "-q", "-S", "-T", "20", "-U", "GabagoolOS", "-O", "-", url, NULL };
    if (!net_path(argv[0], path, sizeof path) || pipe2(fd, O_CLOEXEC)) return -1;
    rd_pid = vfork();
    if (rd_pid < 0) { close(fd[0]); close(fd[1]); rd_pid = 0; return -1; }
    if (rd_pid == 0)
    {
        setsid();
        int null = open("/dev/null", O_RDWR);
        dup2(null, 0);
        dup2(fd[1], 1);
        int err = open(RD_ERR, O_WRONLY | O_CREAT | O_TRUNC, 0644);
        dup2(err >= 0 ? err : null, 2);
        for (int i = 3; i < 256; i++) close(i);
        execv(path, (char *const *)argv);
        _exit(127);
    }
    close(fd[1]);
    return fd[0];
#endif
}
#ifndef NET_DEMO
#include <dlfcn.h>
/* HTTPS for the radio through the OpenSSL the R1's own system carries
 * (/usr/lib/libssl.so.1.1), loaded when first wanted: no build-time
 * dependency, and wget only when it is missing. Like wget's own TLS, the
 * server's certificate is not checked (the system has no CA bundle). */
static struct {
    bool tried, ok;
    void *(*method)(void);
    void *(*ctx_new)(const void *);
    void *(*ssl_new)(void *);
    int (*set_fd)(void *, int);
    long (*ctrl)(void *, int, long, void *);
    int (*connect)(void *);
    int (*read)(void *, void *, int);
    int (*write)(void *, const void *, int);
    void (*ssl_free)(void *);
    int (*get_error)(const void *, int);   /* optional: a read that timed out, not failed */
    void *ctx;
} tls;
static pthread_mutex_t tls_lock = PTHREAD_MUTEX_INITIALIZER;   /* the radio and the Audiobookshelf worker both load it */
static bool tls_load_locked(void);
static bool tls_load(void)
{
    pthread_mutex_lock(&tls_lock);
    bool ok = tls_load_locked();
    pthread_mutex_unlock(&tls_lock);
    return ok;
}
static bool tls_load_locked(void)
{
    if (tls.tried) return tls.ok;
    tls.tried = true;
    signal(SIGPIPE, SIG_IGN);            /* OpenSSL writes without MSG_NOSIGNAL; a dropped station is an error, not a crash */
    void *c = dlopen("libcrypto.so.1.1", RTLD_NOW | RTLD_GLOBAL);
    void *s = c ? dlopen("libssl.so.1.1", RTLD_NOW) : NULL;
    if (!s) { sl_log("radio: no libssl.so.1.1 (%s): HTTPS goes through wget", dlerror()); return false; }
    *(void **)&tls.method = dlsym(s, "TLS_client_method");
    *(void **)&tls.ctx_new = dlsym(s, "SSL_CTX_new");
    *(void **)&tls.ssl_new = dlsym(s, "SSL_new");
    *(void **)&tls.set_fd = dlsym(s, "SSL_set_fd");
    *(void **)&tls.ctrl = dlsym(s, "SSL_ctrl");
    *(void **)&tls.connect = dlsym(s, "SSL_connect");
    *(void **)&tls.read = dlsym(s, "SSL_read");
    *(void **)&tls.write = dlsym(s, "SSL_write");
    *(void **)&tls.ssl_free = dlsym(s, "SSL_free");
    *(void **)&tls.get_error = dlsym(s, "SSL_get_error");
    tls.ok = tls.method && tls.ctx_new && tls.ssl_new && tls.set_fd && tls.ctrl && tls.connect && tls.read &&
             tls.write && tls.ssl_free && (tls.ctx = tls.ctx_new(tls.method()));
    sl_log("radio: %s", tls.ok ? "HTTPS through the system's OpenSSL" : "OpenSSL incomplete: HTTPS goes through wget");
    return tls.ok;
}
static void *rd_ssl;                     /* the stream's TLS, when it has one */
static volatile int rd_sock = -1;        /* the socket being opened, so a stop can cut it short */
static void rd_close(int s) { rd_sock = -1; close(s); }
static unsigned rd_metaint, rd_meta_left; /* ICY: audio bytes between song titles */
static ssize_t rd_recv(int fd, void *buf, size_t n)
{
    if (rd_ssl) { int r = tls.read(rd_ssl, buf, (int)n); return r > 0 ? r : -1; }
    return recv(fd, buf, n, 0);
}

/* A stream over plain HTTP, read by us: busybox wget turns away the
 * "ICY 200 OK" many stations answer with, and its errors say little. An
 * HTTP/1.0 GET, redirects followed; the socket comes back past the
 * headers. -1 on failure; -2 with *https set when it moves to HTTPS,
 * which only wget speaks. Runs on the radio thread: it may wait. */
static int rd_http(const char *url, char *https, size_t https_cap, char *why, size_t why_cap, bool raw)
{
    char at[512];
    snprintf(at, sizeof at, "%s", url);
    for (int hop = 0; hop < 5; hop++)
    {
        bool secure = !strncasecmp(at, "https://", 8);
        if (!secure && strncasecmp(at, "http://", 7)) { snprintf(why, why_cap, "not a web address"); return -1; }
        if (secure && !tls_load()) { snprintf(https, https_cap, "%s", at); return -2; }
        char host[200], port[8];
        snprintf(port, sizeof port, secure ? "443" : "80");
        const char *h = at + (secure ? 8 : 7), *slash = strchr(h, '/');
        size_t hl = slash ? (size_t)(slash - h) : strlen(h);
        if (!hl || hl >= sizeof host) { snprintf(why, why_cap, "bad address"); return -1; }
        memcpy(host, h, hl);
        host[hl] = '\0';
        char *colon = strrchr(host, ':');
        if (colon && !strchr(colon, ']')) { snprintf(port, sizeof port, "%s", colon + 1); *colon = '\0'; }
        const char *path = slash ? slash : "/";
        struct addrinfo hints = { 0 }, *ai = NULL;
        hints.ai_family = AF_UNSPEC;
        hints.ai_socktype = SOCK_STREAM;
        int gai = getaddrinfo(host, port, &hints, &ai);
        if (gai || !ai) { snprintf(why, why_cap, "%s: no such host", host); return -1; }
        int s = -1;
        for (struct addrinfo *a = ai; a && s < 0 && rd_run; a = a->ai_next)
        {
            s = socket(a->ai_family, SOCK_STREAM | SOCK_CLOEXEC, 0);
            if (s < 0) continue;
            fcntl(s, F_SETFL, O_NONBLOCK);
            int r = connect(s, a->ai_addr, a->ai_addrlen);
            struct pollfd pw = { s, POLLOUT, 0 };
            int err = 0, ready = 0;
            socklen_t el = sizeof err;
            for (int t = 0; r < 0 && errno == EINPROGRESS && t < 16 && rd_run && !ready; t++) ready = poll(&pw, 1, 500) == 1;
            if (r < 0 && (!ready || getsockopt(s, SOL_SOCKET, SO_ERROR, &err, &el) || err))
            { rd_close(s); s = -1; continue; }
            fcntl(s, F_SETFL, 0);
            rd_sock = s;
        }
        freeaddrinfo(ai);
        if (s < 0) { snprintf(why, why_cap, "%s:%s did not connect", host, port); return -1; }
        struct timeval tv = { 15, 0 };   /* a station gone quiet ends, not hangs */
        setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
        setsockopt(s, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
        if (rd_ssl) { tls.ssl_free(rd_ssl); rd_ssl = NULL; }
        if (secure)
        {
            void *ssl = tls.ssl_new(tls.ctx);
            if (ssl && tls.set_fd(ssl, s) == 1)
            {
                tls.ctrl(ssl, 55, 0, host);   /* SSL_set_tlsext_host_name: the name the server goes by */
                if (tls.connect(ssl) == 1) rd_ssl = ssl;
            }
            if (!rd_ssl)
            {
                if (ssl) tls.ssl_free(ssl);
                rd_close(s);
                snprintf(https, https_cap, "%s", at);   /* our TLS could not: wget may */
                return -2;
            }
        }
        char req[900];
        int n = snprintf(req, sizeof req, "GET %s HTTP/1.0\r\nHost: %s\r\nUser-Agent: GabagoolOS/1.0\r\n"
                         "Accept: */*\r\nIcy-MetaData: 1\r\nConnection: close\r\n\r\n", path, host);
        if (n <= 0 || n >= (int)sizeof req ||
            (rd_ssl ? tls.write(rd_ssl, req, n) : (int)send(s, req, (size_t)n, MSG_NOSIGNAL)) != n)
        {
            if (rd_ssl) { tls.ssl_free(rd_ssl); rd_ssl = NULL; }
            rd_close(s);
            snprintf(why, why_cap, "%s: request not sent", host);
            return -1;
        }
        /* the headers, a byte at a time: the body starts right after them */
        char hd[4096];
        size_t got = 0;
        while (rd_run && got + 1 < sizeof hd && rd_recv(s, hd + got, 1) == 1)
        {
            got++;
            if ((got >= 4 && !memcmp(hd + got - 4, "\r\n\r\n", 4)) || (got >= 2 && !memcmp(hd + got - 2, "\n\n", 2)))
                break;
        }
        hd[got] = '\0';
        const char *sp = strchr(hd, ' ');
        int status = sp ? atoi(sp + 1) : 0;   /* HTTP/1.x 200, or ICY 200 */
        /* a playlist where the stream should be (.pls, .m3u): the first address in it */
        bool list = false;
        for (const char *l = hd; l && *l; l = strchr(l, '\n') ? strchr(l, '\n') + 1 : NULL)
            if (!strncasecmp(l, "Content-Type:", 13))
            {
                char ct[64];
                snprintf(ct, sizeof ct, "%.*s", (int)strcspn(l + 13, "\r\n"), l + 13);
                list = strcasestr(ct, "mpegurl") || strcasestr(ct, "scpls") || strcasestr(ct, "x-pls");
                break;
            }
        /* or by the address, when the type says nothing (Radio Deejay's .m3u8 came as audio) */
        size_t pl = strcspn(path, "?");
        if (!list && pl >= 5 && (!strncasecmp(path + pl - 5, ".m3u8", 5) || !strncasecmp(path + pl - 4, ".m3u", 4) ||
                                 !strncasecmp(path + pl - 4, ".pls", 4)))
            list = true;
        rd_metaint = 0;
        for (const char *l = hd; l && *l; l = strchr(l, '\n') ? strchr(l, '\n') + 1 : NULL)
            if (!strncasecmp(l, "icy-metaint:", 12)) rd_metaint = (unsigned)atoi(l + 12);
        rd_meta_left = rd_metaint;
        if (status == 200 && (!list || raw)) return s;
        if (status == 200)
        {
            char body[4096];
            size_t bn = 0;
            ssize_t r;
            while (bn + 1 < sizeof body && (r = rd_recv(s, body + bn, sizeof body - 1 - bn)) > 0) bn += (size_t)r;
            body[bn] = '\0';
            if (rd_ssl) { tls.ssl_free(rd_ssl); rd_ssl = NULL; }
            rd_close(s);
            if (strstr(body, "#EXT-X-")) { snprintf(https, https_cap, "%s", at); return -3; }   /* HLS: its own reader */
            const char *u = strstr(body, "http://"), *u2 = strstr(body, "https://");
            if (!u || (u2 && u2 < u)) u = u2;
            if (!u) { snprintf(why, why_cap, "%s sent an empty playlist", host); return -1; }
            snprintf(at, sizeof at, "%.*s", (int)strcspn(u, " \t\r\n\""), u);
            continue;
        }
        if (rd_ssl) { tls.ssl_free(rd_ssl); rd_ssl = NULL; }
        rd_close(s);
        const char *loc = NULL;
        for (const char *l = hd; l && *l; l = strchr(l, '\n') ? strchr(l, '\n') + 1 : NULL)
            if (!strncasecmp(l, "Location:", 9)) { loc = l + 9; break; }
        if (status >= 300 && status < 400 && loc)
        {
            while (*loc == ' ') loc++;
            size_t ll = strcspn(loc, "\r\n");
            char next[512];
            const char *dflt = secure ? "443" : "80";
            if (*loc == '/') snprintf(next, sizeof next, "%s://%s%s%s%.*s", secure ? "https" : "http", host,
                                      strcmp(port, dflt) ? ":" : "", strcmp(port, dflt) ? port : "", (int)ll, loc);
            else snprintf(next, sizeof next, "%.*s", (int)ll, loc);
            snprintf(at, sizeof at, "%s", next);
            continue;
        }
        snprintf(why, why_cap, "%s answered %d", host, status);
        return -1;
    }
    snprintf(why, why_cap, "too many redirects");
    return -1;
}
#endif
static char rd_why[200];                 /* our own client's failure, for sl_net_radio_why */
#ifdef NET_DEMO
static volatile bool rd_hls;
static ssize_t rd_read_audio(int fd, unsigned char *buf, size_t n) { return read(fd, buf, n); }
#endif
/* the song on air, from the station's in-band titles */
static pthread_mutex_t rd_title_lock = PTHREAD_MUTEX_INITIALIZER;
static char rd_title[128];
void sl_net_radio_title(char *out, size_t cap)
{
    pthread_mutex_lock(&rd_title_lock);
    snprintf(out, cap, "%s", rd_title);
    pthread_mutex_unlock(&rd_title_lock);
}
#ifndef NET_DEMO
/* "StreamTitle='Artist - Song';": the song, without its quotes */
static void rd_meta(const char *m)
{
    const char *t = strstr(m, "StreamTitle='");
    if (!t) return;
    t += 13;
    const char *e = strstr(t, "';");
    size_t n = e ? (size_t)(e - t) : strlen(t);
    pthread_mutex_lock(&rd_title_lock);
    snprintf(rd_title, sizeof rd_title, "%.*s", (int)n, t);
    pthread_mutex_unlock(&rd_title_lock);
}
/* The stream's audio bytes, its titles taken out on the way past */
static volatile bool rd_hls;              /* the stream comes from the HLS reader's socket */
static ssize_t rd_read_audio(int fd, unsigned char *buf, size_t n)
{
    if (rd_hls) return read(fd, buf, n);
    if (!rd_metaint) return rd_ssl ? rd_recv(fd, buf, n) : read(fd, buf, n);
    if (!rd_meta_left)
    {
        unsigned char len;
        if (rd_recv(fd, &len, 1) != 1) return -1;
        char m[16 * 255 + 1];
        size_t want = (size_t)len * 16, got = 0;
        while (got < want) { ssize_t r = rd_recv(fd, m + got, want - got); if (r <= 0) return -1; got += (size_t)r; }
        m[got] = '\0';
        if (got) rd_meta(m);
        rd_meta_left = rd_metaint;
    }
    ssize_t r = rd_recv(fd, buf, n < rd_meta_left ? n : rd_meta_left);
    if (r > 0) rd_meta_left -= (unsigned)r;
    return r;
}
#endif
static inline int16_t rd_sample(mad_fixed_t v)
{
    v += 1L << (MAD_F_FRACBITS - 16);     /* round */
    if (v >= MAD_F_ONE) v = MAD_F_ONE - 1;
    else if (v < -MAD_F_ONE) v = -MAD_F_ONE;
    return (int16_t)(v >> (MAD_F_FRACBITS + 1 - 16));
}
static void rd_push(unsigned n)
{
    for (unsigned k = 0; k < n && rd_run; )
    {
        uint32_t room = RD_RING - (rd_head - rd_tail);
        if (!room) { net_sleep_ms(10); continue; }
        uint32_t take = n - k < room ? n - k : room;
        for (uint32_t i = 0; i < take; i++)
        {
            uint32_t at = (rd_head + i) & (RD_RING - 1);
            rd_ring[at * 2] = rd_pcm[(k + i) * 2];
            rd_ring[at * 2 + 1] = rd_pcm[(k + i) * 2 + 1];
        }
        __sync_synchronize();
        rd_head += take;
        k += take;
    }
}
/* An AAC stream (ADTS frames), through libfaad: the first bytes are
 * already in rd_in. The decoder's samples carry 28 fraction bits, as
 * libmad's do; HE-AAC plays its core only, at its lower rate. */
static void rd_aac(size_t have)
{
    NeAACDecHandle h = NeAACDecOpen();
    if (!h) { snprintf(rd_why, sizeof rd_why, "no memory for the AAC decoder"); rd_state = SL_RADIO_FAILED; return; }
    NeAACDecConfigurationPtr conf = NeAACDecGetCurrentConfiguration(h);
    conf->outputFormat = FAAD_FMT_24BIT; /* not used: the samples are read as they are */
    NeAACDecSetConfiguration(h, conf);
    unsigned frames = 0, bad = 0;
    bool inited = false;
    while (rd_run)
    {
        /* a frame's worth in hand before each decode (ADTS frames are under 2 KB) */
        while (have < 2048 - 12 && rd_run)
        {
            ssize_t r = rd_read_audio(rd_fd, rd_in + have, RD_IN - have);
            if (r <= 0) { rd_state = frames ? SL_RADIO_ENDED : SL_RADIO_FAILED; goto out; }
            have += (size_t)r;
            rd_kib = (unsigned)((bytes_in += (size_t)r) >> 10);
        }
        if (!inited)
        {
            uint32_t sr = 0;
            uint8_t ch = 0;
            int32_t skip = NeAACDecInit(h, rd_in, (uint32_t)(have < 2048 - 12 ? have : 2048 - 12), &sr, &ch);
            if (skip < 0) { snprintf(rd_why, sizeof rd_why, "AAC the decoder could not start on"); rd_state = SL_RADIO_FAILED; goto out; }
            memmove(rd_in, rd_in + skip, have - (size_t)skip);
            have -= (size_t)skip;
            inited = true;
            continue;
        }
        NeAACDecFrameInfo fi;
        memset(&fi, 0, sizeof fi);
        void *got = NeAACDecDecode(h, &fi, rd_in, (uint32_t)(have < 2048 - 12 ? have : 2048 - 12));
        (void)got;
        size_t used = fi.bytesconsumed;
        if (fi.error || !used)
        {
            rd_junk++;
            if (++bad > 512) { snprintf(rd_why, sizeof rd_why, "AAC %s", NeAACDecGetErrorMessage(fi.error)); rd_state = SL_RADIO_FAILED; goto out; }
            used = 1;                     /* past a bad byte, to the next sync */
        }
        else if (fi.samples && fi.channels)
        {
            bad = 0;
            unsigned n = fi.samples / fi.channels;
            if (n > 1152) n = 1152;
            rd_rate = fi.samplerate;
            const real_t *l = h->time_out[0], *rr = fi.channels > 1 ? h->time_out[1] : h->time_out[0];
            for (unsigned i = 0; i < n; i++)
            {
                int32_t a = l[i] >> 13, b = rr[i] >> 13;
                rd_pcm[i * 2] = (int16_t)(a > 32767 ? 32767 : a < -32768 ? -32768 : a);
                rd_pcm[i * 2 + 1] = (int16_t)(b > 32767 ? 32767 : b < -32768 ? -32768 : b);
            }
            rd_push(n);
            rd_frames = ++frames;
            if (frames == 8) rd_state = SL_RADIO_PLAYING;
        }
        if (used > have) used = have;
        memmove(rd_in, rd_in + used, have - used);
        have -= used;
    }
out:
    (void)h;                              /* the library's one static decoder: nothing to free */
}
/* ------------------------------------------------------------ HLS
 * A live stream cut into segments a playlist names (Apple's HTTP Live
 * Streaming, what many public broadcasters send): a thread of its own
 * fetches the playlist again as it grows, takes each new segment, and
 * writes the audio in it (AAC or MP3, out of MPEG-TS, or packed with an
 * ID3 tag in front) into a socket the radio thread reads like any stream.
 * A master playlist's variant nearest 160 kb/s with AAC is chosen.
 * Encrypted streams and fragmented MP4 segments are said by name. */
#define RD_HLS_CAP (512 * 1024)           /* a segment, at most: 10 s at 320 kb/s and room over */
#define RD_HLS_SEGS 64
static pthread_t rd_hls_thread;
static bool rd_hls_up;
static volatile int rd_hls_tx = -1;
static char rd_hls_url[512];
struct rd_seg { unsigned seq; char uri[400]; };
struct rd_list { unsigned target, first; int n; bool end, master, encrypted, fmp4; struct rd_seg seg[RD_HLS_SEGS]; char best[400]; };

/* uri as an address of its own, from the playlist's */
static void rd_resolve(char *out, size_t cap, const char *base, const char *uri)
{
    if (strstr(uri, "://") || !base[0]) { snprintf(out, cap, "%s", uri); return; }
    if (uri[0] == '/')
    {
        const char *h = strstr(base, "://");
        const char *root = h ? strchr(h + 3, '/') : NULL;
        if (h && root) snprintf(out, cap, "%.*s%s", (int)(root - base), base, uri);
        else snprintf(out, cap, "%s", uri);
        return;
    }
    size_t q = strcspn(base, "?");
    const char *slash = NULL;
    for (const char *c = base; c < base + q; c++) if (*c == '/') slash = c;
    snprintf(out, cap, "%.*s%s", slash ? (int)(slash - base + 1) : 0, base, uri);
}
static void rd_list_parse(char *text, struct rd_list *l)
{
    memset(l, 0, sizeof *l);
    l->target = 6;
    unsigned k = 0;
    long best = -1, best_bw = 0;
    bool next_variant = false, next_seg = false;
    long bw = 0;
    bool aac_ok = true;
    for (char *line = text, *nl; line && *line; line = nl)
    {
        nl = strchr(line, '\n');
        if (nl) *nl++ = '\0';
        size_t len = strlen(line);
        while (len && (line[len - 1] == '\r' || line[len - 1] == ' ')) line[--len] = '\0';
        if (!len) continue;
        if (!strncmp(line, "#EXT-X-TARGETDURATION:", 22)) l->target = (unsigned)atoi(line + 22);
        else if (!strncmp(line, "#EXT-X-MEDIA-SEQUENCE:", 22)) l->first = (unsigned)strtoul(line + 22, NULL, 10);
        else if (!strncmp(line, "#EXT-X-ENDLIST", 14)) l->end = true;
        else if (!strncmp(line, "#EXT-X-KEY:", 11) && !strstr(line, "METHOD=NONE")) l->encrypted = true;
        else if (!strncmp(line, "#EXT-X-MAP:", 11)) l->fmp4 = true;
        else if (!strncmp(line, "#EXT-X-STREAM-INF:", 18))
        {
            const char *b = strstr(line, "BANDWIDTH=");
            bw = b ? atol(b + 10) : 0;
            const char *c = strstr(line, "CODECS=");
            aac_ok = !c || strcasestr(c, "mp4a") || strcasestr(c, "mp3");
            next_variant = true;
            l->master = true;
        }
        else if (!strncmp(line, "#EXTINF:", 8)) next_seg = true;
        else if (line[0] == '#') continue;
        else if (next_variant)
        {
            next_variant = false;
            long d = bw > 160000 ? bw - 160000 : 160000 - bw;
            if (aac_ok && (best < 0 || d < best)) { best = d; best_bw = bw; snprintf(l->best, sizeof l->best, "%s", line); }
        }
        else if (next_seg || !l->master)
        {
            next_seg = false;
            if (l->n < RD_HLS_SEGS) { l->seg[l->n].seq = l->first + k; snprintf(l->seg[l->n].uri, sizeof l->seg[l->n].uri, "%s", line); l->n++; }
            else { memmove(l->seg, l->seg + 1, sizeof l->seg[0] * (RD_HLS_SEGS - 1)); l->seg[RD_HLS_SEGS - 1].seq = l->first + k;
                   snprintf(l->seg[RD_HLS_SEGS - 1].uri, sizeof l->seg[0].uri, "%s", line); }
            k++;
        }
    }
    (void)best_bw;
}
/* the whole of an address into buf: its length, -1 when it did not come */
static ssize_t rd_get_all(const char *url, unsigned char *buf, size_t cap)
{
#ifdef NET_DEMO
    int fd = open(url, O_RDONLY);
    bool tls_on = false, wget = false;
#else
    char https[512], why[200];
    bool wget = false;
    int fd = rd_http(url, https, sizeof https, why, sizeof why, true);
    if (fd == -2) { fd = rd_open(https); wget = true; }
    bool tls_on = !wget && rd_ssl;
#endif
    if (fd < 0) return -1;
    size_t n = 0;
    ssize_t r = 0;
    while (n < cap && rd_run)
    {
#ifndef NET_DEMO
        r = tls_on ? rd_recv(fd, buf + n, cap - n) : read(fd, buf + n, cap - n);
#else
        (void)tls_on;
        r = read(fd, buf + n, cap - n);
#endif
        if (r <= 0) break;
        n += (size_t)r;
    }
#ifndef NET_DEMO
    if (rd_ssl) { tls.ssl_free(rd_ssl); rd_ssl = NULL; }
    if (wget) { close(fd); net_reap(&rd_pid); }
    else rd_close(fd);
#else
    (void)wget;
    close(fd);
#endif
    return rd_run ? (ssize_t)n : -1;
}
/* MPEG-TS: the audio stream's bytes, its packets' payloads joined */
struct rd_ts { int pmt, audio; };
static size_t rd_ts_audio(struct rd_ts *t, const unsigned char *in, size_t n, unsigned char *out)
{
    size_t o = 0;
    for (size_t i = 0; i + 188 <= n; )
    {
        const unsigned char *p = in + i;
        if (p[0] != 0x47) { i++; continue; }   /* back in step */
        i += 188;
        int pid = ((p[1] & 0x1f) << 8) | p[2], afc = (p[3] >> 4) & 3, off = 4;
        bool start = p[1] & 0x40;
        if (afc & 2) off += 1 + p[4];
        if (!(afc & 1) || off >= 188) continue;
        const unsigned char *pl = p + off;
        int len = 188 - off;
        if (pid == 0 && start && len > 1 + pl[0] + 12)
        {
            const unsigned char *tb = pl + 1 + pl[0];
            int sl = ((tb[1] & 0x0f) << 8) | tb[2];
            for (int k = 8; k + 4 <= 3 + sl - 4 && 1 + pl[0] + k + 4 <= len; k += 4)
                if ((tb[k] << 8 | tb[k + 1]) != 0) { t->pmt = ((tb[k + 2] & 0x1f) << 8) | tb[k + 3]; break; }
        }
        else if (pid == t->pmt && start && len > 1 + pl[0] + 12)
        {
            const unsigned char *tb = pl + 1 + pl[0];
            int sl = ((tb[1] & 0x0f) << 8) | tb[2], pi = ((tb[10] & 0x0f) << 8) | tb[11];
            const unsigned char *es = tb + 12 + pi, *end = tb + 3 + sl - 4;
            if (end > p + 188) end = p + 188;
            while (es + 5 <= end && t->audio < 0)
            {
                int type = es[0], epid = ((es[1] & 0x1f) << 8) | es[2], el = ((es[3] & 0x0f) << 8) | es[4];
                if (type == 0x0f || type == 0x03 || type == 0x04) t->audio = epid;   /* AAC (ADTS), MPEG audio */
                es += 5 + el;
            }
        }
        else if (pid == t->audio)
        {
            if (start)
            {
                if (len < 9 || pl[0] || pl[1] || pl[2] != 1) continue;
                int h = 9 + pl[8];
                if (h >= len) continue;
                pl += h;
                len -= h;
            }
            memmove(out + o, pl, (size_t)len);   /* out may be in itself: never ahead of what it reads */
            o += (size_t)len;
        }
    }
    return o;
}
/* all of len into the radio thread's socket; false when it is gone */
static bool rd_hls_send(const unsigned char *b, size_t len)
{
    while (len && rd_run)
    {
        ssize_t w = send(rd_hls_tx, b, len, MSG_NOSIGNAL);
        if (w < 0 && (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR)) continue;
        if (w <= 0) return false;
        b += w;
        len -= (size_t)w;
    }
    return rd_run;
}
static void rd_hls_fail(const char *why)
{
    snprintf(rd_why, sizeof rd_why, "%s", why);
}
static void *rd_hls_loop(void *unused)
{
    (void)unused;
    unsigned char *buf = malloc(RD_HLS_CAP);
    static struct rd_list list;
    char url[512];
    snprintf(url, sizeof url, "%s", rd_hls_url);
    unsigned next = 0;
    bool started = false;
    int misses = 0;
    while (buf && rd_run)
    {
        ssize_t n = rd_get_all(url, buf, RD_HLS_CAP - 1);
        if (n <= 0)
        {
            if (++misses >= 3) { if (!started) rd_hls_fail("HLS playlist did not come"); break; }
            for (int i = 0; i < 20 && rd_run; i++) net_sleep_ms(100);
            continue;
        }
        misses = 0;
        buf[n] = '\0';
        if (!strstr((char *)buf, "#EXTM3U")) { rd_hls_fail("HLS playlist that is not one"); break; }
        rd_list_parse((char *)buf, &list);
        if (list.master)
        {
            if (!list.best[0]) { rd_hls_fail("HLS stream without AAC or MP3 audio"); break; }
            char variant[512];
            rd_resolve(variant, sizeof variant, url, list.best);
            snprintf(url, sizeof url, "%s", variant);
            continue;
        }
        if (list.encrypted) { rd_hls_fail("encrypted HLS stream, which the radio cannot play"); break; }
        if (list.fmp4) { rd_hls_fail("HLS stream in MP4 segments, which the radio does not play yet"); break; }
        if (!list.n) { rd_hls_fail("HLS playlist with no segments"); break; }
        if (!started)
        {
            /* live: a few segments from the end, as players start; on demand: the start */
            next = list.end || list.n <= 3 ? list.seg[0].seq : list.seg[list.n - 3].seq;
            started = true;
        }
        bool any = false;
        for (int i = 0; i < list.n && rd_run; i++)
        {
            if (list.seg[i].seq < next) continue;
            char seg[512];
            rd_resolve(seg, sizeof seg, url, list.seg[i].uri);
            ssize_t m = rd_get_all(seg, buf, RD_HLS_CAP);
            next = list.seg[i].seq + 1;
            if (m <= 0) continue;            /* one missing: on to the next */
            any = true;
            size_t a;
            if (buf[0] == 0x47)
            {
                struct rd_ts t = { -1, -1 };
                a = rd_ts_audio(&t, buf, (size_t)m, buf);   /* in place */
                if (!rd_hls_send(buf, a)) goto out;
            }
            else
            {
                size_t skip = 0;           /* packed audio: an ID3 tag with the time first */
                if (m > 10 && !memcmp(buf, "ID3", 3))
                    skip = 10 + ((size_t)(buf[6] & 0x7f) << 21 | (size_t)(buf[7] & 0x7f) << 14 | (size_t)(buf[8] & 0x7f) << 7 | (buf[9] & 0x7f));
                if (skip < (size_t)m && !rd_hls_send(buf + skip, (size_t)m - skip)) goto out;
            }
        }
        if (list.end && next > list.seg[list.n - 1].seq) break;   /* all of it */
        /* live: look again in half a segment's time */
        unsigned wait = (any ? list.target / 2 : list.target) * 1000u;
        if (wait < 1000) wait = 1000;
        for (unsigned w = 0; w < wait && rd_run; w += 100) net_sleep_ms(100);
    }
out:
    free(buf);
    shutdown(rd_hls_tx, SHUT_RDWR);       /* the radio thread reads the end */
    return NULL;
}
/* the reader started: the socket the radio thread reads, -1 when it could not */
static int rd_hls_start(const char *url)
{
    int sv[2];
    if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv)) return -1;
    snprintf(rd_hls_url, sizeof rd_hls_url, "%s", url);
    rd_hls_tx = sv[1];
    struct timeval tv = { 0, 500000 };
    setsockopt(sv[1], SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);   /* a stop is noticed while the radio is full */
    rd_hls = true;
    pthread_attr_t a;
    pthread_attr_init(&a);
    pthread_attr_setstacksize(&a, 128 * 1024);
    rd_hls_up = pthread_create(&rd_hls_thread, &a, rd_hls_loop, NULL) == 0;
    pthread_attr_destroy(&a);
    if (!rd_hls_up) { close(sv[0]); close(sv[1]); rd_hls_tx = -1; rd_hls = false; return -1; }
    return sv[0];
}
static void rd_hls_stop(void)
{
    if (rd_hls_tx >= 0) shutdown(rd_hls_tx, SHUT_RDWR);
    if (rd_hls_up) pthread_join(rd_hls_thread, NULL);
    rd_hls_up = false;
    if (rd_hls_tx >= 0) close(rd_hls_tx);
    rd_hls_tx = -1;
    rd_hls = false;
}

/* ------------------------------------------------------------ FLAC and Ogg
 * FLAC streams, native ("fLaC" and its metadata, then frames) or in Ogg,
 * through the copy of Rockbox's FLAC decoder in flac/; Vorbis in Ogg
 * through the copy of Tremor in tremor/ when it is built in; Opus in Ogg
 * through the copy of Rockbox's Opus decoder in opus/. The samples
 * come as 29-bit integers; 16 are kept. Mono plays on both sides; a
 * stream of more than two channels is said by name. */
#define RD_BIG (96 * 1024)                /* a frame or packet in hand, and room to look past it */
static FLACContext rd_fc;
static int32_t *rd_flac_dec;              /* two channels of MAX_BLOCKSIZE */
static void rd_noyield(void) {}
static void rd_out16(const int32_t *l, const int32_t *r, unsigned n, int shift, unsigned rate)
{
    rd_rate = rate;
    for (unsigned k = 0; k < n && rd_run; )
    {
        unsigned take = n - k < 1152 ? n - k : 1152;
        for (unsigned i = 0; i < take; i++)
        {
            int32_t a = l[k + i] >> shift, b = r[k + i] >> shift;
            rd_pcm[i * 2] = (int16_t)(a > 32767 ? 32767 : a < -32768 ? -32768 : a);
            rd_pcm[i * 2 + 1] = (int16_t)(b > 32767 ? 32767 : b < -32768 ? -32768 : b);
        }
        rd_push(take);
        k += take;
    }
}
/* STREAMINFO's 34 bytes: false for what the decoder cannot take */
static bool rd_flac_info(const unsigned char *b)
{
    memset(&rd_fc, 0, sizeof rd_fc);
    rd_fc.min_blocksize = b[0] << 8 | b[1];
    rd_fc.max_blocksize = b[2] << 8 | b[3];
    rd_fc.min_framesize = b[4] << 16 | b[5] << 8 | b[6];
    rd_fc.max_framesize = b[7] << 16 | b[8] << 8 | b[9];
    rd_fc.samplerate = b[10] << 12 | b[11] << 4 | (b[12] & 0xf0) >> 4;
    rd_fc.channels = ((b[12] & 0x0e) >> 1) + 1;
    rd_fc.bps = ((b[12] & 0x01) << 4 | (b[13] & 0xf0) >> 4) + 1;
    if (rd_fc.channels > 2) { snprintf(rd_why, sizeof rd_why, "FLAC with %d channels, which the radio does not play", rd_fc.channels); return false; }
    if (rd_fc.max_blocksize > MAX_BLOCKSIZE || !rd_fc.samplerate) { snprintf(rd_why, sizeof rd_why, "FLAC the decoder cannot take"); return false; }
    if (!rd_flac_dec) rd_flac_dec = malloc(2 * MAX_BLOCKSIZE * sizeof *rd_flac_dec);
    if (!rd_flac_dec) { snprintf(rd_why, sizeof rd_why, "no memory for the FLAC decoder"); return false; }
    rd_fc.decoded[0] = rd_flac_dec;
    rd_fc.decoded[1] = rd_flac_dec + MAX_BLOCKSIZE;
    return true;
}
/* one frame from b; bytes used, 0 when it is not one */
static int rd_flac_frame(unsigned char *b, int len, unsigned *frames)
{
    if (len < MIN_FRAME_SIZE || flac_decode_frame(&rd_fc, b, len, rd_noyield) < 0) return 0;
    const int32_t *l = rd_fc.decoded[0], *r = rd_fc.channels > 1 ? rd_fc.decoded[1] : rd_fc.decoded[0];
    rd_out16(l, r, (unsigned)rd_fc.blocksize, FLAC_OUTPUT_DEPTH - 16, (unsigned)rd_fc.samplerate);
    rd_frames = ++*frames;
    if (*frames == 4) rd_state = SL_RADIO_PLAYING;
    return rd_fc.framesize > 0 ? rd_fc.framesize : (int)((rd_fc.gb.index + 7) >> 3);
}
/* more of the stream into buf after have bytes; false at its end */
static bool rd_more(unsigned char *buf, size_t *have, size_t cap)
{
    if (*have >= cap) return true;
    ssize_t r = rd_read_audio(rd_fd, buf + *have, cap - *have);
    if (r <= 0) return false;
    *have += (size_t)r;
    rd_kib = (unsigned)((bytes_in += (size_t)r) >> 10);
    return true;
}
/* native FLAC: the first bytes are in rd_in */
static void rd_flac(size_t have0)
{
    unsigned char *buf = malloc(RD_BIG);
    if (!buf) { snprintf(rd_why, sizeof rd_why, "no memory for FLAC"); rd_state = SL_RADIO_FAILED; return; }
    size_t have = have0;
    memcpy(buf, rd_in, have);
    unsigned frames = 0, bad = 0;
    bool info = false;
    /* the metadata: STREAMINFO is the first block */
    size_t at = 4;
    for (bool last = false; !last && rd_run; )
    {
        while (have < at + 4 && rd_run) if (!rd_more(buf, &have, RD_BIG)) goto end;
        last = buf[at] & 0x80;
        size_t len = (size_t)buf[at + 1] << 16 | (size_t)buf[at + 2] << 8 | buf[at + 3];
        if ((buf[at] & 0x7f) == 0)
        {
            while (have < at + 4 + 34 && rd_run) if (!rd_more(buf, &have, RD_BIG)) goto end;
            if (!rd_flac_info(buf + at + 4)) goto end;
            info = true;
        }
        at += 4 + len;
        /* a picture or tags bigger than the buffer go by, a piece at a time */
        while (at > have && rd_run)
        {
            at -= have;
            have = 0;
            if (!rd_more(buf, &have, RD_BIG)) goto end;
        }
    }
    if (!info) { snprintf(rd_why, sizeof rd_why, "FLAC without its stream info"); goto end; }
    memmove(buf, buf + at, have - at);
    have -= at;
    while (rd_run)
    {
        while (have < RD_BIG / 2 && rd_run) if (!rd_more(buf, &have, RD_BIG)) break;
        if (!have) break;
        int used = buf[0] == 0xff && (buf[1] & 0xfe) == 0xf8 ? rd_flac_frame(buf, (int)have, &frames) : 0;
        if (!used)
        {
            /* not a frame here: on to the next sync */
            rd_junk++;
            if (++bad > 4096) { snprintf(rd_why, sizeof rd_why, "FLAC the decoder could not read"); break; }
            size_t k = 1;
            while (k + 1 < have && !(buf[k] == 0xff && (buf[k + 1] & 0xfe) == 0xf8)) k++;
            used = (int)k;
            if (have < 2) { if (!rd_more(buf, &have, RD_BIG)) break; continue; }
        }
        else bad = 0;
        if ((size_t)used > have) used = (int)have;
        memmove(buf, buf + used, have - (size_t)used);
        have -= (size_t)used;
        if (have < 64 && !rd_more(buf, &have, RD_BIG) && have < MIN_FRAME_SIZE) break;
    }
end:
    rd_state = frames ? SL_RADIO_ENDED : SL_RADIO_FAILED;
    free(buf);
}

/* Ogg: pages, their packets, and what the first packet says it is */
#define RD_TREMOR 1                       /* tremor/ is built in */
#include "tremor/ivorbiscodec.h"
#include "opus/opus.h"
/* Opus as the decoder gives it (16-bit, 48 kHz, interleaved) into the ring,
 * the pre-skip of a stream's start left out */
static void rd_opus_out(const int16_t *pcm, int n, int ch, int *skip)
{
    rd_rate = 48000;
    int from = *skip < n ? *skip : n;
    *skip -= from;
    for (int k = from; k < n && rd_run; )
    {
        int take = n - k < 1152 ? n - k : 1152;
        for (int i = 0; i < take; i++)
        {
            rd_pcm[i * 2] = pcm[(k + i) * ch];
            rd_pcm[i * 2 + 1] = pcm[(k + i) * ch + ch - 1];
        }
        rd_push((unsigned)take);
        k += take;
    }
}
static void rd_ogg(size_t have0)
{
    unsigned char *buf = malloc(RD_BIG), *pk = malloc(RD_BIG);
    if (!buf || !pk) { free(buf); free(pk); snprintf(rd_why, sizeof rd_why, "no memory for Ogg"); rd_state = SL_RADIO_FAILED; return; }
    size_t have = have0, pkn = 0;
    memcpy(buf, rd_in, have);
    unsigned frames = 0;
    int kind = 0;                         /* 1 FLAC, 2 Vorbis, 3 Opus */
    OpusDecoder *od = NULL;
    int16_t *opcm = NULL;
    int och = 0, oskip = 0;
    long packets = 0;
    uint32_t serial = 0;
#ifdef RD_TREMOR
    vorbis_info vi;
    vorbis_dsp_state vd;
    vorbis_block vb;
    bool vinit = false, vdsp = false;
    vorbis_info_init(&vi);
#endif
    while (rd_run)
    {
        while (have < 27 && rd_run) if (!rd_more(buf, &have, RD_BIG)) goto end;
        if (memcmp(buf, "OggS", 4))
        {
            /* out of step: the next page */
            size_t k = 1;
            while (k + 4 <= have && memcmp(buf + k, "OggS", 4)) k++;
            rd_junk++;
            memmove(buf, buf + k, have - k);
            have -= k;
            continue;
        }
        unsigned nseg = buf[26];
        while (have < 27 + nseg && rd_run) if (!rd_more(buf, &have, RD_BIG)) goto end;
        size_t body = 0;
        for (unsigned i = 0; i < nseg; i++) body += buf[27 + i];
        size_t page = 27 + nseg + body;
        while (have < page && rd_run) if (!rd_more(buf, &have, RD_BIG)) goto end;
        uint32_t ser = (uint32_t)buf[14] | (uint32_t)buf[15] << 8 | (uint32_t)buf[16] << 16 | (uint32_t)buf[17] << 24;
        bool bos = buf[5] & 2;
        if (bos && kind)
        {
            /* a new stream after this one (a station chaining tracks): begin again */
#ifdef RD_TREMOR
            if (vdsp) { vorbis_block_clear(&vb); vorbis_dsp_clear(&vd); vdsp = false; }
            vorbis_info_clear(&vi); vorbis_info_init(&vi);
            vinit = false;
#endif
            free(od); od = NULL;
            kind = 0; packets = 0; pkn = 0;
        }
        if (!kind && !bos && !packets) { memmove(buf, buf + page, have - page); have -= page; continue; }   /* joined mid-stream: wait for a beginning */
        if (kind && ser != serial) { memmove(buf, buf + page, have - page); have -= page; continue; }   /* another stream in it */
        if (!(buf[5] & 1)) pkn = 0;           /* not a continued packet: a fresh one */
        const unsigned char *d = buf + 27 + nseg;
        for (unsigned i = 0; i < nseg && rd_run; i++)
        {
            unsigned lace = buf[27 + i];
            if (pkn + lace <= RD_BIG) memcpy(pk + pkn, d, lace);
            pkn += lace;
            d += lace;
            if (lace == 255) continue;        /* the packet goes on */
            size_t n = pkn > RD_BIG ? 0 : pkn;
            pkn = 0;
            if (!n) continue;
            if (!packets++)
            {
                serial = ser;
                if (n >= 13 + 38 && pk[0] == 0x7f && !memcmp(pk + 1, "FLAC", 4) && !memcmp(pk + 9, "fLaC", 4))
                {
                    if (!rd_flac_info(pk + 13 + 4)) goto end;
                    kind = 1;
                }
                else if (n >= 7 && pk[0] == 1 && !memcmp(pk + 1, "vorbis", 6))
                {
#ifdef RD_TREMOR
                    ogg_packet op = { pk, (long)n, 1, 0, 0, 0 };
                    if (vorbis_synthesis_headerin(&vi, &op)) { snprintf(rd_why, sizeof rd_why, "Vorbis the decoder could not start on"); goto end; }
                    if (vi.channels > 2) { snprintf(rd_why, sizeof rd_why, "Vorbis with %d channels, which the radio does not play", vi.channels); goto end; }
                    kind = 2;
#else
                    snprintf(rd_why, sizeof rd_why, "Ogg Vorbis stream, which the radio does not play yet");
                    goto end;
#endif
                }
                else if (n >= 19 && !memcmp(pk, "OpusHead", 8))
                {
                    /* OpusHead: version, channels, pre-skip, rate, gain, mapping */
                    och = pk[9];
                    if ((pk[8] & 0xf0) || !och) { snprintf(rd_why, sizeof rd_why, "Ogg Opus the decoder cannot take"); goto end; }
                    if (och > 2 || (pk[18] && (n < 21 || pk[19] != 1)))
                    {
                        snprintf(rd_why, sizeof rd_why, "Ogg Opus with %d channels, which the radio does not play", och);
                        goto end;
                    }
                    oskip = pk[10] | pk[11] << 8;
                    int gain = (int16_t)(pk[16] | pk[17] << 8);
                    if (!opcm) opcm = malloc(5760 * 2 * sizeof *opcm);   /* 120 ms, the longest packet */
                    od = opcm ? malloc((size_t)opus_decoder_get_size(och)) : NULL;
                    if (!od || opus_decoder_init_rockbox(od, 48000, och) != OPUS_OK)
                    {
                        snprintf(rd_why, sizeof rd_why, "no memory for Opus");
                        goto end;
                    }
                    if (gain) opus_decoder_ctl(od, OPUS_SET_GAIN(gain));
                    kind = 3;
                }
                else
                {
                    snprintf(rd_why, sizeof rd_why, "Ogg stream, which the radio does not play yet");
                    goto end;
                }
                continue;
            }
            if (kind == 1)
            {
                if (pk[0] == 0xff && (pk[1] & 0xfe) == 0xf8 && !rd_flac_frame(pk, (int)n, &frames)) rd_junk++;
            }
#ifdef RD_TREMOR
            else if (kind == 2)
            {
                ogg_packet op = { pk, (long)n, 0, 0, -1, packets - 1 };
                if (packets <= 3)
                {
                    if (vorbis_synthesis_headerin(&vi, &op)) { snprintf(rd_why, sizeof rd_why, "Vorbis headers the decoder could not read"); goto end; }
                    if (packets == 3)
                    {
                        if (vorbis_synthesis_init(&vd, &vi) || vorbis_block_init(&vd, &vb)) { snprintf(rd_why, sizeof rd_why, "no memory for Vorbis"); goto end; }
                        vdsp = true;
                        vinit = true;
                    }
                    continue;
                }
                if (!vinit || vorbis_synthesis(&vb, &op) || vorbis_synthesis_blockin(&vd, &vb)) { rd_junk++; continue; }
                ogg_int32_t **pcm;
                int got;
                while ((got = vorbis_synthesis_pcmout(&vd, &pcm)) > 0 && rd_run)
                {
                    rd_out16(pcm[0], pcm[vi.channels > 1 ? 1 : 0], (unsigned)got, 9, (unsigned)vi.rate);
                    vorbis_synthesis_read(&vd, got);
                }
                rd_frames = ++frames;
                if (frames == 8) rd_state = SL_RADIO_PLAYING;
            }
#endif
            else if (kind == 3)
            {
                if (packets == 2) continue;   /* OpusTags */
                int got = opus_decode_rockbox(od, pk, (opus_int32)n, opcm, 5760, 0);
                if (got <= 0) { rd_junk++; continue; }
                rd_opus_out(opcm, got, och, &oskip);
                rd_frames = ++frames;
                if (frames == 25) rd_state = SL_RADIO_PLAYING;   /* half a second of 20 ms packets */
            }
        }
        memmove(buf, buf + page, have - page);
        have -= page;
    }
end:
#ifdef RD_TREMOR
    if (vdsp) { vorbis_block_clear(&vb); vorbis_dsp_clear(&vd); }
    vorbis_info_clear(&vi);
#endif
    free(od);
    free(opcm);
    rd_state = frames ? SL_RADIO_ENDED : SL_RADIO_FAILED;
    free(buf);
    free(pk);
}

static void *rd_loop(void *unused)
{
    (void)unused;
    rd_frame.sbsample = &rd_sb;
    rd_frame.sbsample_prev = &rd_sb_prev;
    rd_frame.overlap = &rd_overlap;
    rd_stream.main_data = &rd_main;
    mad_stream_init(&rd_stream);
    mad_frame_init(&rd_frame);
    mad_synth_init(&rd_synth);
    if (rd_fd < 0 && rd_hls_url[0]) rd_fd = rd_hls_start(rd_hls_url);   /* a playlist from the start */
    if (rd_fd < 0 && rd_hls_url[0]) { rd_state = SL_RADIO_FAILED; return NULL; }
#ifndef NET_DEMO
    if (rd_fd < 0 && rd_url[0])
    {
        char https[512];
        int fd = rd_http(rd_url, https, sizeof https, rd_why, sizeof rd_why, false);
        if (fd == -3) fd = rd_hls_start(https);   /* segments, read by their own thread */
        else if (fd == -2) fd = rd_open(https);   /* moved to HTTPS: wget's */
        if (fd < 0 || !rd_run) { if (fd >= 0) close(fd); rd_state = SL_RADIO_FAILED; return NULL; }
        rd_fd = fd;
    }
#endif
    size_t keep = 0, bytes = 0;
    unsigned frames = 0, junk = 0;
    bytes_in = 0;
    while (rd_run)
    {
        if (rd_stream.next_frame && rd_stream.bufend > rd_stream.next_frame)
        {
            keep = (size_t)(rd_stream.bufend - rd_stream.next_frame);
            memmove(rd_in, rd_stream.next_frame, keep);
        }
        else keep = 0;
        ssize_t r = rd_read_audio(rd_fd, rd_in + keep, RD_IN - keep);
        if (r <= 0) { rd_state = frames ? SL_RADIO_ENDED : SL_RADIO_FAILED; break; }
        if (!bytes && r >= 4)
        {
            /* what came: AAC goes to its own decoder; what is neither is
             * said by name, not "did not answer" */
            const unsigned char *b = rd_in + keep;
            if (b[0] == 0xff && (b[1] & 0xf6) == 0xf0) { bytes_in = (size_t)r; rd_aac(keep + (size_t)r); return NULL; }
            /* a playlist after all (wget fetched it): HLS reads it itself */
            if (!rd_hls && !memcmp(b, "#EXTM3U", r >= 7 ? 7 : 4) && memmem(b, (size_t)r, "#EXT-X-", 7) && (rd_url[0] || rd_hls_url[0]))
            {
                close(rd_fd);
#ifndef NET_DEMO
                net_reap(&rd_pid);
#endif
                rd_fd = rd_hls_start(rd_hls_url[0] ? rd_hls_url : rd_url);
                if (rd_fd < 0) { rd_state = SL_RADIO_FAILED; break; }
                keep = 0;
                continue;
            }
            if (!memcmp(b, "fLaC", 4)) { bytes_in = (size_t)r; rd_flac(keep + (size_t)r); return NULL; }
            if (!memcmp(b, "OggS", 4)) { bytes_in = (size_t)r; rd_ogg(keep + (size_t)r); return NULL; }
            const char *kind = !memcmp(b, "<", 1) || !memcmp(b, "{", 1) ? "a web page" : NULL;
            if (kind) { snprintf(rd_why, sizeof rd_why, "%s stream, which the radio does not play yet", kind); rd_state = SL_RADIO_FAILED; break; }
        }
        bytes += (size_t)r;
        bytes_in = bytes;
        rd_kib = (unsigned)(bytes >> 10);
        mad_stream_buffer(&rd_stream, rd_in, keep + (size_t)r);
        while (rd_run)
        {
            if (mad_frame_decode(&rd_frame, &rd_stream))
            {
                if (rd_stream.error == MAD_ERROR_BUFLEN) break;
                rd_junk++;
                if (MAD_RECOVERABLE(rd_stream.error) && ++junk < 4096) continue;   /* in a row: a tag, a glitch */
                rd_state = SL_RADIO_FAILED;   /* not MP3, or broken past repair */
                rd_run = false;
                break;
            }
            junk = 0;
            rd_frames = frames + 1;
            mad_synth_frame(&rd_synth, &rd_frame);
            const struct mad_pcm *pcm = &rd_synth.pcm;
            rd_rate = pcm->samplerate;
            for (unsigned i = 0; i < pcm->length; i++)
            {
                rd_pcm[i * 2] = rd_sample(pcm->samples[0][i]);
                rd_pcm[i * 2 + 1] = rd_sample(pcm->samples[pcm->channels > 1 ? 1 : 0][i]);
            }
            rd_push(pcm->length);
            if (++frames == 8) rd_state = SL_RADIO_PLAYING;
        }
    }
    return NULL;
}
bool sl_net_radio_start(const char *url)
{
    sl_net_radio_stop();
    rd_url[0] = rd_hls_url[0] = '\0';
    rd_why[0] = '\0';
    pthread_mutex_lock(&rd_title_lock);
    rd_title[0] = '\0';
    pthread_mutex_unlock(&rd_title_lock);
#ifndef NET_DEMO
    rd_why[0] = '\0';
    rd_metaint = rd_meta_left = 0;           /* wget's streams carry no titles: it does not ask */
    if (!strncasecmp(url, "http://", 7) || !strncasecmp(url, "https://", 8))
    { snprintf(rd_url, sizeof rd_url, "%s", url); rd_fd = -1; }
    else
#endif
    {
        size_t ul = strcspn(url, "?");
        if (ul > 5 && !strncasecmp(url + ul - 5, ".m3u8", 5)) { snprintf(rd_hls_url, sizeof rd_hls_url, "%s", url); rd_fd = -1; }
        else
        {
            rd_fd = rd_open(url);
            if (rd_fd < 0) { rd_state = SL_RADIO_FAILED; return false; }
        }
    }
    rd_head = rd_tail = 0;
    rd_rate = rd_kib = rd_frames = rd_junk = 0;
    rd_state = SL_RADIO_CONNECTING;
    rd_run = true;
    if (pthread_create(&rd_thread, NULL, rd_loop, NULL))
    {
        rd_run = false;
        if (rd_fd >= 0) close(rd_fd);
        rd_fd = -1;
        rd_state = SL_RADIO_FAILED;
        return false;
    }
    rd_up = true;
    return true;
}
void sl_net_radio_stop(void)
{
    if (!rd_up) { rd_state = SL_RADIO_OFF; return; }
    rd_run = false;
    if (rd_hls && rd_fd >= 0) shutdown(rd_fd, SHUT_RDWR);   /* HLS: the radio thread's read returns */
    if (rd_hls_tx >= 0) shutdown(rd_hls_tx, SHUT_RDWR);
#ifndef NET_DEMO
    net_reap(&rd_pid);                    /* its pipe closes: a blocked read returns */
    if (rd_fd >= 0) shutdown(rd_fd, SHUT_RDWR);   /* our own socket: the same */
    if (rd_sock >= 0) shutdown(rd_sock, SHUT_RDWR);   /* or the one still being opened */
#endif
    pthread_join(rd_thread, NULL);
    rd_hls_stop();
#ifndef NET_DEMO
    if (rd_ssl) { tls.ssl_free(rd_ssl); rd_ssl = NULL; }
    rd_sock = -1;
    net_reap(&rd_pid);                    /* a wget the thread started after the first reap */
#endif
    if (rd_fd >= 0) close(rd_fd);
    rd_fd = -1;
    rd_up = false;
    rd_state = SL_RADIO_OFF;
}
int sl_net_radio_state(void) { return rd_state; }
unsigned sl_net_radio_rate(void) { return rd_rate; }
size_t sl_net_radio_buffered(void) { return rd_head - rd_tail; }
void sl_net_radio_why(char *out, size_t cap)
{
    char said[160] = "";
#ifndef NET_DEMO
    /* wget's last line: its error, or the last header the server sent */
    char buf[2048];
    int fd = open(RD_ERR, O_RDONLY);
    ssize_t n = fd >= 0 ? read(fd, buf, sizeof buf - 1) : -1;
    if (fd >= 0) close(fd);
    if (n > 0)
    {
        buf[n] = '\0';
        while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r' || buf[n - 1] == ' ')) buf[--n] = '\0';
        char *line = strrchr(buf, '\n');
        snprintf(said, sizeof said, "%s", line ? line + 1 : buf);
    }
#endif
    if (rd_why[0]) snprintf(said, sizeof said, "%s", rd_why);
    snprintf(out, cap, "%u KiB, %u frames, %u bad; %s", rd_kib, rd_frames, rd_junk, said[0] ? said : "wget said nothing");
}
size_t sl_net_radio_read(int16_t *dst, size_t frames)
{
    uint32_t have = rd_head - rd_tail;
    if (frames > have) frames = have;
    for (size_t k = 0; k < frames; k++)
    {
        uint32_t at = (rd_tail + (uint32_t)k) & (RD_RING - 1);
        dst[k * 2] = rd_ring[at * 2];
        dst[k * 2 + 1] = rd_ring[at * 2 + 1];
    }
    __sync_synchronize();
    rd_tail += (uint32_t)frames;
    return frames;
}

/* -------------------------------------------------------------- remote */
/* One small HTTP server: the page at / (an app a phone can keep on its
 * home screen: its manifest and icons), the cover playing now, and
 * /api/... handed one at a time to the interface thread, which owns the
 * player. A request it does not answer in three seconds gets a 503, so a
 * busy player never hangs a phone. A few connections are read at once: a
 * browser opens one ahead that may say nothing for seconds, and it must
 * not hold up the next poll. */
#include "sloppy_remote_page.h"
static int rm_sock = -1;
static volatile bool rm_run;
static pthread_t rm_thread;
static bool rm_up;
static pthread_mutex_t rm_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t rm_cond = PTHREAD_COND_INITIALIZER;
static char rm_path[64], rm_query[256];
static bool rm_pending, rm_taken, rm_done;
static unsigned rm_seq, rm_taken_seq;    /* which request an answer is for: a late one is dropped */
static char rm_body[24 * 1024];
/* what the interface tells this thread: the cover playing now, and the
 * icons' colours */
static struct { char path[512]; long off, size; int kind; unsigned key; } rm_cov;   /* under rm_lock */
static volatile uint32_t rm_ic_acc = 0x72d8cd, rm_ic_ink = 0x182735;
#define RM_CONNS 6
#define RM_REQ 2048
static struct { int fd; size_t got; uint32_t t0; bool up; uint64_t up_left; char req[RM_REQ]; } rm_conn[RM_CONNS];
/* POST /update: a GabagoolOS update file from the page, as its body. It
 * goes to the card a piece at a time between the other requests (an update
 * is tens of MB; polls must not wait for it), into sloppy_ota.c's hands. */
#define RM_UP_IDLE_MS 15000
unsigned sl_net_remote_served;           /* requests answered, for the tests */

/* when the answer being sent must be done: a phone that reads a byte at a
 * time (each send making a little progress, so SO_SNDTIMEO never fires)
 * must not keep the only server thread, nor a cover open on the card */
static uint32_t rm_send_by;
static void rm_send(int fd, const char *b, size_t n)
{
    while (n && (int32_t)(net_ms() - rm_send_by) < 0)
    {
        ssize_t w = send(fd, b, n, MSG_NOSIGNAL);   /* a phone gone away must not end the player */
        if (w <= 0) return;
        b += w;
        n -= (size_t)w;
    }
}
/* the head; len < 0: no length, the body ends when the connection does */
static const char *rm_extra = "";        /* one more header line for the next head (a pairing's cookie) */
static void rm_head(int fd, const char *status, const char *type, const char *cache, long len)
{
    rm_send_by = net_ms() + 20000;   /* every answer starts here: 20 s to send it all */
    char h[448];
    int n = len >= 0 ? snprintf(h, sizeof h, "HTTP/1.1 %s\r\nContent-Type: %s\r\nContent-Length: %ld\r\n"
                                "Cache-Control: %s\r\n%sConnection: close\r\n\r\n", status, type, len, cache, rm_extra)
                     : snprintf(h, sizeof h, "HTTP/1.1 %s\r\nContent-Type: %s\r\nCache-Control: %s\r\n%sConnection: close\r\n\r\n",
                                status, type, cache, rm_extra);
    rm_extra = "";
    rm_send(fd, h, (size_t)n);
}
static void rm_reply_c(int fd, const char *status, const char *type, const char *cache, const void *body, size_t len)
{
    rm_head(fd, status, type, cache, (long)len);
    rm_send(fd, body, len);
    sl_net_remote_served++;
}
static void rm_reply(int fd, const char *status, const char *type, const char *body, size_t len)
{
    rm_reply_c(fd, status, type, "no-store", body, len);
}
bool sl_net_query_param(const char *query, const char *key, char *out, size_t n)
{
    size_t kl = strlen(key), o = 0;
    for (const char *p = query; p && *p; p = strchr(p, '&') ? strchr(p, '&') + 1 : NULL)
    {
        if (strncmp(p, key, kl) || p[kl] != '=') continue;
        for (p += kl + 1; *p && *p != '&' && o + 1 < n; p++)
        {
            if (*p == '+') out[o++] = ' ';
            else if (*p == '%' && isxdigit((unsigned char)p[1]) && isxdigit((unsigned char)p[2]))
            {
                char hex[3] = { p[1], p[2], 0 };
                out[o++] = (char)strtol(hex, NULL, 16);
                p += 2;
            }
            else out[o++] = *p;
        }
        out[o] = '\0';
        return true;
    }
    if (n) out[0] = '\0';
    return false;
}

/* ---- the app's icon, drawn here at the size asked: the accent's disc with
 * a play mark on the night blue, all of it inside the middle 80 % that a
 * launcher's mask keeps. No picture file: a few hundred lines of pixels. */
static float rm_clamp01(float v) { return v < 0 ? 0 : v > 1 ? 1 : v; }
/* signed distance from (px, py) to the triangle v (three x, y pairs): < 0 inside */
static float rm_tri_sd(float px, float py, const float *v)
{
    float e[3][2], w[3][2], best = 1e30f, sgn = 1;
    for (int i = 0; i < 3; i++)
    {
        int j = (i + 1) % 3;
        e[i][0] = v[2 * j] - v[2 * i]; e[i][1] = v[2 * j + 1] - v[2 * i + 1];
        w[i][0] = px - v[2 * i]; w[i][1] = py - v[2 * i + 1];
    }
    float s = e[0][0] * e[2][1] - e[0][1] * e[2][0] > 0 ? 1.f : -1.f;
    for (int i = 0; i < 3; i++)
    {
        float t = rm_clamp01((w[i][0] * e[i][0] + w[i][1] * e[i][1]) / (e[i][0] * e[i][0] + e[i][1] * e[i][1]));
        float qx = w[i][0] - e[i][0] * t, qy = w[i][1] - e[i][1] * t, d = qx * qx + qy * qy;
        float side = s * (w[i][0] * e[i][1] - w[i][1] * e[i][0]);
        if (d < best) best = d;
        if (side < 0) sgn = -1;   /* outside one edge: outside */
    }
    float d = sqrtf(best);
    return sgn < 0 ? d : -d;
}
static unsigned char rm_mix(unsigned a, unsigned b, float t) { return (unsigned char)(a + (b - (float)a) * t + 0.5f); }
static size_t rm_icon(int s, unsigned char **png)
{
    unsigned char *rgb = malloc((size_t)s * s * 3);
    *png = NULL;
    if (!rgb) return 0;
    uint32_t acc = rm_ic_acc, ink = rm_ic_ink;
    unsigned ar = acc >> 16 & 255, ag = acc >> 8 & 255, ab = acc & 255;
    float c = s / 2.f, r = s * 0.30f, glow = s * 0.46f, round = s * 0.028f;
    /* the play mark: its middle a little right of the disc's, as the eye wants it */
    float tri[6] = { c - s * 0.073f, c - s * 0.125f, c - s * 0.073f, c + s * 0.125f, c + s * 0.147f, c };
    for (int y = 0; y < s; y++)
    {
        float fy = (float)y / (s - 1);
        /* the night blue, a step lighter at the top */
        unsigned br = rm_mix(0x1b, 0x0b, fy), bg = rm_mix(0x25, 0x10, fy), bb = rm_mix(0x33, 0x17, fy);
        for (int x = 0; x < s; x++)
        {
            float dx = x + 0.5f - c, dy = y + 0.5f - c, d = sqrtf(dx * dx + dy * dy);
            float R = br, G = bg, B = bb;
            /* the accent's light round the disc, faint */
            float gl = rm_clamp01(1 - (d - r) / (glow - r));
            gl = gl * gl * 0.22f;
            R += (ar - R) * gl; G += (ag - G) * gl; B += (ab - B) * gl;
            float cov = rm_clamp01(r - d + 0.5f);
            if (cov > 0)
            {
                /* the disc, lit from above */
                float lt = (dy / r) * -0.5f + 0.5f, k = lt * 0.16f;
                float dr = ar + (255 - ar) * k, dg = ag + (255 - ag) * k, db = ab + (255 - ab) * k;
                if (lt < 0.5f) { float m = (0.5f - lt) * 0.14f; dr *= 1 - m; dg *= 1 - m; db *= 1 - m; }
                float tc = rm_clamp01(0.5f - (rm_tri_sd(x + 0.5f, y + 0.5f, tri) - round));
                dr += ((ink >> 16 & 255) - dr) * tc; dg += ((ink >> 8 & 255) - dg) * tc; db += ((ink & 255) - db) * tc;
                R += (dr - R) * cov; G += (dg - G) * cov; B += (db - B) * cov;
            }
            unsigned char *o = rgb + ((size_t)y * s + x) * 3;
            o[0] = (unsigned char)(R + 0.5f); o[1] = (unsigned char)(G + 0.5f); o[2] = (unsigned char)(B + 0.5f);
        }
    }
    size_t n = sl_png_encode_rgb(rgb, s, s, png);
    free(rgb);
    return n;
}
size_t sl_net_remote_icon(int size, unsigned char **png) { return rm_icon(size, png); }

/* the manifest: what a phone needs to keep the page as an app */
static const char rm_manifest[] =
    "{\"name\":\"GabagoolOS Remote\",\"short_name\":\"GabagoolOS\",\"id\":\"/\",\"start_url\":\"/?app\","
    "\"scope\":\"/\",\"display\":\"standalone\",\"orientation\":\"portrait\","
    "\"background_color\":\"#0d1219\",\"theme_color\":\"#0d1219\","
    "\"description\":\"Play, pause, skip, search and queue on your HiBy R1 from your phone.\","
    "\"icons\":[{\"src\":\"/icon-192.png\",\"sizes\":\"192x192\",\"type\":\"image/png\",\"purpose\":\"any\"},"
    "{\"src\":\"/icon-512.png\",\"sizes\":\"512x512\",\"type\":\"image/png\",\"purpose\":\"any\"},"
    "{\"src\":\"/icon-512.png\",\"sizes\":\"512x512\",\"type\":\"image/png\",\"purpose\":\"maskable\"}]}";

void sl_net_remote_tint(uint32_t accent, uint32_t ink) { rm_ic_acc = accent; rm_ic_ink = ink; }
void sl_net_remote_cover(const char *path, long off, long size, int kind, unsigned key)
{
    pthread_mutex_lock(&rm_lock);
    snprintf(rm_cov.path, sizeof rm_cov.path, "%s", path ? path : "");
    rm_cov.off = off;
    rm_cov.size = size;
    rm_cov.kind = kind;
    rm_cov.key = key;
    pthread_mutex_unlock(&rm_lock);
}
/* the cover's own bytes, as they are on the card: nothing decoded here,
 * the phone scales it. A tag's unsynchronised picture is undone on the way. */
static void rm_cover(int fd, const char *query)
{
    char k[16], real[600];
    sl_net_query_param(query, "k", k, sizeof k);
    pthread_mutex_lock(&rm_lock);
    long off = rm_cov.off, size = rm_cov.size;
    int kind = rm_cov.kind;
    unsigned key = rm_cov.key;
    snprintf(real, sizeof real, "%s%s", net_root() ? net_root() : "", rm_cov.path);
    pthread_mutex_unlock(&rm_lock);
    int f = key && (unsigned)strtoul(k, NULL, 10) == key && !net_card_held ? open(real, O_RDONLY) : -1;
    if (f >= 0 && size < 0) { off_t end = lseek(f, 0, SEEK_END); size = end > off ? (long)(end - off) : 0; }
    if (f < 0 || size <= 0 || size > SL_REMOTE_COVER_MAX || lseek(f, off, SEEK_SET) != off)
    {
        if (f >= 0) close(f);
        rm_reply(fd, "404 Not Found", "text/plain", "No cover", 8);
        return;
    }
    bool unsync = (kind & SL_REMOTE_COVER_UNSYNC) != 0;
    const char *type = (kind & 15) == SL_REMOTE_COVER_PNG ? "image/png" : "image/jpeg";
    /* the URL names this cover alone: the phone keeps it */
    rm_head(fd, "200 OK", type, "max-age=31536000, immutable", unsync ? -1 : size);
    static char buf[16 * 1024];
    bool ff = false;
    while (size > 0 && !net_card_held && (int32_t)(net_ms() - rm_send_by) < 0)   /* USB mode: let go of the card at once */
    {
        ssize_t r = read(f, buf, (size_t)(size < (long)sizeof buf ? size : (long)sizeof buf));
        if (r <= 0) break;
        size -= r;
        size_t n = (size_t)r;
        if (unsync)
        {
            size_t o = 0;
            for (size_t i = 0; i < n; i++)
            {
                if (ff && buf[i] == 0) { ff = false; continue; }   /* FF 00 was FF */
                ff = (unsigned char)buf[i] == 0xff;
                buf[o++] = buf[i];
            }
            n = o;
        }
        rm_send(fd, buf, n);
    }
    close(f);
    sl_net_remote_served++;
}
/* a header's value in the head req (up to its blank line), cut to n */
static bool rm_header(const char *req, const char *name, char *out, size_t n)
{
    const char *end = strstr(req, "\r\n\r\n"), *h = req;
    size_t k = strlen(name);
    while ((h = strstr(h, "\r\n")) && (!end || h < end))
    {
        h += 2;
        if (strncasecmp(h, name, k) || h[k] != ':') continue;
        h += k + 1;
        while (*h == ' ' || *h == '\t') h++;
        size_t l = strcspn(h, "\r\n");
        if (l >= n) l = n - 1;
        memcpy(out, h, l);
        out[l] = '\0';
        return true;
    }
    return false;
}
/* Asked by the page this player serves, at its own address: never by
 * another web site a phone has open (a link or a form there would press
 * our buttons), nor through a name that is really someone else's (a
 * DNS-rebinding page reading the library). Phones open us by our address. */
static bool rm_trusted(const char *req)
{
    char v[200];
    if (rm_header(req, "Sec-Fetch-Site", v, sizeof v) && strcmp(v, "same-origin") && strcmp(v, "none")) return false;
    char host[200] = "";
    if (rm_header(req, "Host", host, sizeof host))
    {
        size_t hl = strcspn(host, ":");
        bool ip = hl > 0;
        for (size_t i = 0; i < hl; i++) if (!isdigit((unsigned char)host[i]) && host[i] != '.') ip = false;
        if (!ip && strncmp(host, "localhost", hl > 9 ? hl : 9) && host[0] != '[') return false;
    }
    if (rm_header(req, "Origin", v, sizeof v) && (strncmp(v, "http://", 7) || strcmp(v + 7, host))) return false;
    return true;
}
/* ---- pairing: a phone new to the player asks (/pair), the player shows
 * a code of six digits for two minutes, and the phone sends it back
 * (/pair?code=). Right, it gets a token of its own in a cookie, kept on
 * the card too, and every request but the page, its manifest and icons
 * and /pair must carry it (401 without). Five wrong codes and the code is
 * gone and /pair says wait (429) for a minute: a guesser gets five tries
 * a minute at a million codes. Forget (the Wi-Fi page) drops them all. */
#define RM_PAIRS 8
#define RM_TOK 32                            /* hex digits: 128 random bits */
#define RM_CODE_MS 120000
#define RM_TRIES 5
#define RM_LOCK_MS 60000
#define RM_PAIR_FILE "/.rockbox/sloppy/remote-phones"
static pthread_mutex_t rm_pair_lock = PTHREAD_MUTEX_INITIALIZER;
static char rm_tok[RM_PAIRS][RM_TOK + 1];    /* under rm_pair_lock; oldest first */
static int rm_ntok;
static bool rm_tok_read;                     /* the card's list is in */
static char rm_pcode[8];                     /* the code on screen; "" none */
static uint32_t rm_pcode_until, rm_plock_until;
static unsigned rm_pcode_serial;
static int rm_pfails;
static void rm_random(unsigned char *b, size_t n)
{
    int f = open("/dev/urandom", O_RDONLY);
    ssize_t r = f >= 0 ? read(f, b, n) : -1;
    if (f >= 0) close(f);
    if (r != (ssize_t)n)                     /* never on Linux; still something */
    {
        struct timespec t;
        clock_gettime(CLOCK_MONOTONIC, &t);
        uint32_t x = (uint32_t)t.tv_nsec ^ (uint32_t)t.tv_sec * 2654435761u ^ (uint32_t)getpid();
        for (size_t i = 0; i < n; i++) { x ^= x << 13; x ^= x >> 17; x ^= x << 5; b[i] = (unsigned char)x; }
    }
}
static void rm_tok_load(void)                /* under rm_pair_lock */
{
    if (rm_tok_read || net_card_held || !net_root()) return;
    char path[256], line[64];
    snprintf(path, sizeof path, "%s" RM_PAIR_FILE, net_root());
    FILE *f = fopen(path, "r");
    if (!f && errno != ENOENT) return;       /* the card away: ask again later */
    rm_tok_read = true;
    rm_ntok = 0;
    while (f && rm_ntok < RM_PAIRS && fgets(line, sizeof line, f))
        if (strspn(line, "0123456789abcdef") == RM_TOK) { memcpy(rm_tok[rm_ntok], line, RM_TOK); rm_tok[rm_ntok++][RM_TOK] = '\0'; }
    if (f) fclose(f);
}
static void rm_tok_save(void)                /* under rm_pair_lock */
{
    if (net_card_held || !net_root()) return;   /* kept until the player stops */
    char path[256], tmp[264];
    snprintf(path, sizeof path, "%s" RM_PAIR_FILE, net_root());
    if (!rm_ntok) { remove(path); return; }
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w");
    if (!f) return;
    for (int i = 0; i < rm_ntok; i++) fprintf(f, "%s\n", rm_tok[i]);
    bool ok = fflush(f) == 0 && fsync(fileno(f)) == 0;   /* on the card before the rename */
    if (fclose(f) || !ok || rename(tmp, path)) remove(tmp);
}
/* the request's token is one we gave */
static bool rm_paired(const char *req)
{
    char c[512];
    if (!rm_header(req, "Cookie", c, sizeof c)) return false;
    const char *v = NULL;
    for (const char *p = c; (p = strstr(p, "gbtok=")); p += 6)
        if (p == c || p[-1] == ' ' || p[-1] == ';') { v = p + 6; break; }
    if (!v || strspn(v, "0123456789abcdef") != RM_TOK) return false;
    bool ok = false;
    pthread_mutex_lock(&rm_pair_lock);
    rm_tok_load();
    for (int i = 0; i < rm_ntok; i++)
    {
        unsigned d = 0;                      /* every digit looked at: no timing to learn it by */
        for (int k = 0; k < RM_TOK; k++) d |= (unsigned)(rm_tok[i][k] ^ v[k]);
        ok |= !d;
    }
    pthread_mutex_unlock(&rm_pair_lock);
    return ok;
}
static void rm_pair(int fd, const char *query)
{
    char code[16], cookie[128], tok[RM_TOK + 1];
    bool has = query && sl_net_query_param(query, "code", code, sizeof code);
    uint32_t now = net_ms();
    int st;
    pthread_mutex_lock(&rm_pair_lock);
    if (rm_pcode[0] && (int32_t)(now - rm_pcode_until) >= 0) rm_pcode[0] = '\0';
    if ((int32_t)(now - rm_plock_until) < 0) st = 429;
    else if (!has)
    {
        if (!rm_pcode[0])                    /* a code on the player's screen: a new one only when none waits */
        {
            unsigned char r[4];
            rm_random(r, sizeof r);
            snprintf(rm_pcode, sizeof rm_pcode, "%06lu", (unsigned long)(((uint32_t)r[0] << 24 | r[1] << 16 | r[2] << 8 | r[3]) % 1000000u));
            rm_pcode_serial++;
            rm_pcode_until = now + RM_CODE_MS;   /* asking again keeps neither it nor its tries going */
        }
        st = 202;
    }
    else if (!rm_pcode[0]) st = 410;
    else if (strcmp(code, rm_pcode))
    {
        st = 403;
        if (++rm_pfails >= RM_TRIES) { rm_pcode[0] = '\0'; rm_pfails = 0; rm_plock_until = now + RM_LOCK_MS; st = 429; }
    }
    else
    {
        unsigned char r[RM_TOK / 2];
        rm_random(r, sizeof r);
        for (int i = 0; i < RM_TOK / 2; i++) snprintf(tok + 2 * i, 3, "%02x", r[i]);
        rm_tok_load();
        if (rm_ntok == RM_PAIRS) { memmove(rm_tok[0], rm_tok[1], sizeof rm_tok[0] * (RM_PAIRS - 1)); rm_ntok--; }   /* the oldest phone goes */
        memcpy(rm_tok[rm_ntok++], tok, sizeof tok);
        rm_tok_save();
        rm_pcode[0] = '\0';
        rm_pfails = 0;
        st = 200;
    }
    pthread_mutex_unlock(&rm_pair_lock);
    static const struct { int code; const char *status, *body; } a[] = {
        { 200, "200 OK", "{\"ok\":true}" },
        { 202, "202 Accepted", "{\"code\":6}" },   /* the player shows it */
        { 403, "403 Forbidden", "{\"error\":\"code\"}" },
        { 410, "410 Gone", "{\"error\":\"expired\"}" },
        { 429, "429 Too Many Requests", "{\"error\":\"wait\"}" },
    };
    unsigned k = 0;
    while (a[k].code != st) k++;
    if (st == 200)
    {
        /* a year, then pair again; never sent to another site, nor read by a script */
        snprintf(cookie, sizeof cookie, "Set-Cookie: gbtok=%s; Max-Age=31536000; Path=/; HttpOnly; SameSite=Strict\r\n", tok);
        rm_extra = cookie;
    }
    rm_reply(fd, a[k].status, "application/json", a[k].body, strlen(a[k].body));
}
bool sl_net_remote_pair_code(char *code, size_t n, unsigned *serial)
{
    pthread_mutex_lock(&rm_pair_lock);
    if (rm_pcode[0] && (int32_t)(net_ms() - rm_pcode_until) >= 0) rm_pcode[0] = '\0';
    bool on = rm_pcode[0];
    snprintf(code, n, "%s", rm_pcode);
    *serial = rm_pcode_serial;
    pthread_mutex_unlock(&rm_pair_lock);
    return on;
}
void sl_net_remote_pair_cancel(void)
{
    pthread_mutex_lock(&rm_pair_lock);
    rm_pcode[0] = '\0';
    pthread_mutex_unlock(&rm_pair_lock);
}
int sl_net_remote_paired(void)
{
    pthread_mutex_lock(&rm_pair_lock);
    rm_tok_load();
    int n = rm_ntok;
    pthread_mutex_unlock(&rm_pair_lock);
    return n;
}
void sl_net_remote_forget(void)
{
    pthread_mutex_lock(&rm_pair_lock);
    rm_tok_load();
    rm_ntok = 0;
    rm_tok_read = true;                      /* none, even if the card could not be told */
    rm_tok_save();
    rm_pcode[0] = '\0';
    rm_pfails = 0;
    rm_plock_until = net_ms();               /* a fresh start: whoever holds the player may pair at once */
    pthread_mutex_unlock(&rm_pair_lock);
}
/* A question for the UI thread (rm_tick answers it): false when it gave
 * no answer within `secs`. */
static bool rm_ask_ui(const char *path, const char *q, char *out, size_t n, int secs)
{
    bool ok = false;
    pthread_mutex_lock(&rm_lock);
    snprintf(rm_path, sizeof rm_path, "%s", path);
    snprintf(rm_query, sizeof rm_query, "%s", q ? q : "");
    rm_pending = true;
    rm_taken = rm_done = false;
    rm_seq++;
    struct timespec until;
    clock_gettime(CLOCK_REALTIME, &until);
    until.tv_sec += secs;
    while (!rm_done && rm_run)
        if (pthread_cond_timedwait(&rm_cond, &rm_lock, &until)) break;
    if (rm_done) { snprintf(out, n, "%s", rm_body); ok = true; }
    rm_pending = false;
    pthread_mutex_unlock(&rm_lock);
    return ok;
}
/* "Download bug report": the player writes it to the card (the same file
 * Settings > Advanced makes), and the phone gets that file to save */
static void rm_report(int fd)
{
    static char answer[512];
    char path[300] = "", disp[160];
    const char *p = rm_ask_ui("/api/report", NULL, answer, sizeof answer, 10) ? strstr(answer, "\"path\":\"") : NULL;
    if (p) { p += 8; snprintf(path, sizeof path, "%.*s", (int)strcspn(p, "\""), p); }
    int in = path[0] ? open(path, O_RDONLY) : -1;
    struct stat st;
    char *body = in >= 0 && fstat(in, &st) == 0 && st.st_size > 0 && st.st_size < 1024 * 1024 ? malloc(st.st_size) : NULL;
    ssize_t got = body ? read(in, body, st.st_size) : -1;
    if (in >= 0) close(in);
    if (got > 0)
    {
        const char *name = strrchr(path, '/');
        snprintf(disp, sizeof disp, "Content-Disposition: attachment; filename=\"%s\"\r\n", name ? name + 1 : path);
        rm_extra = disp;
        rm_reply(fd, "200 OK", "text/plain; charset=utf-8", body, (size_t)got);
    }
    else rm_reply(fd, "503 Service Unavailable", "text/plain", "The report could not be made", 28);
    free(body);
}
static void rm_client(int fd, char *req)
{
    struct timeval tv = { 5, 0 };
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);   /* a phone that stops reading lets go in time */
    if (!rm_trusted(req))
    {
        rm_reply(fd, "403 Forbidden", "text/plain", "Open this from the player's own address", 39);
        return;
    }
    bool paired = rm_paired(req);        /* before the path is cut out of req, its headers with it */
    char *sp = strchr(req, ' ');
    if (!sp) return;
    char *path = sp + 1, *end = strchr(path, ' ');
    if (!end) return;
    *end = '\0';
    char *q = strchr(path, '?');
    if (q) *q++ = '\0';
    if (!strcmp(path, "/"))
    {
        rm_reply_c(fd, "200 OK", "text/html; charset=utf-8", "no-cache", sl_remote_html, sizeof sl_remote_html - 1);
        return;
    }
    if (!strcmp(path, "/manifest.webmanifest"))
    {
        rm_reply_c(fd, "200 OK", "application/manifest+json", "no-cache", rm_manifest, sizeof rm_manifest - 1);
        return;
    }
    int isz = !strcmp(path, "/icon-192.png") ? 192 : !strcmp(path, "/icon-512.png") ? 512 :
              !strcmp(path, "/apple-touch-icon.png") || !strcmp(path, "/apple-touch-icon-precomposed.png") ? 180 :
              !strcmp(path, "/favicon.ico") || !strcmp(path, "/icon-48.png") ? 48 : 0;
    if (isz)
    {
        unsigned char *png;
        size_t n = rm_icon(isz, &png);
        if (n) rm_reply_c(fd, "200 OK", "image/png", "max-age=86400", png, n);
        else rm_reply(fd, "503 Service Unavailable", "text/plain", "No memory", 9);
        free(png);
        return;
    }
    if (!strcmp(path, "/pair")) { rm_pair(fd, q); return; }
    /* the page's words may come before pairing: its pairing card needs them */
    if (strcmp(path, "/api/hello") && !paired)
    {
        rm_reply(fd, "401 Unauthorized", "application/json", "{\"error\":\"pair\"}", 16);
        return;
    }
    if (!strcmp(path, "/cover")) { rm_cover(fd, q); return; }
    if (!strcmp(path, "/report.txt")) { rm_report(fd); return; }
    if (!strcmp(path, "/shot.png"))
    {
        /* the last screenshot, as it went to the card (sloppy_png.c keeps it) */
        size_t cap = sl_shot_png_size();
        void *png = cap ? malloc(cap) : NULL;
        size_t n = png ? sl_shot_png(png, cap, NULL) : 0;
        if (n) rm_reply(fd, "200 OK", "image/png", png, n);
        else rm_reply(fd, "404 Not Found", "text/plain", "No screenshot yet", 17);
        free(png);
        return;
    }
    if (strncmp(path, "/api/", 5))
    {
        rm_reply(fd, "404 Not Found", "text/plain", "Not found", 9);
        return;
    }
    static char out[sizeof rm_body];
    if (rm_ask_ui(path, q, out, sizeof out, 3)) rm_reply(fd, "200 OK", "application/json; charset=utf-8", out, strlen(out));
    else rm_reply(fd, "503 Service Unavailable", "application/json", "{\"error\":\"busy\"}", 16);
}
static void rm_drop(int i)
{
    if (rm_conn[i].up) { rm_conn[i].up = false; sl_ota_upload_end(false); }   /* gone before the end: nothing kept */
    close(rm_conn[i].fd);
    rm_conn[i].fd = -1;
}
static void rm_up_answer(int i, int code)
{
    static const struct { int code; const char *status, *body; } a[] = {
        { 200, "200 OK", "{\"ok\":true}" },
        { 400, "400 Bad Request", "{\"error\":\"length\"}" },
        { 401, "401 Unauthorized", "{\"error\":\"pair\"}" },
        { 403, "403 Forbidden", "{\"error\":\"nokey\"}" },
        { 409, "409 Conflict", "{\"error\":\"busy\"}" },
        { 413, "413 Payload Too Large", "{\"error\":\"size\"}" },
        { 421, "421 Misdirected Request", "{\"error\":\"origin\"}" },   /* not from the player's own page */
        { 503, "503 Service Unavailable", "{\"error\":\"usb\"}" },
        { 507, "507 Insufficient Storage", "{\"error\":\"space\"}" },
    };
    unsigned k = 0;
    while (k + 1 < sizeof a / sizeof *a && a[k].code != code) k++;
    if (a[k].code != code) k = 1;
    rm_reply(rm_conn[i].fd, a[k].status, "application/json", a[k].body, strlen(a[k].body));
}
/* the head is in: an upload starts (true), or it is an ordinary request */
static bool rm_up_begin(int i)
{
    char *req = rm_conn[i].req, *end = strstr(req, "\r\n\r\n");
    if (strncmp(req, "POST /update ", 13) || !end) return false;
    if (!rm_trusted(req)) { rm_up_answer(i, 421); rm_drop(i); return true; }
    if (!rm_paired(req)) { rm_up_answer(i, 401); rm_drop(i); return true; }
    char *cl = strcasestr(req, "\r\nContent-Length:");
    unsigned long long len = cl && cl < end ? strtoull(cl + 17, NULL, 10) : 0;
    int code = len ? sl_ota_upload_begin(len) : 400;
    if (code) { rm_up_answer(i, code); rm_drop(i); return true; }
    rm_conn[i].up = true;
    rm_conn[i].up_left = len;
    size_t have = rm_conn[i].got - (size_t)(end + 4 - req);
    if (have > len) have = (size_t)len;
    if (have && !sl_ota_upload_write(end + 4, have)) { rm_conn[i].up = false; sl_ota_upload_end(false); rm_up_answer(i, 503); rm_drop(i); return true; }
    rm_conn[i].up_left -= have;
    if (!rm_conn[i].up_left) { rm_conn[i].up = false; sl_ota_upload_end(true); rm_up_answer(i, 200); rm_drop(i); }
    return true;
}
static void rm_up_more(int i)
{
    static char buf[16 * 1024];
    size_t want = rm_conn[i].up_left < sizeof buf ? (size_t)rm_conn[i].up_left : sizeof buf;
    ssize_t r = recv(rm_conn[i].fd, buf, want, 0);
    if (r <= 0) { rm_drop(i); return; }
    rm_conn[i].t0 = net_ms();
    if (!sl_ota_upload_write(buf, (size_t)r)) { rm_conn[i].up = false; sl_ota_upload_end(false); rm_up_answer(i, 503); rm_drop(i); return; }
    rm_conn[i].up_left -= (uint64_t)r;
    if (!rm_conn[i].up_left) { rm_conn[i].up = false; sl_ota_upload_end(true); rm_up_answer(i, 200); rm_drop(i); }
}
static void *rm_loop(void *unused)
{
    (void)unused;
    for (int i = 0; i < RM_CONNS; i++) rm_conn[i].fd = -1;
    while (rm_run)
    {
        fd_set rd;
        FD_ZERO(&rd);
        FD_SET(rm_sock, &rd);
        int top = rm_sock;
        for (int i = 0; i < RM_CONNS; i++)
            if (rm_conn[i].fd >= 0) { FD_SET(rm_conn[i].fd, &rd); if (rm_conn[i].fd > top) top = rm_conn[i].fd; }
        struct timeval tv = { 0, 500000 };
        int ready = select(top + 1, &rd, NULL, NULL, &tv);
        uint32_t now = net_ms();
        if (ready > 0 && FD_ISSET(rm_sock, &rd))
        {
            int c = accept(rm_sock, NULL, NULL);
            int slot = -1;
            for (int i = 0; c >= 0 && i < RM_CONNS && slot < 0; i++) if (rm_conn[i].fd < 0) slot = i;
            if (c >= 0 && slot < 0) close(c);   /* all six busy: the phone tries again */
            else if (c >= 0) { rm_conn[slot].fd = c; rm_conn[slot].got = 0; rm_conn[slot].t0 = now; rm_conn[slot].up = false; }
        }
        for (int i = 0; i < RM_CONNS; i++)
        {
            if (rm_conn[i].fd < 0) continue;
            if (rm_conn[i].up)
            {
                if (ready > 0 && FD_ISSET(rm_conn[i].fd, &rd)) rm_up_more(i);
                else if (now - rm_conn[i].t0 > RM_UP_IDLE_MS) rm_drop(i);   /* the phone went quiet */
                continue;
            }
            if (ready > 0 && FD_ISSET(rm_conn[i].fd, &rd))
            {
                ssize_t r = recv(rm_conn[i].fd, rm_conn[i].req + rm_conn[i].got, RM_REQ - 1 - rm_conn[i].got, 0);
                if (r <= 0) { rm_drop(i); continue; }
                rm_conn[i].got += (size_t)r;
                rm_conn[i].req[rm_conn[i].got] = '\0';
                if (strstr(rm_conn[i].req, "\r\n\r\n") && rm_up_begin(i)) continue;
                if (strstr(rm_conn[i].req, "\r\n\r\n") || rm_conn[i].got >= RM_REQ - 1)
                {
                    rm_client(rm_conn[i].fd, rm_conn[i].req);
                    rm_drop(i);
                    continue;
                }
            }
            if (now - rm_conn[i].t0 > 5000) rm_drop(i);   /* opened and never asked */
        }
    }
    for (int i = 0; i < RM_CONNS; i++) if (rm_conn[i].fd >= 0) rm_drop(i);
    return NULL;
}
bool sl_net_remote_start(void)
{
    if (rm_up) return true;
    int one = 1;
    rm_sock = socket(AF_INET, SOCK_STREAM, 0);
    if (rm_sock < 0) return false;
    setsockopt(rm_sock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    struct sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_ANY);
    a.sin_port = htons(SL_REMOTE_PORT);
    if (bind(rm_sock, (struct sockaddr *)&a, sizeof a) || listen(rm_sock, 4)) goto fail;
    rm_run = true;
    if (pthread_create(&rm_thread, NULL, rm_loop, NULL)) goto fail;
    rm_up = true;
    return true;
fail:
    rm_run = false;
    close(rm_sock);
    rm_sock = -1;
    return false;
}
void sl_net_remote_stop(void)
{
    if (!rm_up) return;
    rm_run = false;
    pthread_mutex_lock(&rm_lock);
    pthread_cond_broadcast(&rm_cond);
    pthread_mutex_unlock(&rm_lock);
    pthread_join(rm_thread, NULL);
    close(rm_sock);
    rm_sock = -1;
    rm_up = false;
}
bool sl_net_remote_on(void) { return rm_up; }
bool sl_net_remote_take(char *path, size_t pn, char *query, size_t qn)
{
    bool got = false;
    pthread_mutex_lock(&rm_lock);
    if (rm_pending && !rm_taken)
    {
        snprintf(path, pn, "%s", rm_path);
        snprintf(query, qn, "%s", rm_query);
        rm_taken = got = true;
        rm_taken_seq = rm_seq;
    }
    pthread_mutex_unlock(&rm_lock);
    return got;
}
void sl_net_remote_answer(const char *json)
{
    pthread_mutex_lock(&rm_lock);
    if (rm_pending && rm_taken && rm_taken_seq == rm_seq)   /* not an answer to a request that timed out */
    {
        snprintf(rm_body, sizeof rm_body, "%s", json);
        rm_done = true;
        pthread_cond_signal(&rm_cond);
    }
    pthread_mutex_unlock(&rm_lock);
}

/* ----------------------------------------------------------- scrobbling */
/* ListenBrainz and the Audioscrobbler log, on one worker thread. Files,
 * from the card root:
 *   /.rockbox/sloppy/scrobble.tsv        listens waiting for ListenBrainz
 *   /.rockbox/sloppy/listenbrainz.token  the user token, and nothing else
 *   /.scrobbler.log                      the Audioscrobbler log for Last.fm
 * ListenBrainz requests use the R1's system libssl through the socket
 * helper; certificates are not checked because the system has no CA bundle.
 * Nothing is sent without a token, and the token is never logged. */
#define SCR_QUEUE   SL_CAST_DIR "/scrobble.tsv"
#define SCR_TOKEN   SL_CAST_DIR "/listenbrainz.token"
#define SCR_LOG     "/.scrobbler.log"
#define SCR_API     "https://api.listenbrainz.org/1/"
#define SCR_CAP     2000             /* listens kept waiting; the oldest go first */
#define SCR_BATCH   20               /* listens per request */
#define SCR_INBOX   16
#define SCR_MSGS    8
#define SCR_LINE    512              /* a queue line: three tags of SL_SCROB_TEXT and numbers */
/* Last.fm: its own queue, and the session a sign-in gives */
#define SCR_LFM_QUEUE   SL_CAST_DIR "/lastfm.tsv"
#define SCR_LFM_SESSION SL_CAST_DIR "/lastfm.session"
#define LFM_TOKEN_MS    (10u * 60u * 1000u)   /* how long a phone sign-in is waited for */
#include "sloppy_lastfm_state.h"
/* The API account's key and secret are not in the program or its source.
 * A release carries them in SCR_KEYS on the card, scrambled (sloppy-dev/
 * make-keys.py writes it): without the file, Last.fm says "Not in this
 * build" and the rest of scrobbling works. The tests set their own. */
#define SCR_KEYS    SL_CAST_DIR "/keys.bin"
const char *sl_lastfm_key = "", *sl_lastfm_secret = "";
unsigned sl_lastfm_poll_ms = 4000;      /* how often a phone sign-in is asked after */

static pthread_mutex_t scr_lock = PTHREAD_MUTEX_INITIALIZER;   /* the shared state below */
static pthread_mutex_t scr_files = PTHREAD_MUTEX_INITIALIZER;  /* held while the worker writes */
static pthread_cond_t scr_cond;
static struct {
    /* from the Rockbox side */
    struct sl_listen inbox[SCR_INBOX];
    int n_inbox, writing;
    struct sl_listen now;
    bool now_pending;
    uint32_t now_ms;
    bool lb_on, log_on, online, hold, test, reload, kick, retry;
    char token[64];
    bool token_new;
    bool lfm_on;
    int lfm_req;                         /* LFM_REQ_*: a sign-in or out asked for */
    char lfm_user[64], lfm_pass[128];    /* a password sign-in's, wiped once used */
    /* to it */
    struct sl_scrobble_status st;
    char msgs[SCR_MSGS][120];
    int msg_first, n_msgs;
    bool started;
} scr;
/* the worker's own */
static struct {
    bool loaded, token_bad, waiting_said, fail_said;
    char token[64];
    int queued, failures, split;
    uint32_t next_ms;
    /* Last.fm */
    bool lfm_loaded, lfm_lost, lfm_fail_said, lfm_key_refused;
    char lfm_sk[40], lfm_name[64];       /* the session: never logged */
    int lfm_queued, lfm_failures;
    uint32_t lfm_next_ms;
    char lfm_token[40];                  /* a phone sign-in waiting to be allowed */
    uint32_t lfm_token_until, lfm_poll_ms;
} sw;
enum { LFM_REQ_NONE, LFM_REQ_PHONE, LFM_REQ_PASSWORD, LFM_REQ_CANCEL, LFM_REQ_SIGNOUT };
#if defined(SIMULATOR) || defined(SLOPPY_NET_TEST)
int (*sl_net_scrobble_fake)(const char *url, const char *auth, const char *body, char *out, size_t cap);
#endif

/* a line for the Rockbox log (the worker may not write it itself) */
static void __attribute__((format(printf, 1, 2))) scr_say(const char *fmt, ...)
{
    char b[120];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(b, sizeof b, fmt, ap);
    va_end(ap);
    pthread_mutex_lock(&scr_lock);
    if (scr.n_msgs == SCR_MSGS) { scr.msg_first = (scr.msg_first + 1) % SCR_MSGS; scr.n_msgs--; }   /* the oldest goes */
    memcpy(scr.msgs[(scr.msg_first + scr.n_msgs++) % SCR_MSGS], b, sizeof b);
    pthread_mutex_unlock(&scr_lock);
}

static void scr_error(const char *e, bool tell)
{
    pthread_mutex_lock(&scr_lock);
    snprintf(scr.st.error, sizeof scr.st.error, "%s", e);
    if (tell) scr.st.fail_seq++;
    pthread_mutex_unlock(&scr_lock);
}

static bool scr_path(char *p, size_t n, const char *name)
{
    const char *root = net_root();
    return root && snprintf(p, n, "%s%s", root, name) < (int)n;
}

/* ---- the files: only with scr_files held and no USB mode */
static void scr_token_load(void)
{
    char p[256], t[80] = "";
    sw.token[0] = '\0';
    int fd = scr_path(p, sizeof p, SCR_TOKEN) ? open(p, O_RDONLY) : -1;
    if (fd < 0) return;
    ssize_t r = read(fd, t, sizeof t - 1);
    close(fd);
    t[r > 0 ? r : 0] = '\0';
    t[strcspn(t, " \t\r\n")] = '\0';
    bool ok = t[0] && strlen(t) < sizeof sw.token;
    for (const char *c = t; ok && *c; c++)
        ok = (*c >= '0' && *c <= '9') || (*c >= 'a' && *c <= 'z') || (*c >= 'A' && *c <= 'Z') || *c == '-';
    if (ok) strcpy(sw.token, t);
    else scr_say("token file is not a token, ignored");
    memset(t, 0, sizeof t);
}

static void scr_token_save(const char *t)
{
    char p[256];
    if (!scr_path(p, sizeof p, SCR_TOKEN)) return;
    if (!t[0]) { unlink(p); scr_say("token forgotten"); return; }
    char tmp[260];                       /* written aside, then renamed: a power cut keeps the old one */
    snprintf(tmp, sizeof tmp, "%s.tmp", p);
    int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    bool ok = fd >= 0 && write(fd, t, strlen(t)) == (ssize_t)strlen(t) && write(fd, "\n", 1) == 1 && fsync(fd) == 0;
    if (fd >= 0 && close(fd)) ok = false;
    if (ok) ok = rename(tmp, p) == 0;
    if (!ok) unlink(tmp);
    scr_say(ok ? "token saved" : "could not save the token");
}

static int scr_count_lines(const char *name)
{
    char p[256], b[4096];
    int fd = scr_path(p, sizeof p, name) ? open(p, O_RDONLY) : -1, n = 0;
    if (fd < 0) return 0;
    ssize_t r;
    while ((r = read(fd, b, sizeof b)) > 0)
        for (ssize_t i = 0; i < r; i++) n += b[i] == '\n';
    close(fd);
    return n;
}

/* one line at the end of a file; a line torn by a power cut is ended first */
static bool scr_append(const char *name, const char *header, const char *line)
{
    char p[256];
    if (!scr_path(p, sizeof p, name)) return false;
    int fd = open(p, O_RDWR | O_CREAT | O_APPEND, 0666);
    if (fd < 0) return false;
    off_t size = lseek(fd, 0, SEEK_END);
    char last = '\n';
    if (size > 0 && pread(fd, &last, 1, size - 1) != 1) last = '\n';
    bool ok = size >= 0;
    if (ok && size == 0 && header) ok = write(fd, header, strlen(header)) == (ssize_t)strlen(header);
    if (ok && last != '\n') ok = write(fd, "\n", 1) == 1;
    if (ok) ok = write(fd, line, strlen(line)) == (ssize_t)strlen(line);
    fsync(fd);
    close(fd);
    return ok;
}

/* a queue without its first n lines: copied to a new file, then renamed;
 * *queued gets what is left */
static bool scr_drop(const char *name, int n, int *queued)
{
    char p[256], tmp[272], b[4096];
    if (n <= 0) return true;
    if (!scr_path(p, sizeof p, name)) return false;
    snprintf(tmp, sizeof tmp, "%s.tmp", p);
    int in = open(p, O_RDONLY);
    if (in < 0) { *queued = 0; return true; }
    int out = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0666);
    if (out < 0) { close(in); return false; }
    int skip = n, kept = 0;
    bool ok = true;
    ssize_t r;
    while (ok && (r = read(in, b, sizeof b)) > 0)
    {
        ssize_t from = 0;
        while (skip && from < r) if (b[from++] == '\n') skip--;
        for (ssize_t i = from; i < r; i++) kept += b[i] == '\n';
        if (from < r) ok = write(out, b + from, (size_t)(r - from)) == r - from;
    }
    close(in);
    if (ok) ok = fsync(out) == 0;
    if (close(out)) ok = false;
    if (!ok || rename(tmp, p)) { unlink(tmp); return false; }
    *queued = kept;
    return true;
}

/* Up to max listens from the start of the queue. A first line that is no
 * listen (a power cut's leftover) is dropped on the spot. */
static int scr_read(const char *name, int *queued, struct sl_listen *l, int max)
{
    char p[256];
    static char b[SCR_BATCH * SCR_LINE];
    for (int tries = 0; tries < 8; tries++)
    {
        int fd = scr_path(p, sizeof p, name) ? open(p, O_RDONLY) : -1;
        if (fd < 0) return 0;
        ssize_t r = read(fd, b, sizeof b - 1);
        close(fd);
        if (r <= 0) return 0;
        b[r] = '\0';
        int n = 0;
        bool whole = strchr(b, '\n') != NULL;   /* at least one ended line */
        char *s = b, *e;
        while (n < max && (e = strchr(s, '\n')))
        {
            *e = '\0';
            if (!sl_scrob_parse_line(s, &l[n])) break;
            n++;
            s = e + 1;
        }
        if (n || !whole) return n;
        scr_say("dropped a queue line that is not a listen");
        if (!scr_drop(name, 1, queued)) return 0;
    }
    return 0;
}

/* ---- the network */
/* The HTTP status of wget's report (-S prints the status line), 0 none */
static __attribute__((unused)) int scr_status(const char *out)
{
    const char *h = strstr(out, "HTTP/1.");
    return h ? atoi(h + 9) : 0;
}

/* One scrobble request; ListenBrainz uses the R1's OpenSSL socket helper,
 * while Last.fm keeps its existing wget form request. */
struct scr_reply { char *out; size_t cap, used; };
static bool scr_reply_sink(void *ctx, const char *data, size_t n)
{
    struct scr_reply *reply = ctx;
    if (!reply->cap || reply->used >= reply->cap - 1) return false;
    size_t room = reply->cap - 1 - reply->used;
    if (n > room) return false;
    memcpy(reply->out + reply->used, data, n);
    reply->used += n;
    reply->out[reply->used] = '\0';
    return true;
}

static int scr_http_as(const char *url, const char *body, char *out, size_t cap, bool listenbrainz)
{
    char auth[96] = "";
    if (listenbrainz) snprintf(auth, sizeof auth, "Authorization: Token %s", sw.token);
    int status;
#ifdef NET_DEMO
    out[0] = '\0';
    if (sl_net_scrobble_fake) status = sl_net_scrobble_fake(url, auth, body, out, cap);
    else
    {
        /* the simulator's pretend server takes anything */
        snprintf(out, cap, "  HTTP/1.1 200 OK\n%s", strstr(url, "validate-token") ?
                 "{\"code\":200,\"message\":\"Token valid.\",\"valid\":true,\"user_name\":\"demo\"}" : "{\"status\":\"ok\"}");
        status = 200;
    }
#else
    if (listenbrainz)
    {
        struct scr_reply reply = { out, cap, 0 };
        struct sl_net_req req = {
            .method = body ? "POST" : "GET", .url = url, .ua = "GabagoolOS",
            .headers = auth, .body = body, .timeout_ms = 20000,
            .sink = scr_reply_sink, .ctx = &reply
        };
        if (cap) out[0] = '\0';
        status = cap ? sl_net_http_req(&req) : -1;
    }
    else
    {
        /* Last.fm retains its form-encoded request through wget. */
        const char *argv[] = { "/bin/sh", "-c",
            "exec /usr/bin/wget -q -S -T 20 -U GabagoolOS -O - --post-data \"$2\" \"$3\" 2>&1",
            "wget", auth, body ? body : "", url, NULL };
        net_run(out, cap, 30000, argv);
        status = scr_status(out);
        if (!status) status = -1;
    }
#endif
    /* whatever came back, the token is not in it (a Last.fm answer is
     * only read for its numbers and a new session, never logged) */
    for (char *t = sw.token[0] ? strstr(out, sw.token) : NULL; t; t = strstr(t, sw.token))
        memset(t, '*', strlen(sw.token));
    memset(auth, 0, sizeof auth);
    return status;
}
static int scr_http(const char *url, const char *body, char *out, size_t cap) { return scr_http_as(url, body, out, cap, true); }


#ifndef NET_DEMO
int sl_net_get(const char *url, char *out, size_t cap)
{
    if (cap < 2) return -1;
    const char *argv[] = { "/usr/bin/wget", "-q", "-T", "30", "-U", "GabagoolOS", "-O", "-", url, NULL };
    if (net_run(out, cap, 60000, argv) != 0) return -1;
    return (int)strlen(out);
}
#endif

/* A GET for the library jobs (sloppy_libjob.c): the answer's text into
 * out, or its bytes into the file at path (the C library's) when path is
 * given. Returns the HTTP status, -1 with no answer. ua names us, as
 * MusicBrainz asks. Blocking, up to timeout_ms: its own thread only. */
#if defined(SIMULATOR) || defined(SLOPPY_NET_TEST)
int (*sl_net_http_fake)(const char *url, char *out, size_t cap, const char *path);
#endif
int sl_net_http_get(const char *url, const char *ua, char *out, size_t cap, const char *path, int timeout_ms)
{
    if (out && cap) out[0] = '\0';
#ifdef NET_DEMO
    (void)ua; (void)timeout_ms;
    return sl_net_http_fake ? sl_net_http_fake(url, out, cap, path) : -1;
#else
    static char report[2048];
    char *buf = path ? report : out;
    size_t bcap = path ? sizeof report : cap;
    const char *argv[] = { "/bin/sh", "-c", path ?
        "exec /usr/bin/wget -q -S -T 20 -U \"$1\" -O \"$3\" \"$2\" 2>&1" :
        "exec /usr/bin/wget -q -S -T 20 -U \"$1\" -O - \"$2\" 2>&1",
        "wget", ua, url, path ? path : "", NULL };
    net_run(buf, bcap, timeout_ms, argv);
    /* the last status line: a redirect's comes first */
    int status = 0;
    for (const char *h = strstr(buf, "HTTP/1."); h; h = strstr(h + 1, "HTTP/1.")) status = atoi(h + 9);
    if (!status && strstr(buf, "server returned error")) status = 500;
    return status ? status : -1;
#endif
}

/* A GET whose answer goes to sink as it comes, a slice at a time, never
 * kept whole: a podcast feed of megabytes is read by its parser in 4 KB.
 * wget writes the body to one pipe and its report (-S: the status lines)
 * to another. sink returning false, *stop set or timeout_ms with nothing
 * coming ends it. Returns the HTTP status, -1 with no answer. Blocking:
 * a worker thread's. */
int sl_net_http_stream(const char *url, const char *ua, int timeout_ms, bool (*sink)(void *ctx, const char *data, size_t n),
                       void *ctx, volatile bool *stop)
{
#ifdef NET_DEMO
    (void)ua; (void)timeout_ms;
    if (!sl_net_http_fake || (stop && *stop)) return -1;
    size_t cap = 4 * 1024 * 1024;
    char *buf = malloc(cap);
    if (!buf) return -1;
    buf[0] = '\0';
    int status = sl_net_http_fake(url, buf, cap, NULL);
    /* the fake's answer may be bytes (a picture): its length, kept by a fake that says so */
    size_t n = sl_net_http_fake_len ? sl_net_http_fake_len : strlen(buf);
    sl_net_http_fake_len = 0;
    if (status == 200 && sink) for (size_t at = 0; at < n; at += 4096)
        if (!sink(ctx, buf + at, n - at < 4096 ? n - at : 4096) || (stop && *stop)) break;
    free(buf);
    return status;
#else
    int body[2], rep[2];
    char path[128];
    if (!net_path("wget", path, sizeof path)) return -1;
    if (pipe2(body, O_CLOEXEC)) return -1;
    if (pipe2(rep, O_CLOEXEC)) { close(body[0]); close(body[1]); return -1; }
    const char *argv[] = { "wget", "-q", "-S", "-T", "20", "-U", ua, "-O", "-", url, NULL };
    pid_t pid = vfork();
    if (pid < 0) { close(body[0]); close(body[1]); close(rep[0]); close(rep[1]); return -1; }
    if (pid == 0)
    {
        int null = open("/dev/null", O_RDWR);
        dup2(null, 0);
        dup2(body[1], 1);
        dup2(rep[1], 2);
        for (int i = 3; i < 256; i++) close(i);
        execv(path, (char *const *)argv);
        _exit(127);
    }
    close(body[1]);
    close(rep[1]);
    char report[1536], buf[4096];
    size_t rn = 0;
    report[0] = '\0';
    bool body_open = true, rep_open = true, killed = false, enough = false;
    uint32_t quiet_since = net_ms();
    while (body_open || rep_open)
    {
        if ((stop && *stop) || (int32_t)(net_ms() - quiet_since) > timeout_ms) { kill(pid, SIGKILL); killed = true; break; }
        struct pollfd p[2] = { { body_open ? body[0] : -1, POLLIN, 0 }, { rep_open ? rep[0] : -1, POLLIN, 0 } };
        if (poll(p, 2, 250) <= 0) continue;
        if (p[0].revents)
        {
            ssize_t r = read(body[0], buf, sizeof buf);
            if (r <= 0) body_open = false;
            else
            {
                quiet_since = net_ms();
                if (sink && !sink(ctx, buf, (size_t)r)) { kill(pid, SIGKILL); killed = enough = true; break; }
            }
        }
        if (p[1].revents)
        {
            ssize_t r = read(rep[0], buf, sizeof buf);
            if (r <= 0) rep_open = false;
            else
            {
                size_t take = (size_t)r < sizeof report - 1 - rn ? (size_t)r : sizeof report - 1 - rn;
                memcpy(report + rn, buf, take);
                rn += take;
                report[rn] = '\0';
            }
        }
    }
    close(body[0]);
    close(rep[0]);
    waitpid(pid, NULL, 0);
    if (killed && !enough) return -1;    /* timed out, or stopped */
    int status = 0;
    for (const char *h = strstr(report, "HTTP/1."); h; h = strstr(h + 1, "HTTP/1.")) status = atoi(h + 9);
    if (!status && strstr(report, "server returned error")) status = 500;
    return status ? status : -1;
#endif
}
#if defined(SIMULATOR) || defined(SLOPPY_NET_TEST)
size_t sl_net_http_fake_len;
int (*sl_net_dl_fake)(const char *url, const char *path, long long have);
#endif

/* A download that goes on by itself: wget -c into path, so a part
 * already there is continued (a server that will not resume sends it
 * whole, which wget writes over the part). The worker that starts it
 * polls; stopping it leaves the part for next time. Never blocks, except
 * sl_net_dl_stop (up to a second, for wget to go). */
bool sl_net_dl_start(struct sl_net_dl *d, const char *url, const char *ua, const char *path)
{
    memset(d, 0, sizeof *d);
    d->fd = -1;
    snprintf(d->url, sizeof d->url, "%s", url);
    snprintf(d->path, sizeof d->path, "%s", path);
#ifdef NET_DEMO
    (void)ua;
    d->pid = 1;                           /* the fake comes a slice a poll */
    return sl_net_dl_fake != NULL;
#else
    int rep[2];
    char prog[128];
    if (!net_path("wget", prog, sizeof prog) || pipe2(rep, O_CLOEXEC)) return false;
    const char *argv[] = { "wget", "-c", "-q", "-S", "-T", "30", "-U", ua, "-O", path, url, NULL };
    pid_t pid = vfork();
    if (pid < 0) { close(rep[0]); close(rep[1]); return false; }
    if (pid == 0)
    {
        int null = open("/dev/null", O_RDWR);
        dup2(null, 0);
        dup2(null, 1);
        dup2(rep[1], 2);
        for (int i = 3; i < 256; i++) close(i);
        execv(prog, (char *const *)argv);
        _exit(127);
    }
    close(rep[1]);
    fcntl(rep[0], F_SETFL, O_NONBLOCK);
    d->pid = pid;
    d->fd = rep[0];
    return true;
#endif
}
/* 0 still coming, else the HTTP status of the end (200 or 206 whole, -1 none) */
int sl_net_dl_poll(struct sl_net_dl *d)
{
    if (d->pid <= 0) return d->status ? d->status : -1;
#ifdef NET_DEMO
    struct stat st;
    long long have = stat(d->path, &st) ? 0 : (long long)st.st_size;
    int r = sl_net_dl_fake ? sl_net_dl_fake(d->url, d->path, have) : -1;
    if (r == 0) return 0;
    d->pid = 0;
    d->status = r;
    return r;
#else
    char buf[512];
    for (;;)
    {
        ssize_t r = read(d->fd, buf, sizeof buf);
        if (r <= 0) break;
        size_t take = (size_t)r < sizeof d->report - 1 - d->n ? (size_t)r : sizeof d->report - 1 - d->n;
        memcpy(d->report + d->n, buf, take);
        d->n += take;
        d->report[d->n] = '\0';
    }
    int ws;
    pid_t w = waitpid(d->pid, &ws, WNOHANG);
    if (w == 0) return 0;
    d->pid = 0;
    close(d->fd);
    d->fd = -1;
    int status = 0;
    for (const char *h = strstr(d->report, "HTTP/1."); h; h = strstr(h + 1, "HTTP/1.")) status = atoi(h + 9);
    bool ok = w > 0 && WIFEXITED(ws) && WEXITSTATUS(ws) == 0;
    /* wget said nothing but ended well: a part that was whole already (416 is "nothing left") */
    if (ok && !status) status = 200;
    if (!ok && (status == 200 || status == 206)) status = -1;   /* cut off half way */
    if (!status && strstr(d->report, "server returned error")) status = 500;
    d->status = status ? status : -1;
    return d->status;
#endif
}
void sl_net_dl_stop(struct sl_net_dl *d)
{
#ifdef NET_DEMO
    d->pid = 0;
#else
    if (d->pid > 0) net_reap(&d->pid);
    if (d->fd >= 0) close(d->fd);
    d->fd = -1;
#endif
    d->status = -1;
}

/* ---- one request of any method, read by us (sloppy_net.h) */
#ifndef MSG_NOSIGNAL
#define MSG_NOSIGNAL 0                    /* macOS: SO_NOSIGPIPE on the socket instead */
#endif
#if defined(SIMULATOR) || defined(SLOPPY_NET_TEST)
int (*sl_net_req_fake)(struct sl_net_req *r);
#endif
struct nr_conn { int s; void *ssl; };
static int nr_send(struct nr_conn *c, const char *b, size_t n)
{
    while (n)
    {
        ssize_t w;
#ifndef NET_DEMO
        if (c->ssl) w = tls.write(c->ssl, b, (int)(n > 16384 ? 16384 : n));
        else
#endif
            w = send(c->s, b, n, MSG_NOSIGNAL);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) return -1;
        b += w;
        n -= (size_t)w;
    }
    return 0;
}
/* bytes, 0 at the end, -1 broken, -2 nothing for a second (the socket's timeout) */
static ssize_t nr_recv(struct nr_conn *c, char *b, size_t n)
{
    for (;;)
    {
#ifndef NET_DEMO
        if (c->ssl)
        {
            int r = tls.read(c->ssl, b, (int)n);
            if (r > 0) return r;
            int e = tls.get_error ? tls.get_error(c->ssl, r) : 5;
            if (e == 6) return 0;                         /* SSL_ERROR_ZERO_RETURN: closed cleanly */
            if (e == 2 || (e == 5 && (errno == EAGAIN || errno == EWOULDBLOCK))) return -2;
            if (e == 5 && errno == EINTR) continue;
            return r == 0 ? 0 : -1;
        }
#endif
        ssize_t r = recv(c->s, b, n, 0);
        if (r >= 0) return r;
        if (errno == EINTR) continue;
        return errno == EAGAIN || errno == EWOULDBLOCK ? -2 : -1;
    }
}
static void nr_close(struct nr_conn *c)
{
#ifndef NET_DEMO
    if (c->ssl) tls.ssl_free(c->ssl);
#endif
    c->ssl = NULL;
    if (c->s >= 0) close(c->s);
    c->s = -1;
}
/* "Wed, 28 Oct 2026 20:59:18 GMT" -> Unix seconds, 0 when it is not that */
static long long nr_date(const char *v)
{
    static const char mon[] = "JanFebMarAprMayJunJulAugSepOctNovDec";
    char m[4];
    int d, y, hh, mm, ss;
    const char *c = strchr(v, ',');
    if (!c || sscanf(c + 1, "%d %3s %d %d:%d:%d", &d, m, &y, &hh, &mm, &ss) != 6 || y < 1970) return 0;
    const char *at = strstr(mon, m);
    if (!at || (at - mon) % 3) return 0;
    int mo = (int)(at - mon) / 3;
    /* days since 1970 (no timegm on every C library) */
    static const int cum[12] = { 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334 };
    long long days = (long long)(y - 1970) * 365 + (y - 1969) / 4 - (y - 1901) / 100 + (y - 1601) / 400 + cum[mo] + d - 1;
    if (mo > 1 && ((y % 4 == 0 && y % 100) || y % 400 == 0)) days++;
    return days * 86400 + hh * 3600 + mm * 60 + ss;
}
/* the body as it comes: whole, by Content-Length, or chunked */
struct nr_body { bool chunked, in_trailer, refused; long long left, want; int crlf; char sz[20]; int szn; };
static bool nr_body_feed(struct sl_net_req *r, struct nr_body *b, const char *d, size_t n, bool *done)
{
    if (!b->chunked)
    {
        if (b->want >= 0 && (long long)n > b->left) n = (size_t)b->left;
        if (b->want >= 0) { b->left -= (long long)n; if (!b->left) *done = true; }
        if (n && r->sink && !r->sink(r->ctx, d, n)) { b->refused = true; return false; }
        return true;
    }
    while (n)
    {
        if (b->left > 0)
        {
            size_t k = (long long)n < b->left ? n : (size_t)b->left;
            if (r->sink && !r->sink(r->ctx, d, k)) { b->refused = true; return false; }
            d += k; n -= k; b->left -= (long long)k;
            if (!b->left) b->crlf = 2;
            continue;
        }
        char ch = *d++;
        n--;
        if (b->crlf) { if (ch == '\n') b->crlf = 0; continue; }   /* the line end after a chunk */
        if (b->in_trailer) { if (ch == '\n') { if (b->szn == 0) { *done = true; return true; } b->szn = 0; } else if (ch != '\r') b->szn++; continue; }
        if (ch == '\r') continue;
        if (ch != '\n') { if (b->szn + 1 < (int)sizeof b->sz) b->sz[b->szn++] = ch; continue; }
        b->sz[b->szn] = '\0';
        b->szn = 0;
        long long size = strtoll(b->sz, NULL, 16);
        if (size < 0) return false;
        if (!size) { b->in_trailer = true; continue; }
        b->left = size;
    }
    return true;
}
static int nr_connect(const char *host, const char *port, struct sl_net_req *r)
{
    struct addrinfo hints, *ai = NULL;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(host, port, &hints, &ai) || !ai) return -1;
    int s = -1;
    for (struct addrinfo *a = ai; a && s < 0 && !(r->stop && *r->stop); a = a->ai_next)
    {
        s = socket(a->ai_family, SOCK_STREAM, 0);
        if (s < 0) continue;
        fcntl(s, F_SETFD, FD_CLOEXEC);
        fcntl(s, F_SETFL, O_NONBLOCK);
        int c = connect(s, a->ai_addr, a->ai_addrlen), err = 0, ready = 0;
        struct pollfd pw = { s, POLLOUT, 0 };
        socklen_t el = sizeof err;
        for (int t = 0; c < 0 && (errno == EINPROGRESS || errno == EINTR) && t < 2 * (r->timeout_ms / 1000 + 1) && !ready && !(r->stop && *r->stop); t++)
            ready = poll(&pw, 1, 500) == 1;
        if (c < 0 && (!ready || getsockopt(s, SOL_SOCKET, SO_ERROR, &err, &el) || err)) { close(s); s = -1; continue; }
        fcntl(s, F_SETFL, 0);
    }
    freeaddrinfo(ai);
    if (s < 0) return -1;
    struct timeval tv = { 1, 0 };         /* a second at a time: a stop is heard */
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    struct timeval tw = { 20, 0 };
    setsockopt(s, SOL_SOCKET, SO_SNDTIMEO, &tw, sizeof tw);
#ifdef SO_NOSIGPIPE
    int one = 1;
    setsockopt(s, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
#endif
    return s;
}
int sl_net_http_req(struct sl_net_req *r)
{
    r->date = 0;
    r->https_failed = false;
#if defined(SIMULATOR) || defined(SLOPPY_NET_TEST)
    if (sl_net_req_fake) return sl_net_req_fake(r);
#endif
    char at[1024];
    if (snprintf(at, sizeof at, "%s", r->url) >= (int)sizeof at) return -1;
    char first_host[200] = "";
    for (int hop = 0; hop < 4; hop++)
    {
        if (r->stop && *r->stop) return -1;
        bool secure = !strncasecmp(at, "https://", 8);
        if (!secure && strncasecmp(at, "http://", 7)) return -1;
        char host[200], port[8], hosthdr[210];
        snprintf(port, sizeof port, secure ? "443" : "80");
        const char *h = at + (secure ? 8 : 7), *slash = strchr(h, '/');
        size_t hl = slash ? (size_t)(slash - h) : strlen(h);
        if (!hl || hl >= sizeof host) return -1;
        memcpy(host, h, hl);
        host[hl] = '\0';
        snprintf(hosthdr, sizeof hosthdr, "%s", host);
        char *colon = strrchr(host, ':');
        if (colon && !strchr(colon, ']')) { snprintf(port, sizeof port, "%s", colon + 1); *colon = '\0'; }
        if (host[0] == '[') { memmove(host, host + 1, strlen(host)); char *e = strchr(host, ']'); if (e) *e = '\0'; }
        /* the sign-in goes nowhere but where it was meant for */
        if (!first_host[0]) snprintf(first_host, sizeof first_host, "%s", host);
        else if (strcasecmp(first_host, host)) return 310;
        const char *path = slash ? slash : "/";
        struct nr_conn c = { -1, NULL };
#ifdef NET_DEMO
        if (secure) { r->https_failed = true; return -1; }
#else
        if (secure && !tls_load()) { r->https_failed = true; return -1; }
#endif
        c.s = nr_connect(host, port, r);
        if (c.s < 0) return -1;
#ifndef NET_DEMO
        if (secure)
        {
            void *ssl = tls.ssl_new(tls.ctx);
            if (ssl && tls.set_fd(ssl, c.s) == 1)
            {
                tls.ctrl(ssl, 55, 0, host);   /* SSL_set_tlsext_host_name */
                struct timeval tv = { 20, 0 };
                setsockopt(c.s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
                if (tls.connect(ssl) == 1) c.ssl = ssl;
                struct timeval t1 = { 1, 0 };
                setsockopt(c.s, SOL_SOCKET, SO_RCVTIMEO, &t1, sizeof t1);
            }
            if (!c.ssl) { if (ssl) tls.ssl_free(ssl); nr_close(&c); r->https_failed = true; return -1; }
        }
#endif
        size_t blen = r->body ? strlen(r->body) : 0;
        char head[2048];
        int n = snprintf(head, sizeof head, "%s %s HTTP/1.1\r\nHost: %s\r\nUser-Agent: %s\r\nAccept: application/json, */*\r\n"
                         "Accept-Encoding: identity\r\nConnection: close\r\n%s", r->method ? r->method : "GET", path, hosthdr,
                         r->ua ? r->ua : "GabagoolOS", r->headers ? r->headers : "");
        if (r->body && n > 0 && n < (int)sizeof head)
            n += snprintf(head + n, sizeof head - (size_t)n, "Content-Type: %s\r\nContent-Length: %zu\r\n",
                          r->ctype ? r->ctype : "application/json", blen);
        if (n > 0 && n < (int)sizeof head) n += snprintf(head + n, sizeof head - (size_t)n, "\r\n");
        bool sent = n > 0 && n < (int)sizeof head && !nr_send(&c, head, (size_t)n) && (!blen || !nr_send(&c, r->body, blen));
        memset(head, 0, sizeof head);     /* it held the token */
        if (!sent) { nr_close(&c); return -1; }
        /* the head of the answer, then the body as it comes */
        char buf[4096], hd[4096];
        size_t got = 0;
        int quiet = 0, status = 0;
        ssize_t k = 0;
        char *end = NULL;
        while (!end)
        {
            if (r->stop && *r->stop) { nr_close(&c); return -1; }
            k = nr_recv(&c, hd + got, sizeof hd - 1 - got);
            if (k == -2) { if (++quiet * 1000 >= r->timeout_ms) break; continue; }
            if (k <= 0) break;
            quiet = 0;
            got += (size_t)k;
            hd[got] = '\0';
            end = strstr(hd, "\r\n\r\n");
            if (!end && got + 1 >= sizeof hd) break;
        }
        if (!end) { nr_close(&c); return -1; }
        *end = '\0';
        size_t body_at = (size_t)(end + 4 - hd);
        status = !strncmp(hd, "HTTP/1.", 7) ? atoi(hd + 9) : 0;
        struct nr_body b;
        memset(&b, 0, sizeof b);
        b.want = -1;
        char loc[600] = "";
        for (char *l = strstr(hd, "\r\n"); l; l = strstr(l + 2, "\r\n"))
        {
            const char *v = l + 2;
            if (!strncasecmp(v, "Content-Length:", 15)) b.want = b.left = atoll(v + 15);
            else if (!strncasecmp(v, "Transfer-Encoding:", 18) && strcasestr(v, "chunked") && strcasestr(v, "chunked") < (strstr(v, "\r\n") ? strstr(v, "\r\n") : v + strlen(v))) b.chunked = true;
            else if (!strncasecmp(v, "Date:", 5)) r->date = nr_date(v + 5);
            else if (!strncasecmp(v, "Location:", 9))
            {
                const char *s = v + 9;
                while (*s == ' ') s++;
                snprintf(loc, sizeof loc, "%.*s", (int)strcspn(s, "\r\n"), s);
            }
        }
        if (b.chunked) b.want = -1;
        if ((status == 301 || status == 302 || status == 303 || status == 307 || status == 308) && loc[0])
        {
            nr_close(&c);
            char next[1024];
            if (!strncasecmp(loc, "http://", 7) || !strncasecmp(loc, "https://", 8)) snprintf(next, sizeof next, "%s", loc);
            else if (loc[0] == '/') snprintf(next, sizeof next, "%.*s%s", (int)(h - at + hl), at, loc);
            else return status;
            snprintf(at, sizeof at, "%s", next);
            continue;
        }
        bool done = !b.chunked && b.want == 0, ok = true;
        if (!done && got > body_at) ok = nr_body_feed(r, &b, hd + body_at, got - body_at, &done);
        quiet = 0;
        while (ok && !done)
        {
            if (r->stop && *r->stop) { nr_close(&c); return -1; }
            k = nr_recv(&c, buf, sizeof buf);
            if (k == -2) { if (++quiet * 1000 >= r->timeout_ms) { ok = false; break; } continue; }
            if (k < 0) { ok = false; break; }
            if (k == 0) { if (b.chunked || b.want > 0) ok = false; break; }   /* the end, early or not */
            quiet = 0;
            ok = nr_body_feed(r, &b, buf, (size_t)k, &done);
        }
        nr_close(&c);
        if (!ok && !b.refused) return -1;   /* cut off; a sink that had enough is not an error */
        return status ? status : -1;
    }
    return -1;
}

/* the first line of wget's report that says what went wrong */
static void scr_reason(const char *out, char *r, size_t n)
{
    snprintf(r, n, "no answer");
    for (const char *s = out; *s; )
    {
        size_t len = strcspn(s, "\n");
        if (len && strncmp(s, "note:", 5) && strncmp(s, "  ", 2))
        {
            snprintf(r, n, "%.*s", (int)(len < 80 ? len : 80), s);
            return;
        }
        s += len + (s[len] == '\n');
    }
}

static void scr_validate(void)
{
    static char out[2048];
    char user[48] = "";
    uint32_t t0 = net_ms();
    int status = scr_http(SCR_API "validate-token", NULL, out, sizeof out);
    int result = status == 200 && sl_scrob_json_true(out, "valid") ? SL_SCROB_GOOD :
                 status == 200 || status == 401 ? SL_SCROB_BAD : SL_SCROB_NO_ANSWER;
    if (result == SL_SCROB_GOOD) sl_scrob_json_text(out, "user_name", user, sizeof user);
    if (result == SL_SCROB_NO_ANSWER) { char why[96]; scr_reason(out, why, sizeof why);
        scr_say("token check: no answer (HTTP %d, %s)", status, why); }
    else scr_say("token check: %s (HTTP %d, %u ms)", result == SL_SCROB_GOOD ? "valid" : "token invalid",
                 status, (unsigned)(net_ms() - t0));
    if (result != SL_SCROB_NO_ANSWER) sw.token_bad = result == SL_SCROB_BAD;
    if (result == SL_SCROB_GOOD) { sw.next_ms = net_ms(); sw.fail_said = false; }
    pthread_mutex_lock(&scr_lock);
    scr.st.test = result;
    snprintf(scr.st.user, sizeof scr.st.user, "%s", user);
    snprintf(scr.st.error, sizeof scr.st.error, "%s", result == SL_SCROB_BAD ? "ListenBrainz did not accept the token" :
             result == SL_SCROB_NO_ANSWER ? "ListenBrainz did not answer" : "");
    scr.st.test_seq++;
    pthread_mutex_unlock(&scr_lock);
}

static void scr_playing_now(const struct sl_listen *l)
{
    static char body[2048], out[1024];
    if (!sl_scrob_json(body, sizeof body, "playing_now", l, 1)) return;
    uint32_t t0 = net_ms();
    int status = scr_http(SCR_API "submit-listens", body, out, sizeof out);
    scr_say("playing now sent (HTTP %d, %u ms)", status, (unsigned)(net_ms() - t0));
    if (status == 401) { sw.token_bad = true; scr_error("ListenBrainz did not accept the token", true); }
}

/* One request with the oldest listens; only what ListenBrainz accepted
 * leaves the queue. It refuses a whole request for one bad listen, so
 * after a 400 they go one at a time until the bad one is found and
 * dropped. */
static void scr_submit(void)
{
    static struct sl_listen l[SCR_BATCH];
    static char body[SCR_BATCH * 1200], out[2048];
    pthread_mutex_lock(&scr_files);
    int n = scr.hold ? 0 : scr_read(SCR_QUEUE, &sw.queued, l, sw.split ? 1 : SCR_BATCH);
    if (!n && !scr.hold) sw.queued = scr_count_lines(SCR_QUEUE);   /* nothing readable after all */
    pthread_mutex_unlock(&scr_files);
    if (!n) { sw.next_ms = net_ms() + 60000; return; }    /* a card that will not read: not in a loop */
    size_t len;
    while (!(len = sl_scrob_json(body, sizeof body, n > 1 ? "import" : "single", l, n)) && n > 1) n--;
    if (!len) n = 1;                       /* cannot happen: one listen always fits */
    uint32_t t0 = net_ms();
    int status = len ? scr_http(SCR_API "submit-listens", body, out, sizeof out) : 400;
    unsigned ms = (unsigned)(net_ms() - t0);
    int drop = 0;
    if (status >= 200 && status < 300)
    {
        drop = n;
        sw.failures = 0;
        if (sw.split) sw.split--;
        scr_say("batch sent: %d listen%s (HTTP %d, %u ms)", n, n == 1 ? "" : "s", status, ms);
        pthread_mutex_lock(&scr_lock);
        scr.st.sent += n;
        scr.st.last_sent = (uint32_t)time(NULL);
        scr.st.error[0] = '\0';
        pthread_mutex_unlock(&scr_lock);
        sw.fail_said = false;
    }
    else if (status == 401)
    {
        sw.token_bad = true;
        scr_say("token invalid (HTTP 401): sending stops until a new token is saved");
        scr_error("ListenBrainz did not accept the token", true);
    }
    else if (status == 400 && n > 1)
    {
        sw.split = n;
        scr_say("batch of %d refused (HTTP 400, %u ms): sending one at a time", n, ms);
    }
    else if (status == 400)
    {
        drop = 1;
        sw.split = 0;
        scr_say("listen refused (HTTP 400), dropped: %.40s - %.40s", l[0].artist, l[0].title);
    }
    else
    {
        /* no answer, a server error or too many requests: later, then less often */
        char why[96];
        scr_reason(out, why, sizeof why);
        sw.failures++;
        uint32_t wait = status == 429 ? 60 : sl_scrob_backoff(sw.failures);
        sw.next_ms = net_ms() + wait * 1000u;
        if (status > 0) scr_say("batch failed (HTTP %d, %u ms), backoff %u s", status, ms, (unsigned)wait);
        else scr_say("batch failed (%s), backoff %u s", why, (unsigned)wait);
        /* five in a row is over an hour of trying: say so once */
        bool tell = sw.failures >= 5 && !sw.fail_said;
        if (tell) sw.fail_said = true;
        scr_error(status > 0 ? "ListenBrainz is having trouble" : "ListenBrainz did not answer", tell);
    }
    if (drop)
    {
        pthread_mutex_lock(&scr_files);
        if (!scr.hold && !scr_drop(SCR_QUEUE, drop, &sw.queued))
        {
            scr_say("could not take sent listens off the queue");
            sw.next_ms = net_ms() + 60000;
        }
        pthread_mutex_unlock(&scr_files);
    }
}

/* ---- Last.fm: its own queue and session, the same worker */
static bool lfm_save_pending;            /* a sign-in came during USB mode: saved once it is over */
static bool lfm_keyed(void) { return sl_lastfm_key[0] && sl_lastfm_secret[0] && !sw.lfm_key_refused; }
static void lfm_set_auth(int state, const char *error, const char *url)
{
    pthread_mutex_lock(&scr_lock);
    scr.st.lfm_auth = state;
    if (error) snprintf(scr.st.lfm_error, sizeof scr.st.lfm_error, "%s", error);
    snprintf(scr.st.lfm_url, sizeof scr.st.lfm_url, "%s", url ? url : "");
    scr.st.lfm_auth_seq++;
    pthread_mutex_unlock(&scr_lock);
}
static void lfm_error(const char *e, bool tell)
{
    pthread_mutex_lock(&scr_lock);
    snprintf(scr.st.lfm_error, sizeof scr.st.lfm_error, "%s", e);
    if (tell) scr.st.lfm_fail_seq++;
    pthread_mutex_unlock(&scr_lock);
}
/* The keys file: "GBK1", then "lastfm\t<key>\t<secret>\n" scrambled by
 * the xorshift stream below (make-keys.py does the same). Read at each
 * load of the files until a key is in; with scr_files held. */
static void lfm_keys_load(void)
{
    static char key[64], secret[64];
    if (sl_lastfm_key[0]) return;
    char p[256];
    unsigned char b[200];
    int fd = scr_path(p, sizeof p, SCR_KEYS) ? open(p, O_RDONLY) : -1;
    if (fd < 0) return;
    ssize_t r = read(fd, b, sizeof b - 1);
    close(fd);
    if (r < 8 || memcmp(b, "GBK1", 4)) { scr_say("keys file is not one, ignored"); return; }
    uint32_t x = 0x9e3779b9u;
    for (ssize_t i = 4; i < r; i++)
    {
        x ^= x << 13; x ^= x >> 17; x ^= x << 5;
        b[i] ^= (unsigned char)x;
    }
    b[r] = '\0';
    char *line = (char *)b + 4, *k, *sec;
    line[strcspn(line, "\r\n")] = '\0';
    if (!strncmp(line, "lastfm\t", 7) && (k = line + 7, sec = strchr(k, '\t')) && sec - k < (long)sizeof key
        && strlen(sec + 1) < sizeof secret && sec > k && sec[1])
    {
        *sec++ = '\0';
        snprintf(key, sizeof key, "%s", k);
        snprintf(secret, sizeof secret, "%s", sec);
        sl_lastfm_key = key; sl_lastfm_secret = secret;
    }
    else scr_say("keys file has no Last.fm key, ignored");
    memset(b, 0, sizeof b);
}
/* the session on the card: its name, a tab, the key; with scr_files held */
static void lfm_session_load(void)
{
    char p[256], b[160] = "";
    sw.lfm_sk[0] = sw.lfm_name[0] = '\0';
    int fd = scr_path(p, sizeof p, SCR_LFM_SESSION) ? open(p, O_RDONLY) : -1;
    if (fd < 0) return;
    ssize_t r = read(fd, b, sizeof b - 1);
    close(fd);
    b[r > 0 ? r : 0] = '\0';
    char *tab = strchr(b, '\t');
    if (tab)
    {
        *tab = '\0';
        tab[1 + strcspn(tab + 1, " \t\r\n")] = '\0';
        if (strlen(tab + 1) > 8 && strlen(tab + 1) < sizeof sw.lfm_sk)
        {
            snprintf(sw.lfm_name, sizeof sw.lfm_name, "%s", b);
            snprintf(sw.lfm_sk, sizeof sw.lfm_sk, "%s", tab + 1);
        }
    }
    if (!sw.lfm_sk[0]) scr_say("Last.fm session file is not a session, ignored");
    memset(b, 0, sizeof b);
}
static bool lfm_session_write(void)
{
    char p[256], b[128];
    if (!scr_path(p, sizeof p, SCR_LFM_SESSION)) return false;
    if (!sw.lfm_sk[0]) { unlink(p); return true; }
    int n = snprintf(b, sizeof b, "%s\t%s\n", sw.lfm_name, sw.lfm_sk);
    char tmp[260];                       /* written aside, then renamed: a power cut keeps the old one */
    snprintf(tmp, sizeof tmp, "%s.tmp", p);
    int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    bool ok = fd >= 0 && write(fd, b, (size_t)n) == n && fsync(fd) == 0;
    if (fd >= 0 && close(fd)) ok = false;
    memset(b, 0, sizeof b);
    if (ok) ok = rename(tmp, p) == 0;
    if (!ok) unlink(tmp);
    return ok;
}
static void lfm_session_save(void)
{
    pthread_mutex_lock(&scr_files);
    if (scr.hold) lfm_save_pending = true;
    else { scr_say(lfm_session_write() ? "Last.fm session saved" : "could not save the Last.fm session"); lfm_save_pending = false; }
    pthread_mutex_unlock(&scr_files);
}
/* One signed call; *err gets Last.fm's error code (0 none). The form
 * carries the session or a password: it is wiped after. */
static int lfm_call(struct sl_lfm_param *p, int n, char *out, size_t cap, int *err)
{
    static char body[SL_LFM_BATCH * 1500 + 512];
    char sig[33];
    sl_lfm_sign(p, n, sl_lastfm_secret, sig);
    size_t len = sl_lfm_body(body, sizeof body, p, n, sig);
    *err = 0;
    if (!len) return 413;
    int status = scr_http_as(SL_LFM_API, body, out, cap, false);
    memset(body, 0, len);
    *err = sl_lfm_error(out);
    return status;
}
/* Last.fm let the session go (the owner took the player off the account):
 * said once, loudly; what waits keeps waiting for a new sign-in */
static void lfm_lost_now(void)
{
    if (!sw.lfm_lost) scr_say("Last.fm session refused (error 9): sending stops until a new sign-in, %d waiting", sw.lfm_queued);
    sw.lfm_lost = true;
    lfm_error("Last.fm signed this player out", true);
}
static void lfm_signed_in(const char *out, const char *how)
{
    char name[64] = "", sk[40] = "";
    sl_scrob_json_text(out, "name", name, sizeof name);
    sl_scrob_json_text(out, "key", sk, sizeof sk);
    if (strlen(sk) < 8) { lfm_set_auth(SL_LFM_AUTH_FAILED, "Last.fm sent no session", NULL); return; }
    snprintf(sw.lfm_name, sizeof sw.lfm_name, "%s", name);
    snprintf(sw.lfm_sk, sizeof sw.lfm_sk, "%s", sk);
    memset(sk, 0, sizeof sk);
    sw.lfm_lost = sw.lfm_fail_said = false;
    sw.lfm_failures = 0;
    sw.lfm_next_ms = net_ms();
    sw.lfm_token[0] = '\0';
    lfm_session_save();
    scr_say("Last.fm: signed in %s", how);
    lfm_error("", false);
    lfm_set_auth(SL_LFM_AUTH_OK, "", NULL);
}
/* a phone sign-in: a token, shown as a QR code the phone opens */
static void lfm_get_token(void)
{
    static char out[2048];
    struct sl_lfm_param p[] = { { "method", "auth.getToken" }, { "api_key", sl_lastfm_key } };
    int err, status = lfm_call(p, 2, out, sizeof out, &err);
    char tok[40] = "";
    if (status == 200 && !err && sl_scrob_json_text(out, "token", tok, sizeof tok) && strlen(tok) >= 8)
    {
        char url[160];
        snprintf(sw.lfm_token, sizeof sw.lfm_token, "%s", tok);
        sw.lfm_token_until = net_ms() + LFM_TOKEN_MS;
        sw.lfm_poll_ms = net_ms() + sl_lastfm_poll_ms;
        sl_lfm_auth_url(url, sizeof url, sl_lastfm_key, tok);
        scr_say("Last.fm: waiting for the phone sign-in");
        lfm_set_auth(SL_LFM_AUTH_WAIT, "", url);
        return;
    }
    if (err == SL_LFM_E_KEY || err == SL_LFM_E_SUSPENDED) sw.lfm_key_refused = true;
    scr_say("Last.fm: no sign-in token (HTTP %d, error %d)", status, err);
    lfm_set_auth(SL_LFM_AUTH_FAILED, sw.lfm_key_refused ? "Last.fm turned this player's key away" : "Last.fm did not answer", NULL);
}
/* has the phone let the player in yet */
static void lfm_poll_session(void)
{
    static char out[2048];
    struct sl_lfm_param p[] = { { "method", "auth.getSession" }, { "api_key", sl_lastfm_key }, { "token", sw.lfm_token } };
    int err, status = lfm_call(p, 3, out, sizeof out, &err);
    if (status == 200 && !err) { lfm_signed_in(out, "from a phone"); return; }
    bool waiting = err == SL_LFM_E_UNAUTHORISED_TOKEN || (!err && (status == 403 || status <= 0 || status >= 500));
    if (waiting && (int32_t)(net_ms() - sw.lfm_token_until) < 0) { sw.lfm_poll_ms = net_ms() + sl_lastfm_poll_ms; return; }
    sw.lfm_token[0] = '\0';
    scr_say("Last.fm: phone sign-in ended (HTTP %d, error %d)", status, err);
    lfm_set_auth(SL_LFM_AUTH_FAILED, waiting || err == SL_LFM_E_TOKEN_EXPIRED ? "The sign-in ran out of time" : "Last.fm did not answer", NULL);
}
static void lfm_password(const char *user, const char *pass)
{
    static char out[2048];
    struct sl_lfm_param p[] = { { "method", "auth.getMobileSession" }, { "api_key", sl_lastfm_key },
                                { "username", user }, { "password", pass } };
    int err, status = lfm_call(p, 4, out, sizeof out, &err);
    for (char *t = pass[0] ? strstr(out, pass) : NULL; t; t = strstr(t, pass)) memset(t, '*', strlen(pass));
    if (status == 200 && !err) { lfm_signed_in(out, "with a password"); return; }
    scr_say("Last.fm: password sign-in refused (HTTP %d, error %d)", status, err);
    lfm_set_auth(SL_LFM_AUTH_FAILED, err == SL_LFM_E_AUTH || (!err && status >= 400 && status < 500) ?
                 "Last.fm did not accept that name and password" : "Last.fm did not answer", NULL);
}
/* a listen's tags as parameters; num keeps its numbers */
static int lfm_track_params(struct sl_lfm_param *p, const struct sl_listen *l, int i, char num[3][16], bool when)
{
    int n = 0;
    char idx[8] = "";
    if (i >= 0) snprintf(idx, sizeof idx, "[%d]", i);
    snprintf(p[n].k, sizeof p[n].k, "artist%s", idx); p[n++].v = l->artist;
    snprintf(p[n].k, sizeof p[n].k, "track%s", idx); p[n++].v = l->title;
    if (when) { snprintf(num[0], 16, "%lu", (unsigned long)l->when); snprintf(p[n].k, sizeof p[n].k, "timestamp%s", idx); p[n++].v = num[0]; }
    if (l->album[0]) { snprintf(p[n].k, sizeof p[n].k, "album%s", idx); p[n++].v = l->album; }
    if (l->track > 0) { snprintf(num[1], 16, "%d", l->track); snprintf(p[n].k, sizeof p[n].k, "trackNumber%s", idx); p[n++].v = num[1]; }
    if (l->secs) { snprintf(num[2], 16, "%lu", (unsigned long)l->secs); snprintf(p[n].k, sizeof p[n].k, "duration%s", idx); p[n++].v = num[2]; }
    if (l->mbid[0]) { snprintf(p[n].k, sizeof p[n].k, "mbid%s", idx); p[n++].v = l->mbid; }
    return n;
}
static void lfm_playing_now(const struct sl_listen *l)
{
    static char out[2048];
    struct sl_lfm_param p[12] = { { "method", "track.updateNowPlaying" }, { "api_key", sl_lastfm_key }, { "sk", sw.lfm_sk } };
    char num[3][16];
    int n = 3 + lfm_track_params(p + 3, l, -1, num, false), err;
    uint32_t t0 = net_ms();
    int status = lfm_call(p, n, out, sizeof out, &err);
    scr_say("Last.fm playing now sent (HTTP %d, %u ms)", status, (unsigned)(net_ms() - t0));
    if (err == SL_LFM_E_SESSION || (!err && status == 403)) lfm_lost_now();
}
/* the oldest listens in one request; what Last.fm took or let go of
 * leaves the queue, the rest waits */
static void lfm_submit(void)
{
    static struct sl_listen l[SL_LFM_BATCH];
    static struct sl_lfm_param p[SL_LFM_PARAMS];
    static char num[SL_LFM_BATCH][3][16], out[4096];
    static int split;
    pthread_mutex_lock(&scr_files);
    int n = scr.hold ? 0 : scr_read(SCR_LFM_QUEUE, &sw.lfm_queued, l, split ? 1 : SL_LFM_BATCH);
    if (!n && !scr.hold) sw.lfm_queued = scr_count_lines(SCR_LFM_QUEUE);
    pthread_mutex_unlock(&scr_files);
    if (!n) { sw.lfm_next_ms = net_ms() + 60000; return; }
    int k = 0, err;
    p[k] = (struct sl_lfm_param){ "method", "track.scrobble" }; k++;
    p[k] = (struct sl_lfm_param){ "api_key", sl_lastfm_key }; k++;
    p[k] = (struct sl_lfm_param){ "sk", sw.lfm_sk }; k++;
    for (int i = 0; i < n; i++) k += lfm_track_params(p + k, &l[i], i, num[i], true);
    uint32_t t0 = net_ms();
    int status = lfm_call(p, k, out, sizeof out, &err);
    unsigned ms = (unsigned)(net_ms() - t0);
    int accepted = 0, ignored = 0, drop = 0;
    if (status == 200 && !err && sl_lfm_counts(out, &accepted, &ignored))
    {
        drop = n;
        sw.lfm_failures = 0;
        if (split) split--;
        scr_say("Last.fm: %d scrobbled, %d ignored (HTTP %d, %u ms)", accepted, ignored, status, ms);
        pthread_mutex_lock(&scr_lock);
        scr.st.lfm_sent += accepted;
        scr.st.lfm_last_sent = (uint32_t)time(NULL);
        scr.st.lfm_error[0] = '\0';
        pthread_mutex_unlock(&scr_lock);
        sw.lfm_fail_said = false;
    }
    else if (err == SL_LFM_E_SESSION || (!err && status == 403)) lfm_lost_now();
    else if (err == SL_LFM_E_KEY || err == SL_LFM_E_SUSPENDED)
    {
        sw.lfm_key_refused = true;
        scr_say("Last.fm refused the API key (error %d): Last.fm sending stops", err);
        lfm_error("Last.fm turned this player's key away", true);
    }
    else if (err == 6 && n > 1) { split = n; scr_say("Last.fm refused a batch of %d (error 6): one at a time", n); }
    else if (err == 6) { drop = 1; split = 0; scr_say("Last.fm refused a listen (error 6), dropped: %.40s - %.40s", l[0].artist, l[0].title); }
    else
    {
        sw.lfm_failures++;
        uint32_t wait = err == SL_LFM_E_RATE ? 300 : sl_scrob_backoff(sw.lfm_failures);
        sw.lfm_next_ms = net_ms() + wait * 1000u;
        scr_say("Last.fm batch failed (HTTP %d, error %d, %u ms), backoff %u s", status, err, ms, (unsigned)wait);
        bool tell = sw.lfm_failures >= 5 && !sw.lfm_fail_said;
        if (tell) sw.lfm_fail_said = true;
        lfm_error(status > 0 ? "Last.fm is having trouble" : "Last.fm did not answer", tell);
    }
    if (drop)
    {
        pthread_mutex_lock(&scr_files);
        if (!scr.hold && !scr_drop(SCR_LFM_QUEUE, drop, &sw.lfm_queued))
        {
            scr_say("could not take sent listens off the Last.fm queue");
            sw.lfm_next_ms = net_ms() + 60000;
        }
        pthread_mutex_unlock(&scr_files);
    }
}
static bool lfm_ready(void) { return lfm_keyed() && sw.lfm_sk[0] && !sw.lfm_lost; }

/* ---- the worker */
static void scr_pass(void)
{
    struct sl_listen in[SCR_INBOX], now;
    char token[64];
    pthread_mutex_lock(&scr_lock);
    int n = scr.n_inbox;
    memcpy(in, scr.inbox, sizeof in[0] * (size_t)n);
    scr.n_inbox = 0;
    scr.writing = n;
    bool lb = scr.lb_on, log = scr.log_on, online = scr.online, test = scr.test, reload = scr.reload;
    bool token_new = scr.token_new, now_pending = scr.now_pending && net_ms() - scr.now_ms < 5 * 60 * 1000u;
    now = scr.now;
    memcpy(token, scr.token, sizeof token);
    memset(scr.token, 0, sizeof scr.token);
    bool retry = scr.retry;
    bool lfm = scr.lfm_on;
    int lfm_req = scr.lfm_req;
    char lfm_user[64], lfm_pass[128];
    memcpy(lfm_user, scr.lfm_user, sizeof lfm_user);
    memcpy(lfm_pass, scr.lfm_pass, sizeof lfm_pass);
    memset(scr.lfm_pass, 0, sizeof scr.lfm_pass);
    scr.lfm_req = LFM_REQ_NONE;
    scr.test = scr.token_new = scr.now_pending = scr.kick = scr.retry = false;
    pthread_mutex_unlock(&scr_lock);

    if (retry) { sw.next_ms = sw.lfm_next_ms = net_ms(); sw.waiting_said = false; }
    pthread_mutex_lock(&scr_files);
    if (!scr.hold)
    {
        if (!sw.loaded || reload)
        {
            char p[256];
            if (scr_path(p, sizeof p, SL_CAST_DIR)) mkdir(p, 0777);
            if (!token_new) scr_token_load();
            sw.queued = scr_count_lines(SCR_QUEUE);
            sw.lfm_queued = scr_count_lines(SCR_LFM_QUEUE);
            lfm_keys_load();
            lfm_session_load();
            if (!sw.loaded || reload) scr_say("%d listen%s waiting, token %s", sw.queued, sw.queued == 1 ? "" : "s",
                                              sw.token[0] || token_new ? "set" : "not set");
            sw.loaded = true;
            pthread_mutex_lock(&scr_lock);
            scr.reload = false;
            pthread_mutex_unlock(&scr_lock);
        }
        if (token_new)
        {
            memcpy(sw.token, token, sizeof sw.token);
            sw.token_bad = false;
            sw.fail_said = false;
            sw.next_ms = net_ms();
            scr_token_save(sw.token);
        }
        for (int i = 0; i < n; i++)
        {
            char line[SCR_LINE];
            if (log && sl_scrob_log_line(line, sizeof line, &in[i]))
            {
                if (scr_append(SCR_LOG, SL_SCROB_LOG_HEADER, line)) scr_say("listen logged to .scrobbler.log");
                else scr_say("could not write .scrobbler.log");
            }
            if (lb && sl_scrob_queue_line(line, sizeof line, &in[i]))
            {
                if (scr_append(SCR_QUEUE, NULL, line)) sw.queued++;
                if (sw.queued) scr_say("listen queued (%d waiting)", sw.queued);
            }
            /* Last.fm keeps its own, signed in or not: a sign-in later sends them */
            if (lfm && sl_scrob_queue_line(line, sizeof line, &in[i]) && scr_append(SCR_LFM_QUEUE, NULL, line))
                scr_say("Last.fm listen queued (%d waiting)", ++sw.lfm_queued);
        }
        if (sw.lfm_queued > SCR_CAP)
        {
            int over = sw.lfm_queued - SCR_CAP;
            if (scr_drop(SCR_LFM_QUEUE, over, &sw.lfm_queued)) scr_say("Last.fm queue full: dropped the %d oldest", over);
        }
        if (lfm_req == LFM_REQ_SIGNOUT)
        {
            sw.lfm_sk[0] = sw.lfm_name[0] = sw.lfm_token[0] = '\0';
            sw.lfm_lost = false;
            scr_say(lfm_session_write() ? "Last.fm: signed out" : "Last.fm: could not remove the session file");
            lfm_error("", false);
        }
        if (lfm_save_pending) { lfm_session_write(); lfm_save_pending = false; }
        if (sw.queued > SCR_CAP)
        {
            int over = sw.queued - SCR_CAP;
            if (scr_drop(SCR_QUEUE, over, &sw.queued)) scr_say("queue full: dropped the %d oldest listen%s", over, over == 1 ? "" : "s");
        }
    }
    else
    {
        /* USB mode came first: they go back for later */
        pthread_mutex_lock(&scr_lock);
        int room = SCR_INBOX - scr.n_inbox, keep = n < room ? n : room;
        memmove(&scr.inbox[keep], scr.inbox, sizeof scr.inbox[0] * (size_t)scr.n_inbox);
        memcpy(scr.inbox, in, sizeof in[0] * (size_t)keep);
        scr.n_inbox += keep;
        if (token_new && !scr.token_new) { memcpy(scr.token, token, sizeof scr.token); scr.token_new = true; }
        pthread_mutex_unlock(&scr_lock);
    }
    pthread_mutex_unlock(&scr_files);
    memset(token, 0, sizeof token);
    pthread_mutex_lock(&scr_lock);
    scr.writing = 0;
    pthread_mutex_unlock(&scr_lock);

    bool ready = lb && sw.loaded && sw.token[0];
    if (test)
    {
        if (!sw.token[0]) scr_say("token check: no token");
        else if (!online)
        {
            scr_say("token check: Wi-Fi is not connected");
            pthread_mutex_lock(&scr_lock);
            scr.st.test = SL_SCROB_NO_ANSWER;
            snprintf(scr.st.error, sizeof scr.st.error, "Join a Wi-Fi network first");
            scr.st.test_seq++;
            pthread_mutex_unlock(&scr_lock);
        }
        else scr_validate();
    }
    if (ready && online && !sw.token_bad && now_pending) scr_playing_now(&now);
    /* Last.fm: a sign-in asked for, one waiting on a phone, what plays, what waits */
    if (lfm_req == LFM_REQ_CANCEL) { sw.lfm_token[0] = '\0'; lfm_set_auth(SL_LFM_AUTH_IDLE, NULL, NULL); }
    if (lfm_req == LFM_REQ_SIGNOUT) lfm_set_auth(SL_LFM_AUTH_IDLE, NULL, NULL);
    if (lfm_req == LFM_REQ_PHONE || lfm_req == LFM_REQ_PASSWORD)
    {
        if (!lfm_keyed()) lfm_set_auth(SL_LFM_AUTH_FAILED, "This build has no Last.fm key", NULL);
        else if (!online) lfm_set_auth(SL_LFM_AUTH_FAILED, "Join a Wi-Fi network first", NULL);
        else if (lfm_req == LFM_REQ_PHONE) lfm_get_token();
        else lfm_password(lfm_user, lfm_pass);
    }
    memset(lfm_pass, 0, sizeof lfm_pass);
    if (sw.lfm_token[0] && online && (int32_t)(net_ms() - sw.lfm_poll_ms) >= 0) lfm_poll_session();
    if (lfm && lfm_ready() && online && now_pending && now.artist[0]) lfm_playing_now(&now);
    if (lfm && lfm_ready() && online && sw.lfm_queued && (int32_t)(net_ms() - sw.lfm_next_ms) >= 0) lfm_submit();
    if (ready && !sw.token_bad && sw.queued)
    {
        if (!online)
        {
            if (!sw.waiting_said) scr_say("Wi-Fi down, %d listen%s waiting", sw.queued, sw.queued == 1 ? "" : "s");
            sw.waiting_said = true;
        }
        else if ((int32_t)(net_ms() - sw.next_ms) >= 0)
        {
            sw.waiting_said = false;
            scr_submit();
        }
    }
    pthread_mutex_lock(&scr_lock);
    scr.st.queued = sw.queued;
    scr.st.has_token = sw.token[0] != '\0';
    scr.st.token_bad = sw.token_bad;
    scr.st.lfm = !sw.lfm_sk[0] ? SL_LFM_OUT : sw.lfm_lost ? SL_LFM_LOST : SL_LFM_IN;
    scr.st.lfm_queued = sw.lfm_queued;
    scr.st.lfm_keyless = !sl_lastfm_key[0] || !sl_lastfm_secret[0];
    snprintf(scr.st.lfm_user, sizeof scr.st.lfm_user, "%s", sw.lfm_name);
    pthread_mutex_unlock(&scr_lock);
}

/* Is there something to do now? Else how long until there may be. */
static bool scr_due(uint32_t *wait_ms)
{
    *wait_ms = 60000;
    if (scr.hold) return false;           /* USB mode: sl_net_scrobble_hold(false) wakes it */
    if (scr.n_inbox || scr.now_pending || scr.test || scr.token_new || scr.reload || scr.kick || scr.retry || scr.lfm_req) return true;
    uint32_t at[3];
    int n = 0;
    if (scr.lb_on && scr.online && sw.token[0] && !sw.token_bad && sw.queued) at[n++] = sw.next_ms;
    if (scr.lfm_on && scr.online && lfm_ready() && sw.lfm_queued) at[n++] = sw.lfm_next_ms;
    if (sw.lfm_token[0] && scr.online) at[n++] = sw.lfm_poll_ms;   /* a phone sign-in being waited for */
    for (int i = 0; i < n; i++)
    {
        int32_t left = (int32_t)(at[i] - net_ms());
        if (left <= 0) return true;
        if ((uint32_t)left < *wait_ms) *wait_ms = (uint32_t)left;
    }
    return false;
}

#ifndef NET_DEMO
static void *scr_worker(void *unused)
{
    (void)unused;
    for (;;)
    {
        scr_pass();
        pthread_mutex_lock(&scr_lock);
        uint32_t wait;
        while (!scr_due(&wait))
        {
            struct timespec until;
            clock_gettime(CLOCK_MONOTONIC, &until);
            until.tv_sec += wait / 1000;
            until.tv_nsec += (long)(wait % 1000) * 1000000L;
            if (until.tv_nsec >= 1000000000L) { until.tv_sec++; until.tv_nsec -= 1000000000L; }
            if (pthread_cond_timedwait(&scr_cond, &scr_lock, &until) == ETIMEDOUT) break;
        }
        pthread_mutex_unlock(&scr_lock);
    }
    return NULL;
}
#endif

static void scr_kick_locked(void)
{
    scr.kick = true;
    if (scr.started) pthread_cond_signal(&scr_cond);
}

void sl_net_scrobble_start(void)
{
    pthread_mutex_lock(&scr_lock);
    bool start = !scr.started;
    scr.started = true;
    pthread_mutex_unlock(&scr_lock);
    if (!start) return;
#ifndef NET_DEMO
    /* the wall clock jumps when it is set from the internet: wait on the other */
    pthread_condattr_t a;
    pthread_condattr_init(&a);
    pthread_condattr_setclock(&a, CLOCK_MONOTONIC);
    pthread_cond_init(&scr_cond, &a);
    pthread_condattr_destroy(&a);
    pthread_t t;
    pthread_attr_t ta;
    pthread_attr_init(&ta);
    pthread_attr_setstacksize(&ta, 128 * 1024);
    if (pthread_create(&t, &ta, scr_worker, NULL) == 0) pthread_detach(t);
    else
    {
        pthread_mutex_lock(&scr_lock);
        scr.started = false;
        pthread_mutex_unlock(&scr_lock);
    }
    pthread_attr_destroy(&ta);
#else
    pthread_cond_init(&scr_cond, NULL);
#endif
}

void sl_net_scrobble_config(bool listenbrainz, bool log, bool lastfm)
{
    pthread_mutex_lock(&scr_lock);
    scr.lb_on = listenbrainz;
    scr.log_on = log;
    scr.lfm_on = lastfm;
    scr_kick_locked();
    pthread_mutex_unlock(&scr_lock);
}

void sl_net_scrobble_token(const char *token)
{
    pthread_mutex_lock(&scr_lock);
    snprintf(scr.token, sizeof scr.token, "%s", token);
    scr.token_new = true;
    scr.st.test = SL_SCROB_UNTESTED;
    scr.st.user[0] = scr.st.error[0] = '\0';
    scr_kick_locked();
    pthread_mutex_unlock(&scr_lock);
}

void sl_net_scrobble_online(bool up)
{
    pthread_mutex_lock(&scr_lock);
    if (up != scr.online)
    {
        scr.online = up;
        scr.retry = up;                       /* a new chance at once */
        scr_kick_locked();
    }
    pthread_mutex_unlock(&scr_lock);
}

void sl_net_scrobble_hold(bool hold)
{
    net_card_held = hold;                     /* a DLNA download stops at its next chunk */
    pthread_mutex_lock(&scr_files);           /* a write in progress ends first */
    pthread_mutex_lock(&scr_lock);
    scr.hold = hold;
    if (!hold) { scr.reload = true; scr_kick_locked(); }   /* the computer may have changed the files */
    pthread_mutex_unlock(&scr_lock);
    pthread_mutex_unlock(&scr_files);
}

bool sl_net_scrobble_add(const struct sl_listen *l)
{
    pthread_mutex_lock(&scr_lock);
    bool ok = scr.n_inbox < SCR_INBOX;
    if (ok) scr.inbox[scr.n_inbox++] = *l;
    scr_kick_locked();
    pthread_mutex_unlock(&scr_lock);
    return ok;
}

void sl_net_scrobble_now(const struct sl_listen *l)
{
    pthread_mutex_lock(&scr_lock);
    scr.now = *l;
    scr.now_pending = true;
    scr.now_ms = net_ms();
    scr_kick_locked();
    pthread_mutex_unlock(&scr_lock);
}

static void lfm_ask(int req, const char *user, const char *pass)
{
    pthread_mutex_lock(&scr_lock);
    scr.lfm_req = req;
    snprintf(scr.lfm_user, sizeof scr.lfm_user, "%s", user ? user : "");
    snprintf(scr.lfm_pass, sizeof scr.lfm_pass, "%s", pass ? pass : "");
    if (req == LFM_REQ_PHONE || req == LFM_REQ_PASSWORD)
    {
        scr.st.lfm_auth = req == LFM_REQ_PHONE ? SL_LFM_AUTH_TOKEN : SL_LFM_AUTH_CHECKING;
        scr.st.lfm_url[0] = scr.st.lfm_error[0] = '\0';
        scr.st.lfm_auth_seq++;
    }
    scr_kick_locked();
    pthread_mutex_unlock(&scr_lock);
}
void sl_net_lastfm_signin_phone(void) { lfm_ask(LFM_REQ_PHONE, NULL, NULL); }
void sl_net_lastfm_signin_password(const char *user, const char *pass) { lfm_ask(LFM_REQ_PASSWORD, user, pass); }
void sl_net_lastfm_signin_cancel(void) { lfm_ask(LFM_REQ_CANCEL, NULL, NULL); }
void sl_net_lastfm_signout(void) { lfm_ask(LFM_REQ_SIGNOUT, NULL, NULL); }

void sl_net_scrobble_test(void)
{
    pthread_mutex_lock(&scr_lock);
    scr.test = true;
    scr.st.test = SL_SCROB_TESTING;
    scr_kick_locked();
    pthread_mutex_unlock(&scr_lock);
}

void sl_net_scrobble_status(struct sl_scrobble_status *s)
{
    pthread_mutex_lock(&scr_lock);
    *s = scr.st;
    pthread_mutex_unlock(&scr_lock);
}

bool sl_net_scrobble_message(char *out, size_t n)
{
    pthread_mutex_lock(&scr_lock);
    bool any = scr.n_msgs > 0;
    if (any)
    {
        snprintf(out, n, "%s", scr.msgs[scr.msg_first]);
        scr.msg_first = (scr.msg_first + 1) % SCR_MSGS;
        scr.n_msgs--;
    }
    pthread_mutex_unlock(&scr_lock);
    return any;
}

void sl_net_scrobble_poll(void)
{
#ifdef NET_DEMO
    uint32_t wait;
    if (scr.started && scr_due(&wait)) scr_pass();   /* the worker, in place */
#endif
}

bool sl_net_scrobble_flush(int ms)
{
    uint32_t until = net_ms() + (uint32_t)ms;
    for (;;)
    {
        sl_net_scrobble_poll();
        pthread_mutex_lock(&scr_lock);
        bool done = !scr.started || scr.hold || (!scr.n_inbox && !scr.writing);
        pthread_mutex_unlock(&scr_lock);
        if (done) return true;
        if ((int32_t)(net_ms() - until) >= 0) return false;
        net_sleep_ms(20);
    }
}

/* ------------------------------------------------------------ erasing */
/* What "Erase GabagoolOS data" set aside at the start (.rockbox/sloppy-
 * erased0..9, a thumbnail a cover, so thousands of files on a big card),
 * deleted here on a thread of its own at the lowest priority, so the
 * player is in use at once. A folder left half done (the player went off)
 * is picked up at the next start. */
#include <dirent.h>
#include <sys/resource.h>
static volatile int erase_files;          /* deleted so far, for the log and the tests */
static volatile bool erase_running;
static void erase_tree(char *path, size_t cap)
{
    DIR *d = opendir(path);
    if (d)
    {
        size_t n = strlen(path);
        struct dirent *e;
        while ((e = readdir(d)))
        {
            if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
            if (n + 1 + strlen(e->d_name) + 1 > cap) continue;
            path[n] = '/';
            strcpy(path + n + 1, e->d_name);
            struct stat st;
            if (!lstat(path, &st) && S_ISDIR(st.st_mode)) erase_tree(path, cap);
            else if (!unlink(path)) erase_files++;
            path[n] = '\0';
        }
        closedir(d);
    }
    rmdir(path);
}
static void *erase_run(void *arg)
{
    (void)arg;
    setpriority(PRIO_PROCESS, 0, 19);     /* this thread only, on Linux */
    char base[512], path[1024];
    snprintf(base, sizeof base, "%s/.rockbox", net_root() ? net_root() : "");
    for (int i = 0; i < 10; i++)
    {
        snprintf(path, sizeof path, "%s/sloppy-erased%d", base, i);
        erase_tree(path, sizeof path);
    }
    erase_running = false;
    return NULL;
}
/* start deleting what was set aside, if anything was; false when nothing is */
bool sl_net_erase_start(void)
{
    if (erase_running || !net_root()) return erase_running;
    char path[512];
    bool any = false;
    struct stat st;
    for (int i = 0; i < 10 && !any; i++)
    {
        snprintf(path, sizeof path, "%s/.rockbox/sloppy-erased%d", net_root(), i);
        any = !stat(path, &st);
    }
    if (!any) return false;
    erase_running = true;
    pthread_t t;
    if (pthread_create(&t, NULL, erase_run, NULL)) { erase_running = false; return false; }
    pthread_detach(t);
    return true;
}
bool sl_net_erase_busy(void) { return erase_running; }
int sl_net_erase_count(void) { return erase_files; }
