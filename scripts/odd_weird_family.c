/* Erdős #470: C/GMP port of scripts/odd_weird_family.py (same search, same checkpoint format).
 *
 * Build: gcc -O2 -o /tmp/owf scripts/odd_weird_family.c -lgmp
 * Usage: /tmp/owf K [CKFILE]      (env START3=E, STOP3=E exactly as in the Python script)
 *
 * This is a line-by-line port: same node order, same counters (n, fam, qchk, star, skip), same
 * failure list and the same checkpoint keys (Python repr of (f, un, ud, j, q0)), so the Python and
 * C workers can share and resume from the same CKFILE. All arithmetic is exact (mpz).
 * isprime is the same deterministic Miller-Rabin (same bases, same sieve below 2^24) as in Python.
 * Differences that do not change results: the divisor cache is per depth instead of a dict, the
 * Pstruct cache keeps only the last prefix, and checkpoint reloads read only complete new lines.
 *
 * Speed: the sorted divisors and Pstruct0 (the hot spot) run in unsigned __int128 when
 * sigma < 2^126, in fixed 256-bit integers when sigma < 2^254 and every prime of f is < 2^64, and
 * in mpz otherwise. The bitset shift-or only touches words that can change. All three paths are
 * the same algorithm on the same exact integers.
 * Extra env vars (testing only): PSLOW=1 forces the mpz path, PSLOW=2 skips the u128 path;
 * NODELIMIT=N stops after N nodes and prints the counters; ROOTTEST=E runs only the region subtree
 * of the root 3^E (no checkpoint), i.e. the call whose True closes the top-level loop over v_3.
 * Validation (session 31): K = 4 and K = 5 give the same counters as Python and a byte-identical
 * K = 5 checkpoint (auto, PSLOW=1, PSLOW=2); Python<->C cross-resume gives the same key set.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <gmp.h>

#define SIEVE_N (1u << 24)
#define CB 32768L /* C = 1<<15 */
#define NW (CB / 64)
#define WIN 10000L
#define MAXK 16
#define CKDEPTH 3

static unsigned char *SV;
static int K, START3 = 1, STOP3 = 0;
static long NODELIMIT = 0; /* env NODELIMIT=N: stop after N nodes (benchmarking/profiling only) */
static long st_n, st_fam, st_qchk, st_star, st_skip, st_nfail;
static char *fails[20];
static time_t t0;

/* current prefix f = [(fp[i], fe[i]) for i < L] */
static mpz_t fp[MAXK];
static long fe[MAXK];

static void sieve(void) {
  SV = malloc(SIEVE_N);
  memset(SV, 1, SIEVE_N);
  SV[0] = SV[1] = 0;
  for (unsigned i = 2; (unsigned long)i * i < SIEVE_N; i++)
    if (SV[i])
      for (unsigned j = i * i; j < SIEVE_N; j += i) SV[j] = 0;
}

static int isprime(const mpz_t n) {
  static int init = 0;
  static mpz_t d, x, nm1, a;
  if (!init) { mpz_inits(d, x, nm1, a, NULL); init = 1; }
  if (mpz_cmp_ui(n, SIEVE_N) < 0) {
    if (mpz_sgn(n) < 0) return 0;
    return SV[mpz_get_ui(n)] == 1;
  }
  static const unsigned long TP[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
  for (int i = 0; i < 11; i++)
    if (mpz_divisible_ui_p(n, TP[i])) return mpz_cmp_ui(n, TP[i]) == 0;
  mpz_sub_ui(nm1, n, 1);
  mpz_set(d, nm1);
  long s = 0;
  while (mpz_even_p(d)) { mpz_tdiv_q_2exp(d, d, 1); s++; }
  static const unsigned long AB[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
  for (int i = 0; i < 12; i++) {
    mpz_set_ui(a, AB[i]);
    mpz_powm(x, a, d, n);
    if (mpz_cmp_ui(x, 1) == 0 || mpz_cmp(x, nm1) == 0) continue;
    int found = 0;
    for (long r = 0; r < s - 1; r++) {
      mpz_mul(x, x, x);
      mpz_mod(x, x, n);
      if (mpz_cmp(x, nm1) == 0) { found = 1; break; }
    }
    if (!found) return 0;
  }
  return 1;
}

static void sig(mpz_t r, const mpz_t p, long e) { /* (p^(e+1)-1)/(p-1) */
  mpz_t t;
  mpz_init(t);
  mpz_pow_ui(r, p, e + 1);
  mpz_sub_ui(r, r, 1);
  mpz_sub_ui(t, p, 1);
  mpz_divexact(r, r, t);
  mpz_clear(t);
}

/* ---------- repr helpers ---------- */
typedef struct { char *s; size_t n, cap; } sbuf;
static void sb_add(sbuf *b, const char *s) {
  size_t l = strlen(s);
  if (b->n + l + 1 > b->cap) { b->cap = 2 * (b->n + l + 1) + 64; b->s = realloc(b->s, b->cap); }
  memcpy(b->s + b->n, s, l + 1);
  b->n += l;
}
static void sb_mpz(sbuf *b, const mpz_t x) {
  char *s = mpz_get_str(NULL, 10, x);
  sb_add(b, s);
  free(s);
}
static void sb_long(sbuf *b, long x) { char t[32]; snprintf(t, sizeof t, "%ld", x); sb_add(b, t); }
static void sb_f(sbuf *b, int L) {
  sb_add(b, "[");
  for (int i = 0; i < L; i++) {
    if (i) sb_add(b, ", ");
    sb_add(b, "(");
    sb_mpz(b, fp[i]);
    sb_add(b, ", ");
    sb_long(b, fe[i]);
    sb_add(b, ")");
  }
  sb_add(b, "]");
}

/* ---------- checkpoint set ---------- */
static char **HS;
static size_t HCAP, HN;
static uint64_t hstr(const char *s) {
  uint64_t h = 1469598103934665603ULL;
  for (; *s; s++) { h ^= (unsigned char)*s; h *= 1099511628211ULL; }
  return h;
}
static int hs_has(const char *s) {
  if (!HCAP) return 0;
  for (size_t i = hstr(s) & (HCAP - 1);; i = (i + 1) & (HCAP - 1)) {
    if (!HS[i]) return 0;
    if (!strcmp(HS[i], s)) return 1;
  }
}
static void hs_add(const char *s) {
  if (hs_has(s)) return;
  if (2 * (HN + 1) > HCAP) {
    size_t oc = HCAP;
    char **old = HS;
    HCAP = oc ? 2 * oc : 1 << 16;
    HS = calloc(HCAP, sizeof(char *));
    HN = 0;
    for (size_t i = 0; i < oc; i++)
      if (old[i]) {
        size_t j = hstr(old[i]) & (HCAP - 1);
        while (HS[j]) j = (j + 1) & (HCAP - 1);
        HS[j] = old[i];
        HN++;
      }
    free(old);
  }
  size_t j = hstr(s) & (HCAP - 1);
  while (HS[j]) j = (j + 1) & (HCAP - 1);
  HS[j] = strdup(s);
  HN++;
}
static const char *CKNAME;
static FILE *CK;
static long ckoff = 0;
static void ck_reload(void) { /* read complete new lines of CKNAME (append-only file) */
  FILE *in = fopen(CKNAME, "r");
  if (!in) return;
  fseek(in, ckoff, SEEK_SET);
  char *line = NULL;
  size_t cap = 0;
  ssize_t r;
  while ((r = getline(&line, &cap, in)) > 0) {
    if (line[r - 1] != '\n') break; /* partial line written by another worker: read it later */
    ckoff += r;
    char *a = line, *e = line + r;
    while (a < e && (*a == ' ' || *a == '\t' || *a == '\n' || *a == '\r')) a++;
    while (e > a && (e[-1] == ' ' || e[-1] == '\t' || e[-1] == '\n' || e[-1] == '\r')) e--;
    if (e > a) { *e = 0; hs_add(a); }
  }
  free(line);
  fclose(in);
}

/* ---------- divisors (sorted), cached per depth ---------- */
typedef struct { int valid, len; mpz_t kp[MAXK]; long ke[MAXK]; size_t n, cap; mpz_t *v, *w; } DL;
static DL dc[MAXK + 1];
static void dl_reserve(DL *d, size_t n) {
  if (n <= d->cap) return;
  d->v = realloc(d->v, n * sizeof(mpz_t));
  d->w = realloc(d->w, n * sizeof(mpz_t));
  for (size_t i = d->cap; i < n; i++) { mpz_init(d->v[i]); mpz_init(d->w[i]); }
  d->cap = n;
}
static int dl_match(DL *d, int L) {
  if (!d->valid || d->len != L) return 0;
  for (int i = 0; i < L; i++)
    if (d->ke[i] != fe[i] || mpz_cmp(d->kp[i], fp[i])) return 0;
  return 1;
}
static DL *divisors(int L) {
  DL *d = &dc[L];
  if (dl_match(d, L)) return d;
  if (L == 0) {
    dl_reserve(d, 1);
    mpz_set_ui(d->v[0], 1);
    d->n = 1;
  } else {
    DL *b = divisors(L - 1);
    long e = fe[L - 1];
    size_t m = b->n, n = m * (e + 1);
    dl_reserve(d, n);
    for (size_t i = 0; i < m; i++) mpz_set(d->v[i], b->v[i]);
    for (long k = 1; k <= e; k++)
      for (size_t i = 0; i < m; i++) mpz_mul(d->v[k * m + i], d->v[(k - 1) * m + i], fp[L - 1]);
    /* bottom-up merge of the e+1 sorted runs of length m */
    for (size_t run = m; run < n; run *= 2) {
      for (size_t lo = 0; lo < n; lo += 2 * run) {
        size_t mid = lo + run < n ? lo + run : n, hi = lo + 2 * run < n ? lo + 2 * run : n;
        size_t i = lo, j = mid, o = lo;
        while (i < mid && j < hi) {
          if (mpz_cmp(d->v[j], d->v[i]) < 0) mpz_swap(d->w[o++], d->v[j++]);
          else mpz_swap(d->w[o++], d->v[i++]);
        }
        while (i < mid) mpz_swap(d->w[o++], d->v[i++]);
        while (j < hi) mpz_swap(d->w[o++], d->v[j++]);
      }
      mpz_t *t = d->v; d->v = d->w; d->w = t;
    }
    d->n = n;
  }
  if (!d->valid) for (int i = 0; i < MAXK; i++) mpz_init(d->kp[i]);
  d->valid = 1;
  d->len = L;
  for (int i = 0; i < L; i++) { mpz_set(d->kp[i], fp[i]); d->ke[i] = fe[i]; }
  return d;
}

/* ---------- P = subset sums of the proper divisors of M ---------- */
typedef struct { int none; long c; /* -1 = None */ mpz_t sp; uint64_t B[NW]; } PS;
/* B |= (B<<d) & mask, computed only for bit positions <= top (callers guarantee that bits above
 * top are either zero or overwritten afterwards, so this is exact) */
static void shiftor(uint64_t *B, unsigned long d, long top) {
  if (d >= (unsigned long)CB) return;
  long ws = d / 64, bs = d % 64, hw = top / 64;
  if (hw > NW - 1) hw = NW - 1;
  for (long w = hw; w >= ws; w--) {
    uint64_t v = B[w - ws] << bs;
    if (bs && w - ws - 1 >= 0) v |= B[w - ws - 1] >> (64 - bs);
    B[w] |= v;
  }
}
static int bit(const uint64_t *B, unsigned long y) { return (B[y / 64] >> (y % 64)) & 1; }

static void Pstruct0(PS *ps, int L, const mpz_t M, const mpz_t sigma) {
  DL *dl = divisors(L);
  mpz_t *ds = dl->v;
  size_t n = dl->n - 1;
  mpz_sub(ps->sp, sigma, M);
  memset(ps->B, 0, sizeof ps->B);
  ps->B[0] = 1;
  ps->none = 0;
  long T = 0, c = -1;
  size_t i = 0;
  while (i < n) {
    if (mpz_cmp_ui(ds[i], 2 * CB - T) >= 0) {
      long hb = T / 2;
      c = 0;
      for (long w = hb / 64; w >= 0; w--) {
        uint64_t x = ~ps->B[w];
        if (w == hb / 64 && hb % 64 != 63) x &= (((uint64_t)1) << (hb % 64 + 1)) - 1;
        if (x) { c = w * 64 + (63 - __builtin_clzll(x)) + 1; break; }
      }
      if (T - 2 * c < 0) { ps->none = 1; return; }
      break;
    }
    unsigned long d = mpz_get_ui(ds[i]);
    shiftor(ps->B, d, T + d); /* every bit of B is <= T before the shift */
    T += d;
    i++;
  }
  ps->c = c;
  if (c >= 0) {
    mpz_t Sj, lim;
    mpz_init_set_ui(Sj, T);
    mpz_init(lim);
    size_t j = i;
    while (j < n) {
      mpz_sub_ui(lim, Sj, 2 * c);
      mpz_add_ui(lim, lim, 1);
      /* l = bisect_right(ds, lim, j, n) */
      size_t lo = j, hi = n;
      while (lo < hi) {
        size_t md = (lo + hi) / 2;
        if (mpz_cmp(lim, ds[md]) < 0) hi = md; else lo = md + 1;
      }
      if (lo == j) { ps->none = 1; mpz_clears(Sj, lim, NULL); return; }
      for (size_t l = j; l < lo; l++) mpz_add(Sj, Sj, ds[l]);
      j = lo;
    }
    for (size_t l = i; l < n; l++) {
      if (mpz_cmp_ui(ds[l], c) >= 0) break;
      shiftor(ps->B, mpz_get_ui(ds[l]), c - 1); /* bits >= c are all set just below */
    }
    if (c < CB) {
      ps->B[c / 64] |= ~(uint64_t)0 << (c % 64);
      for (long w = c / 64 + 1; w < NW; w++) ps->B[w] = ~(uint64_t)0;
    }
    if (mpz_cmp(Sj, ps->sp)) { fprintf(stderr, "assert T==sp failed\n"); exit(2); }
    mpz_clears(Sj, lim, NULL);
  } else if (mpz_cmp_ui(ps->sp, T)) { fprintf(stderr, "assert T==sp failed\n"); exit(2); }
  if (c > CB) ps->none = 1;
}

/* ---------- fast path: the same divisors and the same Pstruct0 in unsigned __int128 ----------
 * Used when sigma < 2^126 (then every divisor and every partial sum is < 2^127): same algorithm on
 * the same exact integers, so the result is identical to the mpz path (checked with PSLOW=1). */
typedef unsigned __int128 u128;
static int PSLOW = 0; /* env PSLOW: 0 = auto (u128, w256, mpz), 1 = mpz only, 2 = w256 (or mpz) only */
static u128 to128(const mpz_t x) {
  u128 r = mpz_getlimbn(x, 0);
  if (mpz_size(x) > 1) r |= ((u128)mpz_getlimbn(x, 1)) << 64;
  return r;
}
typedef struct { int valid, len; mpz_t kp[MAXK]; long ke[MAXK]; size_t n, cap; u128 *v, *w; } DL128;
static DL128 dc128[MAXK + 1];
static DL128 *divisors128(int L) {
  DL128 *d = &dc128[L];
  if (d->valid && d->len == L) {
    int ok = 1;
    for (int i = 0; i < L && ok; i++) ok = d->ke[i] == fe[i] && !mpz_cmp(d->kp[i], fp[i]);
    if (ok) return d;
  }
  size_t n;
  if (L == 0) n = 1;
  else n = divisors128(L - 1)->n * (fe[L - 1] + 1);
  if (n > d->cap) {
    d->v = realloc(d->v, n * sizeof(u128));
    d->w = realloc(d->w, n * sizeof(u128));
    d->cap = n;
  }
  /* incremental case: the cache holds the same prefix with the last exponent e-1, so the new
   * list is that sorted list merged with the single sorted run base * p^e (same result) */
  int inc = L > 0 && d->valid && d->len == L && d->ke[L - 1] == fe[L - 1] - 1 &&
            !mpz_cmp(d->kp[L - 1], fp[L - 1]);
  for (int i = 0; inc && i < L - 1; i++) inc = d->ke[i] == fe[i] && !mpz_cmp(d->kp[i], fp[i]);
  if (L == 0) d->v[0] = 1;
  else if (inc) {
    DL128 *b = &dc128[L - 1];
    size_t m = b->n, old = d->n, o = 0, i = 0, j = 0;
    u128 p = to128(fp[L - 1]), pe = 1;
    for (long k = 0; k < fe[L - 1]; k++) pe *= p;
    /* d->w = merge(d->v[0..old), b->v * pe) */
    while (i < old && j < m) {
      u128 y = b->v[j] * pe;
      if (y < d->v[i]) { d->w[o++] = y; j++; } else d->w[o++] = d->v[i++];
    }
    while (i < old) d->w[o++] = d->v[i++];
    while (j < m) d->w[o++] = b->v[j++] * pe;
    u128 *t = d->v; d->v = d->w; d->w = t;
  } else {
    DL128 *b = &dc128[L - 1];
    size_t m = b->n;
    u128 p = to128(fp[L - 1]);
    memcpy(d->v, b->v, m * sizeof(u128));
    for (size_t k = m; k < n; k++) d->v[k] = d->v[k - m] * p;
    for (size_t run = m; run < n; run *= 2) {
      for (size_t lo = 0; lo < n; lo += 2 * run) {
        size_t mid = lo + run < n ? lo + run : n, hi = lo + 2 * run < n ? lo + 2 * run : n;
        size_t i = lo, j = mid, o = lo;
        while (i < mid && j < hi) d->w[o++] = d->v[j] < d->v[i] ? d->v[j++] : d->v[i++];
        while (i < mid) d->w[o++] = d->v[i++];
        while (j < hi) d->w[o++] = d->v[j++];
      }
      u128 *t = d->v; d->v = d->w; d->w = t;
    }
  }
  d->n = n;
  if (!d->valid) for (int i = 0; i < MAXK; i++) mpz_init(d->kp[i]);
  d->valid = 1;
  d->len = L;
  for (int i = 0; i < L; i++) { mpz_set(d->kp[i], fp[i]); d->ke[i] = fe[i]; }
  return d;
}
static void Pstruct0_128(PS *ps, int L, const mpz_t M, const mpz_t sigma) {
  DL128 *dl = divisors128(L);
  u128 *ds = dl->v;
  size_t n = dl->n - 1;
  mpz_sub(ps->sp, sigma, M);
  u128 sp = to128(ps->sp);
  memset(ps->B, 0, sizeof ps->B);
  ps->B[0] = 1;
  ps->none = 0;
  long T = 0, c = -1;
  size_t i = 0;
  while (i < n) {
    if (ds[i] >= (u128)(2 * CB - T)) {
      long hb = T / 2;
      c = 0;
      for (long w = hb / 64; w >= 0; w--) {
        uint64_t x = ~ps->B[w];
        if (w == hb / 64 && hb % 64 != 63) x &= (((uint64_t)1) << (hb % 64 + 1)) - 1;
        if (x) { c = w * 64 + (63 - __builtin_clzll(x)) + 1; break; }
      }
      if (T - 2 * c < 0) { ps->none = 1; return; }
      break;
    }
    unsigned long d = (unsigned long)ds[i];
    shiftor(ps->B, d, T + d);
    T += d;
    i++;
  }
  ps->c = c;
  u128 Sj = T;
  if (c >= 0) {
    size_t j = i;
    while (j < n) {
      u128 lim = Sj - 2 * (u128)c + 1; /* Sj >= T >= 2c */
      size_t lo = j, hi = n;
      while (lo < hi) {
        size_t md = (lo + hi) / 2;
        if (lim < ds[md]) hi = md; else lo = md + 1;
      }
      if (lo == j) { ps->none = 1; return; }
      for (size_t l = j; l < lo; l++) Sj += ds[l];
      j = lo;
    }
    for (size_t l = i; l < n; l++) {
      if (ds[l] >= (u128)c) break;
      shiftor(ps->B, (unsigned long)ds[l], c - 1);
    }
    if (c < CB) {
      ps->B[c / 64] |= ~(uint64_t)0 << (c % 64);
      for (long w = c / 64 + 1; w < NW; w++) ps->B[w] = ~(uint64_t)0;
    }
  }
  if (Sj != sp) { fprintf(stderr, "assert T==sp failed (u128)\n"); exit(2); }
  if (c > CB) ps->none = 1;
}

/* ---------- fast path 2: fixed 256-bit integers (sigma < 2^254, every prime of f < 2^64) ----------
 * Same algorithm as Pstruct0 on the same exact integers (no overflow below 2^256). */
typedef struct { uint64_t x[4]; } w256;
static inline int wlt(const w256 *a, const w256 *b) {
  for (int i = 3; i >= 0; i--) if (a->x[i] != b->x[i]) return a->x[i] < b->x[i];
  return 0;
}
static inline w256 wmul64(w256 a, uint64_t p) {
  w256 r; u128 c = 0;
  for (int i = 0; i < 4; i++) { c += (u128)a.x[i] * p; r.x[i] = (uint64_t)c; c >>= 64; }
  return r;
}
static inline void wadd(w256 *a, const w256 *b) {
  u128 c = 0;
  for (int i = 0; i < 4; i++) { c += (u128)a->x[i] + b->x[i]; a->x[i] = (uint64_t)c; c >>= 64; }
}
static inline int wltsmall(const w256 *a, uint64_t s) { /* a < s */
  return !a->x[3] && !a->x[2] && !a->x[1] && a->x[0] < s;
}
static w256 wfrom(const mpz_t z) {
  w256 r = {{0, 0, 0, 0}};
  for (size_t i = 0; i < mpz_size(z) && i < 4; i++) r.x[i] = mpz_getlimbn(z, i);
  return r;
}
typedef struct { int valid, len; mpz_t kp[MAXK]; long ke[MAXK]; size_t n, cap; w256 *v, *w; } DL256;
static DL256 dc256[MAXK + 1];
static DL256 *divisors256(int L) {
  DL256 *d = &dc256[L];
  if (d->valid && d->len == L) {
    int ok = 1;
    for (int i = 0; i < L && ok; i++) ok = d->ke[i] == fe[i] && !mpz_cmp(d->kp[i], fp[i]);
    if (ok) return d;
  }
  size_t n;
  if (L == 0) n = 1;
  else n = divisors256(L - 1)->n * (fe[L - 1] + 1);
  if (n > d->cap) {
    d->v = realloc(d->v, n * sizeof(w256));
    d->w = realloc(d->w, n * sizeof(w256));
    d->cap = n;
  }
  int inc = L > 0 && d->valid && d->len == L && d->ke[L - 1] == fe[L - 1] - 1 &&
            !mpz_cmp(d->kp[L - 1], fp[L - 1]);
  for (int i = 0; inc && i < L - 1; i++) inc = d->ke[i] == fe[i] && !mpz_cmp(d->kp[i], fp[i]);
  if (L == 0) { w256 one = {{1, 0, 0, 0}}; d->v[0] = one; }
  else if (inc) {
    DL256 *b = &dc256[L - 1];
    size_t m = b->n, old = d->n, o = 0, i = 0, j = 0;
    uint64_t p = mpz_getlimbn(fp[L - 1], 0);
    while (i < old && j < m) {
      w256 y = b->v[j];
      for (long k = 0; k < fe[L - 1]; k++) y = wmul64(y, p);
      if (wlt(&y, &d->v[i])) { d->w[o++] = y; j++; } else d->w[o++] = d->v[i++];
    }
    while (i < old) d->w[o++] = d->v[i++];
    while (j < m) { w256 y = b->v[j++]; for (long k = 0; k < fe[L - 1]; k++) y = wmul64(y, p); d->w[o++] = y; }
    w256 *t = d->v; d->v = d->w; d->w = t;
  } else {
    DL256 *b = &dc256[L - 1];
    size_t m = b->n;
    uint64_t p = mpz_getlimbn(fp[L - 1], 0);
    memcpy(d->v, b->v, m * sizeof(w256));
    for (size_t k = m; k < n; k++) d->v[k] = wmul64(d->v[k - m], p);
    for (size_t run = m; run < n; run *= 2) {
      for (size_t lo = 0; lo < n; lo += 2 * run) {
        size_t mid = lo + run < n ? lo + run : n, hi = lo + 2 * run < n ? lo + 2 * run : n;
        size_t i = lo, j = mid, o = lo;
        while (i < mid && j < hi) d->w[o++] = wlt(&d->v[j], &d->v[i]) ? d->v[j++] : d->v[i++];
        while (i < mid) d->w[o++] = d->v[i++];
        while (j < hi) d->w[o++] = d->v[j++];
      }
      w256 *t = d->v; d->v = d->w; d->w = t;
    }
  }
  d->n = n;
  if (!d->valid) for (int i = 0; i < MAXK; i++) mpz_init(d->kp[i]);
  d->valid = 1;
  d->len = L;
  for (int i = 0; i < L; i++) { mpz_set(d->kp[i], fp[i]); d->ke[i] = fe[i]; }
  return d;
}
static void Pstruct0_256(PS *ps, int L, const mpz_t M, const mpz_t sigma) {
  DL256 *dl = divisors256(L);
  w256 *ds = dl->v;
  size_t n = dl->n - 1;
  mpz_sub(ps->sp, sigma, M);
  w256 sp = wfrom(ps->sp);
  memset(ps->B, 0, sizeof ps->B);
  ps->B[0] = 1;
  ps->none = 0;
  long T = 0, c = -1;
  size_t i = 0;
  while (i < n) {
    if (!wltsmall(&ds[i], 2 * CB - T)) {
      long hb = T / 2;
      c = 0;
      for (long w = hb / 64; w >= 0; w--) {
        uint64_t x = ~ps->B[w];
        if (w == hb / 64 && hb % 64 != 63) x &= (((uint64_t)1) << (hb % 64 + 1)) - 1;
        if (x) { c = w * 64 + (63 - __builtin_clzll(x)) + 1; break; }
      }
      if (T - 2 * c < 0) { ps->none = 1; return; }
      break;
    }
    unsigned long d = ds[i].x[0];
    shiftor(ps->B, d, T + d);
    T += d;
    i++;
  }
  ps->c = c;
  w256 Sj = {{(uint64_t)T, 0, 0, 0}};
  if (c >= 0) {
    size_t j = i;
    while (j < n) {
      /* lim = Sj - 2c + 1 (Sj >= T >= 2c): subtract the small value 2c-1 or add 1 */
      w256 lim = Sj;
      long sub = 2 * c - 1;
      if (sub < 0) { w256 one = {{1, 0, 0, 0}}; wadd(&lim, &one); }
      else {
        uint64_t bw = (uint64_t)sub;
        for (int k = 0; k < 4 && bw; k++) {
          uint64_t o = lim.x[k];
          lim.x[k] = o - bw;
          bw = o < bw ? 1 : 0;
        }
      }
      size_t lo = j, hi = n;
      while (lo < hi) {
        size_t md = (lo + hi) / 2;
        if (wlt(&lim, &ds[md])) hi = md; else lo = md + 1;
      }
      if (lo == j) { ps->none = 1; return; }
      for (size_t l = j; l < lo; l++) wadd(&Sj, &ds[l]);
      j = lo;
    }
    for (size_t l = i; l < n; l++) {
      if (!wltsmall(&ds[l], (uint64_t)c)) break;
      shiftor(ps->B, ds[l].x[0], c - 1);
    }
    if (c < CB) {
      ps->B[c / 64] |= ~(uint64_t)0 << (c % 64);
      for (long w = c / 64 + 1; w < NW; w++) ps->B[w] = ~(uint64_t)0;
    }
  }
  if (memcmp(&Sj, &sp, sizeof sp)) { fprintf(stderr, "assert T==sp failed (w256)\n"); exit(2); }
  if (c > CB) ps->none = 1;
}
static int primes_fit64(int L) {
  for (int i = 0; i < L; i++) if (mpz_size(fp[i]) > 1) return 0;
  return 1;
}
static PS PC;
static int pc_valid = 0, pc_len;
static mpz_t pc_kp[MAXK];
static long pc_ke[MAXK];
static PS *Pstruct(int L, const mpz_t M, const mpz_t sigma) {
  if (pc_valid && pc_len == L) {
    int ok = 1;
    for (int i = 0; i < L && ok; i++) ok = pc_ke[i] == fe[i] && !mpz_cmp(pc_kp[i], fp[i]);
    if (ok) return &PC;
  }
  size_t sb = mpz_sizeinbase(sigma, 2);
  if (!PSLOW && sb <= 126) Pstruct0_128(&PC, L, M, sigma);
  else if ((PSLOW == 0 || PSLOW == 2) && sb <= 254 && primes_fit64(L)) Pstruct0_256(&PC, L, M, sigma);
  else Pstruct0(&PC, L, M, sigma);
  pc_valid = 1;
  pc_len = L;
  for (int i = 0; i < L; i++) { mpz_set(pc_kp[i], fp[i]); pc_ke[i] = fe[i]; }
  return &PC;
}

static int inP(const mpz_t x, const PS *ps) {
  static int init = 0;
  static mpz_t t;
  if (!init) { mpz_init(t); init = 1; }
  if (mpz_sgn(x) < 0 || mpz_cmp(x, ps->sp) > 0) return 0;
  if (ps->c < 0) {
    if (mpz_cmp_ui(x, CB) < 0) return bit(ps->B, mpz_get_ui(x));
    mpz_sub(t, ps->sp, x);
    return bit(ps->B, mpz_get_ui(t));
  }
  if (mpz_cmp_ui(x, CB) < 0) return bit(ps->B, mpz_get_ui(x));
  mpz_sub(t, ps->sp, x); /* x > sp-C  <=>  sp-x < C */
  if (mpz_cmp_ui(t, CB) < 0) return bit(ps->B, mpz_get_ui(t));
  return 1;
}
static int inQ(const mpz_t x, const mpz_t M, const PS *ps) {
  if (inP(x, ps)) return 1;
  mpz_t y;
  mpz_init(y);
  mpz_sub(y, x, M);
  int r = inP(y, ps);
  mpz_clear(y);
  return r;
}

static int pp_Mq(const mpz_t q, const mpz_t M, const mpz_t D, const PS *ps) {
  mpz_t sigma, lo, hi, alo, ahi, t, x, a;
  mpz_inits(sigma, lo, hi, alo, ahi, t, x, a, NULL);
  int res = 0;
  mpz_add(sigma, ps->sp, M);
  if (ps->c >= 0) {
    for (int w = 0; w < 2; w++) {
      if (w == 0) { mpz_set_ui(lo, ps->c); mpz_sub_ui(hi, ps->sp, ps->c); }
      else { mpz_add_ui(lo, M, ps->c); mpz_sub_ui(hi, sigma, ps->c); }
      mpz_cdiv_q(alo, lo, q);
      mpz_sub(alo, alo, D);
      if (mpz_cmp_ui(alo, ps->c) < 0) mpz_set_ui(alo, ps->c);
      mpz_fdiv_q(ahi, hi, q);
      mpz_sub(ahi, ahi, D);
      mpz_sub_ui(t, ps->sp, ps->c);
      if (mpz_cmp(t, ahi) < 0) mpz_set(ahi, t);
      if (mpz_cmp(alo, ahi) <= 0) { res = 1; goto out; }
    }
  }
  for (long ai = 0;; ) {
    mpz_add_ui(t, D, ai);
    mpz_mul(x, t, q);
    if (mpz_cmp(x, sigma) > 0 || mpz_cmp_ui(ps->sp, ai) < 0) break;
    mpz_set_ui(a, ai);
    if (inP(a, ps)) {
      if (inP(x, ps)) { res = 1; goto out; }
      mpz_sub(t, x, M);
      if (inP(t, ps)) { res = 1; goto out; }
    }
    ai++;
    if (ai > 20000) break;
  }
out:
  mpz_clears(sigma, lo, hi, alo, ahi, t, x, a, NULL);
  return res;
}

/* pp_Mqe: exact DFS over base-q digits with a budget of 5000 calls */
static long budget;
static const mpz_t *g_q, *g_M, *g_sigma;
static const PS *g_ps;
static long g_e;
static int go(const mpz_t x, long i) {
  if (budget <= 0) return 0;
  budget--;
  if (i == g_e) return inP(x, g_ps);
  mpz_t s0, m, y;
  mpz_inits(s0, m, y, NULL);
  int res = 0;
  mpz_fdiv_r(s0, x, *g_q);
  if (mpz_cmp(x, *g_sigma) < 0) mpz_set(m, x); else mpz_set(m, *g_sigma);
  while (mpz_cmp(s0, m) <= 0) {
    if (inQ(s0, *g_M, g_ps)) {
      mpz_sub(y, x, s0);
      mpz_fdiv_q(y, y, *g_q);
      if (go(y, i + 1)) { res = 1; break; }
    }
    mpz_add(s0, s0, *g_q);
    if (budget <= 0) break;
  }
  mpz_clears(s0, m, y, NULL);
  return res;
}
static int pp_Mqe(const mpz_t q, long e, const mpz_t M, const PS *ps) {
  mpz_t sigma, r, t;
  mpz_inits(sigma, r, t, NULL);
  mpz_add(sigma, ps->sp, M);
  sig(r, q, e);
  mpz_mul(r, r, sigma);
  mpz_pow_ui(t, q, e);
  mpz_mul(t, t, M);
  mpz_mul_2exp(t, t, 1);
  mpz_sub(r, r, t);
  budget = 5000;
  g_q = (const mpz_t *)q;
  g_M = (const mpz_t *)M;
  g_sigma = (const mpz_t *)&sigma;
  g_ps = ps;
  g_e = e;
  int res = go(r, 0);
  mpz_clears(sigma, r, t, NULL);
  return res;
}

static void add_fail(const char *tag, int L, const mpz_t *q, long e) {
  st_nfail++;
  if (st_nfail > 20) return;
  sbuf b = {0};
  sb_add(&b, "('");
  sb_add(&b, tag);
  sb_add(&b, "', ");
  sb_f(&b, L);
  if (q) { sb_add(&b, ", "); sb_mpz(&b, *q); }
  if (e >= 0) { sb_add(&b, ", "); sb_long(&b, e); }
  sb_add(&b, ")");
  fails[st_nfail - 1] = b.s;
}

static int family(int L, const mpz_t M, const mpz_t sigma, const mpz_t un, const mpz_t ud, const mpz_t q0) {
  st_fam++;
  int res = 0;
  mpz_t D, t, u, qtop, q, wlo[3], whi[3], s_, pe;
  mpz_inits(D, t, u, qtop, q, s_, pe, NULL);
  for (int i = 0; i < 3; i++) mpz_inits(wlo[i], whi[i], NULL);
  mpz_mul_2exp(D, M, 1);
  mpz_sub(D, D, sigma);
  mpz_mul_2exp(t, ud, 1);
  if (mpz_cmp(un, t) >= 0) goto out;
  PS *ps = Pstruct(L, M, sigma);
  if (ps->none) { add_fail("nostruct", L, NULL, -1); goto out; }
  mpz_fdiv_q(qtop, sigma, D);
  if (mpz_cmp(q0, qtop) <= 0) {
    int nw;
    if (ps->c < 0) { nw = 1; mpz_set(wlo[0], q0); mpz_set(whi[0], qtop); }
    else {
      nw = 3;
      mpz_set(wlo[0], q0);
      mpz_set_ui(t, CB); mpz_fdiv_q(t, t, D); mpz_add_ui(t, t, 1);
      if (mpz_cmp(qtop, t) < 0) mpz_set(whi[0], qtop); else mpz_set(whi[0], t);
      mpz_sub_ui(t, ps->sp, CB); mpz_fdiv_q(wlo[1], t, D);
      mpz_add_ui(t, M, CB); mpz_fdiv_q(whi[1], t, D); mpz_add_ui(whi[1], whi[1], 1);
      mpz_sub_ui(t, sigma, CB); mpz_fdiv_q(wlo[2], t, D);
      mpz_set(whi[2], qtop);
    }
    /* effective ranges [max(lo,q0), min(hi,qtop)]; "seen" = inside an earlier effective range */
    for (int w = 0; w < nw; w++) {
      if (mpz_cmp(wlo[w], q0) < 0) mpz_set(wlo[w], q0);
      if (mpz_cmp(whi[w], qtop) > 0) mpz_set(whi[w], qtop);
    }
    for (int w = 0; w < nw; w++) {
      mpz_set(q, wlo[w]);
      if (mpz_even_p(q)) mpz_add_ui(q, q, 1);
      for (; mpz_cmp(q, whi[w]) <= 0; mpz_add_ui(q, q, 2)) {
        if (!isprime(q)) continue;
        int seen = 0;
        for (int v = 0; v < w && !seen; v++)
          if (mpz_cmp(q, wlo[v]) >= 0 && mpz_cmp(q, whi[v]) <= 0) seen = 1;
        if (seen) continue;
        st_qchk++;
        if (!pp_Mq(q, M, D, ps)) { add_fail("Mq", L, (const mpz_t *)&q, -1); goto out; }
      }
    }
  }
  mpz_add_ui(q, qtop, 1);
  if (mpz_cmp(q0, q) > 0) mpz_set(q, q0);
  for (;;) {
    /* un*q < 2ud(q-1) */
    mpz_mul(t, un, q);
    mpz_sub_ui(u, q, 1); mpz_mul(u, u, ud); mpz_mul_2exp(u, u, 1);
    if (mpz_cmp(t, u) < 0) { res = 1; goto out; }
    mpz_add_ui(t, qtop, WIN);
    if (mpz_cmp(q, t) > 0) goto out;
    if (isprime(q)) {
      st_star++;
      for (long e = 1;; e++) {
        sig(s_, q, e);
        mpz_pow_ui(pe, q, e);
        mpz_mul(t, sigma, s_);
        mpz_mul(u, M, pe); mpz_mul_2exp(u, u, 1);
        if (mpz_cmp(t, u) >= 0) {
          if (!pp_Mqe(q, e, M, ps)) { add_fail("star", L, (const mpz_t *)&q, e); goto out; }
          break;
        }
        mpz_mul(t, un, s_);
        mpz_mul(u, ud, pe); mpz_mul_2exp(u, u, 1);
        if (mpz_cmp(t, u) >= 0 || e > 200) goto out;
      }
    }
    mpz_add_ui(q, q, 2);
  }
out:
  mpz_clears(D, t, u, qtop, q, s_, pe, NULL);
  for (int i = 0; i < 3; i++) mpz_clears(wlo[i], whi[i], NULL);
  return res;
}

static void print_st(FILE *o) {
  fprintf(o, "{'n': %ld, 'fam': %ld, 'qchk': %ld, 'star': %ld, 'skip': %ld, 'nfail': %ld}",
          st_n, st_fam, st_qchk, st_star, st_skip, st_nfail);
}

static int search(int L, const mpz_t M, const mpz_t sigma, const mpz_t un, const mpz_t ud, int j, const mpz_t q0);
static int search1(int L, const mpz_t M, const mpz_t sigma, const mpz_t un, const mpz_t ud, int j, const mpz_t q0) {
  st_n++;
  if (NODELIMIT && st_n >= NODELIMIT) { printf("NODELIMIT reached %ld s ", (long)(time(NULL) - t0)); print_st(stdout); printf("\n"); exit(3); }
  if (st_n % 200000 == 0) {
    sbuf b = {0};
    sb_f(&b, L);
    fprintf(stderr, "progress %ld %ld %ld %s\n", st_n, st_fam, (long)(time(NULL) - t0), b.s);
    free(b.s);
  }
  int res = 0;
  mpz_t t;
  mpz_init(t);
  mpz_mul_2exp(t, M, 1);
  if (mpz_cmp(sigma, t) >= 0) { mpz_clear(t); return 1; }
  mpz_mul_2exp(t, ud, 1);
  if (j == 0) { res = mpz_cmp(un, t) < 0; mpz_clear(t); return res; }
  mpz_clear(t);
  if (j == 1) return family(L, M, sigma, un, ud, q0);
  mpz_t q, a, b, s, pe, an, ad, g, Mn, Sn, q2;
  mpz_inits(q, a, b, s, pe, an, ad, g, Mn, Sn, q2, NULL);
  mpz_set(q, q0);
  for (;; mpz_add_ui(q, q, 2)) {
    mpz_set(a, un);
    mpz_set(b, ud);
    for (int i = 0; i < j; i++) {
      mpz_add_ui(g, q, 2 * i); mpz_mul(a, a, g);
      mpz_sub_ui(g, g, 1); mpz_mul(b, b, g);
    }
    mpz_mul_2exp(b, b, 1);
    if (mpz_cmp(a, b) < 0) { res = 1; break; }
    if (!isprime(q)) continue;
    int top3 = (j == K && mpz_cmp_ui(q, 3) == 0);
    long e = top3 ? START3 : 1;
    mpz_add_ui(q2, q, 2);
    for (;;) {
      sig(s, q, e);
      mpz_pow_ui(pe, q, e);
      mpz_mul(Mn, M, pe);
      mpz_mul(Sn, sigma, s);
      mpz_mul(an, un, q);
      mpz_sub_ui(ad, q, 1); mpz_mul(ad, ad, ud);
      mpz_gcd(g, an, ad); mpz_divexact(an, an, g); mpz_divexact(ad, ad, g);
      mpz_set(fp[L], q); fe[L] = e;
      if (search(L + 1, Mn, Sn, an, ad, j - 1, q2)) break;
      mpz_mul(an, un, s);
      mpz_mul(ad, ud, pe);
      mpz_gcd(g, an, ad); mpz_divexact(an, an, g); mpz_divexact(ad, ad, g);
      mpz_set(fp[L], q); fe[L] = e;
      if (!search(L + 1, Mn, Sn, an, ad, j - 1, q2)) { res = 0; goto out; }
      e++;
      if (STOP3 && top3 && e > STOP3) {
        printf("STOP3 reached: 3^%d done ", STOP3);
        print_st(stdout);
        printf("\n");
        fflush(stdout);
        exit(0);
      }
    }
  }
out:
  mpz_clears(q, a, b, s, pe, an, ad, g, Mn, Sn, q2, NULL);
  return res;
}

static int search(int L, const mpz_t M, const mpz_t sigma, const mpz_t un, const mpz_t ud, int j, const mpz_t q0) {
  if (L <= CKDEPTH && CK) {
    sbuf b = {0};
    sb_add(&b, "(");
    sb_f(&b, L);
    sb_add(&b, ", "); sb_mpz(&b, un);
    sb_add(&b, ", "); sb_mpz(&b, ud);
    sb_add(&b, ", "); sb_long(&b, j);
    sb_add(&b, ", "); sb_mpz(&b, q0);
    sb_add(&b, ")");
    if (!hs_has(b.s) && L <= 2) ck_reload(); /* another worker may have finished it meanwhile */
    if (hs_has(b.s)) { st_skip++; free(b.s); return 1; }
    int r = search1(L, M, sigma, un, ud, j, q0);
    if (r && (L > 0 || START3 == 1)) { /* a helper's root answer is not a proof: never record it */
      hs_add(b.s);
      fprintf(CK, "%s\n", b.s);
      fflush(CK);
    }
    free(b.s);
    return r;
  }
  return search1(L, M, sigma, un, ud, j, q0);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s K [CKFILE]\n", argv[0]); return 1; }
  K = atoi(argv[1]);
  if (K < 1 || K >= MAXK) return 1;
  const char *s3 = getenv("START3"), *p3 = getenv("STOP3");
  if (s3 && *s3) START3 = atoi(s3);
  if (p3 && *p3) STOP3 = atoi(p3);
  const char *ps_ = getenv("PSLOW");
  if (ps_ && *ps_) PSLOW = atoi(ps_);
  const char *nl = getenv("NODELIMIT");
  if (nl && *nl) NODELIMIT = atol(nl);
  t0 = time(NULL);
  sieve();
  for (int i = 0; i < MAXK; i++) { mpz_init(fp[i]); mpz_init(pc_kp[i]); }
  mpz_init(PC.sp);
  if (argc > 2) {
    CKNAME = argv[2];
    ck_reload();
    CK = fopen(CKNAME, "a");
    if (!CK) { perror(CKNAME); return 1; }
  }
  mpz_t one, three;
  mpz_init_set_ui(one, 1);
  mpz_init_set_ui(three, 3);
  const char *rt = getenv("ROOTTEST");
  if (rt && *rt) {
    /* ROOTTEST=E (estimation only, no checkpoint): run the region subtree of the root 3^E, i.e. the
     * call search([(3,E)], 3^E, sigma(3^E), 3, 2, K-1, 5) that closes the top-level loop when True */
    long E = atol(rt);
    mpz_t M, S, un, ud, q0;
    mpz_inits(M, S, un, ud, q0, NULL);
    mpz_pow_ui(M, three, E);
    sig(S, three, E);
    mpz_set_ui(un, 3); mpz_set_ui(ud, 2); mpz_set_ui(q0, 5);
    mpz_set_ui(fp[0], 3); fe[0] = E;
    int r = search(1, M, S, un, ud, K - 1, q0);
    printf("ROOTTEST 3^%ld %s ", E, r ? "True" : "False");
    print_st(stdout);
    printf(" %ld\n", (long)(time(NULL) - t0));
    for (long i = 0; i < st_nfail && i < 3; i++) printf("%s\n", fails[i]);
    return 0;
  }
  int ok = search(0, one, one, one, one, K, three);
  printf("%d %s ", K, ok ? "True" : "False");
  print_st(stdout);
  printf(" %ld\n", (long)(time(NULL) - t0));
  for (long i = 0; i < st_nfail && i < 20; i++) printf("%s\n", fails[i]);
  return 0;
}
