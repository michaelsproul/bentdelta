// Bytes: whole files as word arrays, four bytes to a U32 word, little-endian
// (bytes.bend). On a little-endian host the words are the file's bytes, so
// loading and storing are plain copies.
// =====

#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <unistd.h>

// The depth of the smallest power-of-two word array holding n bytes.
static u32 bytes_depth(u64 n) {
  u64 w = (n + 3) / 4;
  u32 d = 0;
  while (((u64)1 << d) < w) {
    d += 1;
  }
  return d;
}

// Backs the heap with transparent huge pages: byte arrays are large, and
// 4 KiB faults dominate otherwise. Only a hint; failure is harmless.
static void bytes_huge(void) {
  static int done = 0;
  if (!done) {
    done = 1;
    madvise(CORPUS, corpus_size, MADV_HUGEPAGE);
  }
}

#ifdef CID(Bytes.read)

Term bytes_read_run(Env e, Term* f, IoWork* w) {
  bytes_huge();
  u64   plen = 0;
  char* path = io_cstr(e, f[0], &plen);
  int   fd   = open(path, O_RDONLY);
  free(path);
  if (fd < 0) {
    return io_fail(e, (u32)errno, NULL);
  }
  struct stat st;
  if (fstat(fd, &st) != 0) {
    int c = errno;
    close(fd);
    return io_fail(e, (u32)c, NULL);
  }
  u64 n = (u64)st.st_size;
  if (n > ((u64)1 << 31)) {
    close(fd);
    return io_fail(e, EFBIG, "file too large (over 2 GiB)");
  }
  u32 d   = bytes_depth(n);
  u64 loc = heap_alloc(e, buf_wcls(d));
  if (err_seen(e.mem)) {
    close(fd);
    return io_fail(e, ENOMEM, "out of memory");
  }
  unsigned char* dst = (unsigned char*)(e.mem + loc);
  u64 at = 0;
  while (at < n) {
    ssize_t k = read(fd, dst + at, (n - at) < (1u << 30) ? (size_t)(n - at) : (1u << 30));
    if (k <= 0) {
      break;
    }
    at += (u64)k;
  }
  close(fd);
  memset(dst + at, 0, ((u64)4 << d) - at);
  Term arr = term_blk(false, d, loc);
  return io_done(e, io_tup(e, (Term)(u32)at, arr));
}

static void __attribute__((constructor)) bytes_read_use(void) {
  io_eff(CID(Bytes.read), bytes_read_run, 0);
}

#endif

#ifdef CID(Bytes.zeros)

// A word array holding n zero bytes, cleared with memset rather than a slot
// at a time.
Term bytes_zeros_run(Env e, Term* f, IoWork* w) {
  bytes_huge();
  u64 n   = (u32)f[0];
  u32 d   = bytes_depth(n);
  u64 loc = heap_alloc(e, buf_wcls(d));
  if (err_seen(e.mem)) {
    return io_fail(e, ENOMEM, "out of memory");
  }
  memset((u32*)(e.mem + loc), 0, sizeof(u32) << d);
  return io_done(e, term_blk(false, d, loc));
}

static void __attribute__((constructor)) bytes_zeros_use(void) {
  io_eff(CID(Bytes.zeros), bytes_zeros_run, 0);
}

#endif

#ifdef CID(Bytes.write)

Term bytes_write_run(Env e, Term* f, IoWork* w) {
  u64   plen = 0;
  char* path = io_cstr(e, f[0], &plen);
  u64   n    = (u32)f[1];
  Term  arr  = f[2];
  u32   d    = blk_cls(arr);
  if (term_tag(arr) != TAG_BUF || n > ((u64)4 << d)) {
    free(path);
    term_sink(e, arr);
    return io_fail(e, EINVAL, "bad byte array");
  }
  const unsigned char* src = (const unsigned char*)(e.mem + blk_loc(e.mem, arr));
  int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  free(path);
  if (fd < 0) {
    int c = errno;
    term_sink(e, arr);
    return io_fail(e, (u32)c, NULL);
  }
  u64 at  = 0;
  int bad = 0;
  while (at < n) {
    ssize_t r = write(fd, src + at, (n - at) < (1u << 30) ? (size_t)(n - at) : (1u << 30));
    if (r <= 0) {
      bad = errno ? errno : EIO;
      break;
    }
    at += (u64)r;
  }
  if (close(fd) != 0 && !bad) {
    bad = errno;
  }
  term_sink(e, arr);
  if (bad) {
    return io_fail(e, (u32)bad, NULL);
  }
  return io_done(e, term_pak(CID(Unit), 0));
}

static void __attribute__((constructor)) bytes_write_use(void) {
  io_eff(CID(Bytes.write), bytes_write_run, 0);
}

#endif
