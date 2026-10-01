import Base
import ./bytes.bend as B
import ./vcdiff.bend as V
import ./check.bend as C

# bentdelta: a VCDIFF (RFC 3284) delta encoder and decoder, compatible with
# xdelta3.
#
#   bentdelta -e [-s source] target delta     make a delta
#   bentdelta -d [-s source] delta target     apply a delta

# Files as byte arrays
# ====================

def Bytes.read(path: String) -> IO(Result<&1, &1, U32 & String, U32 & Array<U32>>):
  import "./io/bytes.c"
  import "./io/bytes.js"

def Bytes.write(path: String, len: U32, data: Array<U32>) ->
  IO(Result<&1, &1, U32 & String, Unit>):
  import "./io/bytes.c"
  import "./io/bytes.js"

def Bytes.zeros(n: U32) -> IO(Result<&1, &1, U32 & String, Array<U32>>):
  import "./io/bytes.c"
  import "./io/bytes.js"

def load.k(la: U32 & Array<U32>) -> B.Bytes:
  (len, a) = la
  B.Bytes{len, a}

def load(path: String) -> IO(B.Bytes):
  do IO<B.Bytes>:
    la : U32 & Array<U32> <- IO.try(U32 & Array<U32>, Bytes.read(path))
    return load.k(la)

def save(path: String, b: B.Bytes) -> IO(Unit):
  match b:
    case B.Bytes{len, buf}:
      IO.try(Unit, Bytes.write(path, len, buf))

def empty() -> B.Bytes:
  B.Bytes{0, [0 : U32^0n]}

# Command line
# ============

type Cmd is Data:
  Cmd{mode: U32, src: Maybe<&2, String>, files: List<&2, String>}

def usage() -> String:
  "usage: bentdelta -e [-s source] target delta\n       bentdelta -d [-s source] delta target"

def u32.pick(c: Bool, a: U32, b: U32) -> U32:
  Bool.pick(U32, c, a, b)

def cmd.go(args: List<&2, String>, +mode: U32, +want_src: Bool,
  +src: Maybe<&2, String>, +files: List<&2, String>) -> Cmd:
  match args:
    case Nil{}:
      Cmd{mode, src, List.reverse(&2, String, files)}
    case Con{+a, rest}:
      +is_e = String.eq(a, "-e")
      +is_d = String.eq(a, "-d")
      +is_p = String.eq(a, "--plain")
      +is_s = String.eq(a, "-s")
      +plain = Bool.not(is_e || is_d || is_s || is_p)
      +mode2 = u32.pick(is_e, 1, u32.pick(is_d, 2, u32.pick(is_p, 3, mode)))
      +src2 = Bool.pick(Maybe<&2, String>, want_src, Some{a}, src)
      +files2 = Bool.pick(List<&2, String>, plain && Bool.not(want_src), a <> files,
        files)
      cmd.go(rest, mode2, is_s, src2, files2)

def strs.share(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> strs.share(t)

def cmd.parse(args: List<&2, String>) -> Cmd:
  match args:
    case Nil{}:
      Cmd{0, None{}, []}
    case Con{prog, rest}:
      cmd.go(rest, 0, False{}, None{}, [])

# Running
# =======

def src.load(m: Maybe<&2, String>) -> IO(B.Bytes):
  match m:
    case None{}:
      IO.pure(B.Bytes, empty())
    case Some{path}:
      load(path)

def run.decoded(out: String,
  r: B.Bytes & (B.Bytes & Result<&1, &1, U32, B.Bytes>)) -> IO(Unit):
  match r:
    case Tuple{s, Tuple{d, Done{t}}}:
      save(out, t)
    case Tuple{s, Tuple{d, Fail{e}}}:
      IO.die(Unit, 1, "bentdelta: " ++ V.E.show(e))

def run.decode.k(s: B.Bytes, out: String, r: B.Bytes & U32) -> IO(Unit):
  (d, +n) = r
  do IO<Unit>:
    buf : Array<U32> <- IO.try(Array<U32>, Bytes.zeros(n))
    run.decoded(out, V.decode.into(s, d, buf))

def run.decode(src: Maybe<&2, String>, delta: String, out: String) -> IO(Unit):
  do IO<Unit>:
    s : B.Bytes <- src.load(src)
    d : B.Bytes <- load(delta)
    run.decode.k(s, out, V.decode.size(d))

def run.plain(out: String, r: B.Bytes & B.Bytes) -> IO(Unit):
  (t, d) = r
  save(out, d)

def run.encode.go(plain: Bool, s: B.Bytes, t: B.Bytes, out: String) -> IO(Unit):
  match plain:
    case False{}:
      save(out, C.encode(s, t))
    case True{}:
      run.plain(out, C.fallback(t))

def run.encode(+mode: U32, src: Maybe<&2, String>, tgt: String, out: String) ->
  IO(Unit):
  do IO<Unit>:
    s : B.Bytes <- src.load(src)
    t : B.Bytes <- load(tgt)
    run.encode.go(U32.is_eq(mode, 3), s, t, out)

def run.mode(dec: Bool, +mode: U32, src: Maybe<&2, String>, a: String,
  b: String) -> IO(Unit):
  match dec:
    case True{}:
      run.decode(src, a, b)
    case False{}:
      run.encode(mode, src, a, b)

def run.files(+mode: U32, src: Maybe<&2, String>, files: List<&2, String>) ->
  IO(Unit):
  match files:
    case Con{a, Con{b, Nil{}}}:
      run.mode(U32.is_eq(mode, 2), mode, src, a, b)
    case other:
      IO.die(Unit, 2, usage())

def run.cmd(c: Cmd) -> IO(Unit):
  match c:
    case Cmd{mode, src, files}:
      run.files(mode, src, files)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run.cmd(cmd.parse(strs.share(args)))
