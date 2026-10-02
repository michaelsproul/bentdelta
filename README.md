# bentdelta

A VCDIFF (RFC 3284) delta encoder and decoder written in
[Bend](https://github.com/HigherOrderCO/Bend) 2, compatible with xdelta3,
with a machine-checked round-trip law.

```
bend main.bend -o bentdelta

bentdelta -e [-s source] target delta     make a delta
bentdelta -d [-s source] delta target     apply a delta
```

Deltas from `bentdelta -e` decode with `xdelta3 -d`, and deltas from
`xdelta3 -e -S none` (no secondary compression) decode with `bentdelta -d`.

## The law

`LAWS.bend` states, and `bend PROOF.bend` checks (about 22 minutes), that
for any source and any target under 128 MiB, decoding the delta that the
encoder makes, against the same source, gives back exactly the target's
bytes:

```
law roundtrip:
  for src: B.Bytes
  for tgt: B.Bytes
  for small: {U32.is_lt(B.B.len(tgt), 134217728) == True{} : Bool}
  {C.restore(src, C.encode(src, tgt)) == Done{B.B.list(tgt)}
    : Result<&1, &1, U32, List<&2, U32>>}
```

`C.encode` is the encoder the CLI runs (`encode.bend`, through
`codec.bend`), `C.restore` the decoder (`vcdiff.bend`), and `B.B.list`
reads a byte string a byte at a time.

The proof is about the encoder itself: nothing checks its output at run
time. Each step of the encoder (`encode.bend`, after xdelta3's default
matcher) is mirrored by a function on trees, Data copies of the arrays it
works on, and each mirror is shown to compute what the code does. Facts
about the mirrors then give the delta's shape: a header, then windows,
each of which says (`proofs/spec`) how to rebuild its part of the target
from the source and the target before it. The matcher only buffers matches
whose bytes agree, the emitter writes the three sections of a window as
the spec reads them, and the parallel tasks' outputs join in order. On the
other side, the decoder turns any delta of such windows back into the
target. The bound on the target keeps every position and the delta's
length below 2^31.

The proofs, in `proofs/` (the `.bp` files are the sources; `tools/bpp.py`
expands their rewriting directives into the `.bend` files), build up from:

| file | what it proves |
|---|---|
| `nat`, `word`, `u32` | Nat order and arithmetic; word arithmetic for every width (carries, no-wrap sums, bits); U32 versions |
| `array`, `bytes`, `seq`, `words`, `bits`, `copy` | Data models of `Array<U32>` and packed bytes: reads, writes, words and their bytes, copies, fills and moves |
| `varint`, `adler`, `umod` | varints written and read back; Adler-32 reads only its range; `U32.mod` |
| `spec` | what a window of a delta says, and when it rebuilds a target's bytes |
| `sem`, `dec`, `dwin`, `dtop` | the decoder: its writes, a window's instructions, a window, a whole delta |
| `ctab` | the encoder's opcodes fit the code table |
| `match` | the matcher's byte comparisons count bytes that agree |
| `emit`, `einst` | the emitter writes a window's three sections as the spec reads them |
| `settle`, `segm` | buffered matches settle into instructions; the source segment |
| `scan` | the string matcher: every match it buffers holds |
| `wstart`, `wwrite`, `wfin`, `wspec` | a window: its start, its bytes, its end, and what it leaves for the next |
| `wloop`, `wpar` | runs of windows, and the parallel tasks that encode them |
| `etop` | the encoder: the header, the index, the window count, the bounds, and its delta decoding to the target |
| `top` | the round trip |

`bend <file> --verdict` rechecks a file with the BendTT kernel (which has a
proof in Lean); the proofs here are checked with `bend`.

What is trusted: the Bend checker, the statement in `LAWS.bend` (with
`B.B.list`, `C.encode` and `C.restore`), and the CLI around it
(`main.bend` and the file I/O in `io/bytes.c`).

## Performance

Medians against xdelta3 3.0.11 (`-S none`; level 3, its default), on a 32-core
Linux machine:

| case | encode (xdelta3 / bentdelta) | decode | delta size |
|---|---|---|---|
| 30 MB tar, edited | 0.25 / 0.28 s | 0.12 / 0.10 s | 160366 / 161969 |
| 12 MB, identical | 0.04 / 0.06 s | 0.05 / 0.04 s | 80 / 58 |
| 158 MB shared object, new version | 6.51 / 4.04 s | 0.73 / 0.76 s | 12.86 / 12.35 MB |

The encode times above were measured when the encoder also decoded its
delta to check it; without that check (now that it is proven) encoding takes
about the decode time less.

Targets of 8 windows (56 MiB) or more are encoded in parallel, eight tasks
with their own copies of the inputs; smaller ones gain nothing from it.

Byte strings are packed four bytes to a `U32`, so files load and store
with a plain copy, and copies move whole words. The encoder follows
xdelta3's: 8 MiB windows, a rolling 9-byte checksum over the source, 4-byte
target matches with short chains, runs, lazy matching, its instruction
optimizer and code-table choices, and source segments that slide with the
target (so xdelta3's decoder, holding 64 MiB of source, reads ours as fast
as its own).

## Tests

```
bash tests/interop.sh          # round trips with both decoders, 15 cases
bend tests/bytes_test.bend     # randomized tests of the byte primitives
```

## Limits

- The law covers targets under 128 MiB (the proof bounds the delta's
  length by 14 bytes per target byte, which must stay below 2^31). Larger
  targets work, but the law does not speak of them.
- No secondary compression (xdelta3's default is LZMA): compare against
  `xdelta3 -S none`.
