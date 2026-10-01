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

`LAWS.bend` states, and `bend PROOF.bend` checks (about two minutes), that
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

`C.restore` is the decoder the CLI runs (`vcdiff.bend`), and `B.B.list`
reads a byte string a byte at a time.

The proof is by translation validation. The encoder (`encode.bend`, after
xdelta3's default matcher) is not trusted: `check.bend` decodes its delta
and compares the result with the target (`B.eq`). If they differ, or the
delta does not decode, it substitutes a plain encoding that holds each
target byte in a window of its own. The proof shows that `B.eq` is sound
and that the decoder turns the plain encoding of any target back into that
target. Since decoding is a function, a delta that passed the check decodes
again to the same bytes. The plain encoding is nine times the target's size
and is never used in practice; it is the safety net that makes the law hold
for every input.

The proofs, in `proofs/`, build up from:

| file | what it proves |
|---|---|
| `nat.bend`, `word.bend`, `u32.bend` | Nat order and arithmetic; word arithmetic for every width (carries, no-wrap sums, bits); U32 versions |
| `array.bend` | a Data model of `Array<U32>`: reads and writes, read-after-write, writes in a perfect tree leave other slots |
| `bytes.bend` | packed bytes (four per word): `B.get`/`B.put` on the model, read-after-write, frames, depths |
| `seq.bend` | byte strings as lists: writing a list, holding a list, reading it back |
| `fallback.bend` | the plain encoding is the header and its windows, written into a new tree that holds them |
| `decode.bend` | the decoder on the plain encoding: header, each window, the prescan and decoding loops, the target buffer |
| `eq.bend` | `B.eq` is sound |
| `top.bend` | the round trip, from views of byte strings as trees and the cases of the check |

`bend <file> --verdict` rechecks with the BendTT kernel (which has a proof
in Lean). The libraries up to `fallback.bend`, and `eq.bend`, pass it. The
kernel reports a "mismatch between the TypeScript implementation and the
formalized BendTT kernel" on the last steps of `decode.bend` (evaluating the
decoder with a symbolic source length), which Bend says it will address in
a future update. Those steps check with `bend`, as does the whole law.

What is trusted: the Bend checker, the statement in `LAWS.bend` (with
`B.B.list` and `C.restore`), and the CLI around it (`main.bend` and the file
I/O in `io/bytes.c`).

## Performance

Medians against xdelta3 3.x (`-S none`; level 3, its default), on a 32-core
Linux machine:

| case | encode (xdelta3 / bentdelta) | decode | delta size |
|---|---|---|---|
| 30 MB tar, edited | 0.25 / 0.31 s | 0.12 / 0.09 s | 160366 / 161969 |
| 12 MB, identical | 0.04 / 0.09 s | 0.05 / 0.04 s | 80 / 58 |
| 158 MB shared object, new version | 6.48 / 4.28 s | 0.64 / 0.77 s | 12.86 / 12.35 MB |

Encoding includes the check (decoding the delta again and comparing).
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

- The law covers targets under 128 MiB (the plain encoding must fit a
  U32). Larger targets work, and are checked the same way, but the law does
  not speak of them.
- No secondary compression (xdelta3's default is LZMA): compare against
  `xdelta3 -S none`.
- A window with over 2^20 matches (8 MiB of matches under 8 bytes long)
  overflows the encoder's match buffer; the check then falls back to the
  plain encoding.
