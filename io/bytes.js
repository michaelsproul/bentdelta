// Bytes: the JavaScript lane does not support whole-file byte arrays.

function bytes_unsupported() {
  return io_fail(95);
}

io_eff(CID(Bytes.read), bytes_unsupported);
io_eff(CID(Bytes.write), bytes_unsupported);
io_eff(CID(Bytes.zeros), bytes_unsupported);
