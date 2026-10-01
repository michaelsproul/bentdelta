#!/usr/bin/env bash
# tools/bps.sh proofs/x.bp: a fast draft check of x.bp against stubs of the
# proof files it imports (tools/stub.py; run `tools/stub.py` on them first).
# Proves nothing: check with tools/bp.sh before relying on it.
set -e
D=$(dirname "$0")
f="$1"
out="${f%.bp}.bend"
stub="${f%.bp}.stub.bend"
python3 "$D/bpp.py" "$f" "$out"
python3 "$D/bendsort.py" "$out"
sed -E 's#^import \./([a-z0-9_]+)\.bend as#import ./stub/\1.bend as#' "$out" > "$stub"
r=$(bend "$stub" 2>&1 || true)
rm -f "$stub"
if echo "$r" | grep -q "^Error: [0-9]* defs rely on unsafe"; then
  echo "STUB CHECK OK"
else
  # the error, without the context's hypotheses
  echo "$r" | awk '/^Context:/{c=1; next} /^Location:/{c=0} !c' | cut -c1-"${WIDTH:-800}" | head -c "${LIMIT:-3000}"
fi
