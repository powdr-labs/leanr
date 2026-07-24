#!/usr/bin/env bash
# Build the audited-surface docs site and emit a self-contained single-page HTML site.
# Usage: docs/build.sh [--serve]      (override the start port with PORT=NNNN)
set -euo pipefail
cd "$(dirname "$0")/.."             # repo root

OUT=docs/_out
HTML="$OUT/html-single"

# Render the trust-map figure from its Graphviz source (skips if `dot` is absent).
if command -v dot >/dev/null 2>&1; then
  dot -Tsvg docs/assets/trust.dot -o docs/assets/trust.svg
fi

lake build docs
rm -rf "$OUT"
lake exe docs --output "$OUT"

# Ship the figure alongside the page (Verso references it relatively).
cp docs/assets/trust.svg "$HTML/"

echo "Wrote $HTML/index.html"
if [[ "${1:-}" == "--serve" ]]; then
  # Pick the first free port at or above the requested one (default 8017), so a
  # leftover server doesn't make this fail with "Address already in use".
  PORT=$(python3 - "${PORT:-8017}" <<'PY'
import socket, sys
p = int(sys.argv[1])
while p < 65536:
    with socket.socket() as s:
        if s.connect_ex(("127.0.0.1", p)) != 0:
            print(p); break
    p += 1
else:
    sys.exit("no free port found")
PY
)
  echo "Serving on http://127.0.0.1:$PORT (Ctrl-C to stop)"
  exec python3 -m http.server "$PORT" --bind 127.0.0.1 --directory "$HTML"
fi
