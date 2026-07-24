#!/usr/bin/env bash
# Build the audited-surface docs site and emit a self-contained single-page HTML site.
# Usage: docs/build.sh [--serve]
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
  echo "Serving on http://127.0.0.1:8017 (Ctrl-C to stop)"
  python3 -m http.server 8017 --bind 127.0.0.1 --directory "$HTML"
fi
