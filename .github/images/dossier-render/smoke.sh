#!/usr/bin/env bash
set -euo pipefail

need() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

for cmd in python3 git curl quarto node npm make4ht pdflatex dvisvgm; do
  need "$cmd"
done

quarto_version="$(quarto --version | head -n1)"
if [ "$quarto_version" != "1.9.37" ]; then
  echo "unexpected Quarto version: $quarto_version" >&2
  exit 1
fi

node_version="$(node --version)"
case "$node_version" in
  v22.*) ;;
  *)
    echo "unexpected Node version: $node_version" >&2
    exit 1
    ;;
esac

npm --version >/dev/null
python3 --version
git --version
curl --version | head -n1
make4ht --version | head -n1
pdflatex --version | head -n1
dvisvgm --version | head -n1
