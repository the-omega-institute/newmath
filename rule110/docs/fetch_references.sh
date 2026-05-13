#!/usr/bin/env bash
# Fetch all reference PDFs into rule110/ignores/.
# PDFs are gitignored — only this script + rule110/docs/references.md enter git.
#
# Usage:
#   cd rule110 && bash docs/fetch_references.sh
#
# Idempotent: skips files already present.

set -u

OUT_DIR="${1:-ignores}"
mkdir -p "$OUT_DIR"

fetch() {
    local name="$1" url="$2"
    local path="$OUT_DIR/$name"
    if [ -f "$path" ] && [ -s "$path" ]; then
        echo "skip  $name (exists)"
        return
    fi
    if curl -sLf -o "$path" "$url"; then
        sz=$(stat -f%z "$path" 2>/dev/null || stat -c%s "$path" 2>/dev/null)
        echo "ok    $name ($sz bytes)"
    else
        rm -f "$path"
        echo "FAIL  $name <- $url"
    fi
}

# Primary
fetch cook-2004-universality.pdf                          "http://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf"
fetch martinez-2007-phases-arxiv-0706.3348.pdf            "https://arxiv.org/pdf/0706.3348"
fetch martinez-2012-solitons.pdf                          "https://content.wolfram.com/sites/13/2018/12/21-2-2.pdf"

# Concrete compiler (semantic round-trip lead)
fetch concrete-view-rule110-arxiv-0906.3248.pdf           "https://arxiv.org/pdf/0906.3248"
fetch particular-universal-ca-arxiv-0906.3227.pdf         "https://arxiv.org/pdf/0906.3227"

# Neary-Woods complexity
fetch neary-woods-small-utm-arxiv-0707.4489.pdf           "https://arxiv.org/pdf/0707.4489"
fetch cc-related-arxiv-1110.2230.pdf                      "https://arxiv.org/pdf/1110.2230"

# Glider dynamics
fetch logical-gates-arxiv-1803.05496.pdf                  "https://arxiv.org/pdf/1803.05496"
fetch ca-collider-arxiv-1609.05240.pdf                    "https://arxiv.org/pdf/1609.05240"
fetch supercolliders-arxiv-1105.4332.pdf                  "https://arxiv.org/pdf/1105.4332"

# Cyclic tag complexity
fetch ninagawa-martinez-ct-complexity-arxiv-1307.7951.pdf "https://arxiv.org/pdf/1307.7951"
fetch binary-tag-undecidability-arxiv-1312.6700.pdf       "https://arxiv.org/pdf/1312.6700"

# Class III/IV
fetch class4-vs-3-arxiv-1304.1242.pdf                     "https://arxiv.org/pdf/1304.1242"
fetch wolfram-class-iii-iv-arxiv-1208.2456.pdf            "https://arxiv.org/pdf/1208.2456"

# 2D glider gun (peripheral)
fetch minimal-glider-gun-arxiv-1709.02655.pdf             "https://arxiv.org/pdf/1709.02655"

echo ""
echo "Done. $(ls $OUT_DIR/*.pdf 2>/dev/null | wc -l) PDFs in $OUT_DIR/"
