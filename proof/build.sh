#!/usr/bin/env bash
# Render prose fragments under proof/ to PDF.
#
#   ./build.sh Depth              -> proof/Depth.pdf
#   ./build.sh Bridge/Log/Scale   -> proof/Bridge/Log/Scale.pdf
#   ./build.sh --all              -> one PDF per fragment
#   ./build.sh --main             -> proof/main.pdf (the aggregate document)
#
# Module names are given relative to proof/, without the .tex extension,
# and mirror the paths under PrimeTensor/.
set -euo pipefail

cd "$(dirname "$0")"
AUX="$(mktemp -d)"
trap 'rm -rf "$AUX"' EXIT

render() {
  local module="$1"
  if [ ! -f "$module.tex" ]; then
    echo "build.sh: no such fragment: $module.tex" >&2
    return 1
  fi
  echo "  $module.tex -> $module.pdf"
  local jobname
  jobname="$(printf '%s' "$module" | tr '/' '_')"
  for _ in 1 2; do
    pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory "$AUX" -jobname "$jobname" \
      "\\def\\ProofFile{$module}\\input{standalone.tex}" >/dev/null
  done
  mkdir -p "$(dirname "$module.pdf")"
  mv "$AUX/$jobname.pdf" "$module.pdf"
}

render_main() {
  echo "  main.tex -> main.pdf"
  for _ in 1 2; do
    pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory "$AUX" main.tex >/dev/null
  done
  mv "$AUX/main.pdf" main.pdf
}

case "${1:-}" in
  "")
    echo "usage: build.sh <module> | --all | --main" >&2
    exit 2
    ;;
  --main)
    render_main
    ;;
  --all)
    while IFS= read -r f; do
      render "${f#./}"
    done < <(find . -name '*.tex' \
               ! -name 'main.tex' ! -name 'preamble.tex' \
               ! -name 'standalone.tex' | sed 's/\.tex$//' | sort)
    ;;
  *)
    for m in "$@"; do render "${m%.tex}"; done
    ;;
esac
