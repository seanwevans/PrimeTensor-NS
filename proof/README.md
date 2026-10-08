# `proof/` — prose renderings of the Lean development

This directory contains selected prose renderings, not a complete mirror of
all Lean modules. At the `1c4104d6` audit checkpoint there are 2,383 project
modules and 22 prose fragments. A missing fragment means the source has not
yet been rendered here; it says nothing about whether the Lean module builds.

Most fragments use the same relative path as their source. Explicit historical
exceptions live in `source-map.json`: `MulRat.tex` renders `Mul/Rat.lean` while
retaining its existing fragment name, labels, and PDF path.

`order.txt` is generated from the current source graph. It lists all existing
project modules in dependency order over existing project import edges.
Excluded modules and missing imports are recorded separately in
`tools/audit/known-source-gaps.json`; appearing in this index is not a build
certification. The header records the generating revision and source digest.
It does not establish the provenance of an older `out.pdf`.

```bash
python3 proof/generate_index.py          # refresh after Lean source changes
python3 proof/generate_index.py --check  # check without rewriting
python3 proof/check_fragment.py --all
```

A fragment states what its source defines and proves, with verbatim Lean
excerpts and human-readable explanations. Only existing fragments are included
in the aggregate document. No PDF generation is required to run these checks.

## Fragments are `\input`-able

A per-module `.tex` file is a bare fragment: it opens at `\section` level and
carries no `\documentclass`, no preamble and no `document` environment. It is
pulled into a larger document with a plain `\input` and nothing else:

```latex
\input{Depth}
\input{Bridge/Log/Scale}
```

Fragments therefore may not load packages or define macros. Anything shared
belongs in `preamble.tex`, which supplies the theorem environments, the Lean
listing style, and the notation macros (`\Depth`, `\Axis`, `\fold`, `\leanfile`,
`\lean`, ...).

## Layout

| File | Role |
| --- | --- |
| `preamble.tex` | Shared packages, theorem environments, notation macros. No `\documentclass`. |
| `main.tex` | The aggregate document. Its `\input` list is generated, so it is never edited by hand. |
| `order.txt` | Generated inventory, ordered by existing project imports. |
| `generate_index.py` | Regenerates/checks the index and emits mapped fragment inputs. |
| `source-map.json` | Explicit fragment-to-source path exceptions. |
| `standalone.tex` | One-fragment wrapper used to render a single module to its own PDF. |
| `build.sh` | Driver for both. Checks listings, then runs LuaLaTeX. |
| `check_fragment.py` | Checks quoted snippets, label namespacing, and local references. |
| `<Module>.tex` | The fragments, mirroring the `PrimeTensor/` tree. |

`build.sh --main` regenerates `modules.tex` from `order.txt`, keeping the
entries whose fragment exists (including mapped historical names), and `main.tex` inputs that. `modules.tex` is
generated and not committed. Regenerate the source index when Lean sources change; adding prose for an already indexed module requires only its fragment and any explicit path mapping.

## Building

Builds with **LuaLaTeX**, not pdfLaTeX. Lean sources contain Unicode characters. A Unicode engine lets fragments quote them literally; `preamble.tex` uses `fontspec` and `unicode-math`, with DejaVu Sans Mono for code.

Lean snippets go in a `leancode` environment, which is fvextra's `Verbatim` —
deliberately **not** `listings`. Under LuaLaTeX, `listings` reorders
characters adjacent to non-ASCII ones: it sets `(δ a b` as `δ( a b` and
`‖x‖` as `‖‖x`, silently misquoting the source. `Verbatim` gives up keyword
colouring and gets the characters right, which is the trade this document
needs; `fvextra` adds line breaking so a long Lean signature wraps rather
than running off the page.

On Debian/Ubuntu:

```bash
apt-get install texlive-latex-base texlive-latex-recommended \
    texlive-latex-extra texlive-fonts-recommended texlive-luatex \
    fonts-dejavu-core fonts-lmodern
```

```bash
cd proof
./build.sh Depth              # -> proof/Depth.pdf
./build.sh Bridge/Log/Scale   # -> proof/Bridge/Log/Scale.pdf
./build.sh --all              # one PDF per fragment
./build.sh --main             # -> proof/main.pdf, the aggregate document
```

Module names are given relative to `proof/` and without the extension, so they
normally match the path under `PrimeTensor/`; `source-map.json` records exceptions. Auxiliary files are written to
a temporary directory and discarded; only the PDF is left behind.

## Fragment rules

`check_fragment.py` enforces three things, and `build.sh` runs it before every
render, so a fragment that breaks one fails the build:

1. **Snippets are verbatim.** Every `leancode` block must be an excerpt of
   that module's `.lean` file, copied character for character, so a reader can
   trust the quoted code without diffing it by hand. A block that is
   deliberately not a quote opts out with `% listing:paraphrase` on the
   preceding line.
2. **Labels are namespaced by module**, as `<Module>:<name>` with `/` written
   as `:` — `Depth:def:fold`, `Bridge:Log:Scale:lem:main`. All included fragments
   share one document, and bare labels would collide.
3. **References stay inside the fragment.** A fragment is rendered both alone
   and inside `main.tex`; a `\ref` into another fragment is undefined in the
   first case. Cite another module by file name instead — write
   `\texttt{PrimeTensor/Depth.lean}`, not `\ref{Depth:...}`.

```bash
python3 check_fragment.py Depth     # one module
python3 check_fragment.py --all     # every fragment
```

One further convention, not machine-checked: keep at most one Lean name in a
theorem's bracketed title. Lean identifiers are long unbreakable typewriter
words, and two of them in a title overflow the measure; list the rest in the
body.

## Adding a module

1. Write `proof/<Path>.tex` as a fragment, mirroring `PrimeTensor/<Path>.lean`.
2. Run `python3 generate_index.py --check`; regenerate the index if sources changed.
3. Run `python3 check_fragment.py <Path>`. Render with `./build.sh <Path>` when a PDF is wanted; commit the fragment and any deliberately regenerated PDF.

One branch and one pull request per module, so that each conversion can be
reviewed against its source file on its own.
