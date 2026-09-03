# `proof/` — prose renderings of the Lean development

Each Lean module under `PrimeTensor/` has a matching LaTeX fragment here at
the same relative path, with `.lean` replaced by `.tex`, and a rendered PDF
beside it with `.lean` replaced by `.pdf`:

```
PrimeTensor/Depth.lean            ->  proof/Depth.tex   ->  proof/Depth.pdf
PrimeTensor/Bridge/Log/Scale.lean ->  proof/Bridge/Log/Scale.tex
```

The fragment states, in ordinary mathematical prose, what the module defines
and proves, and gives human-readable proofs of the results it establishes.
Every numbered item carries the name of the Lean declaration it corresponds
to, and each fragment ends with a table listing every declaration in the
module so that coverage is checkable by eye.

`order.txt` lists all 766 modules in import-DAG topological order — the order
the repository's `out.pdf` renders — and is the queue for this conversion.
Fragments are written in that order; anything in `order.txt` without a `.tex`
beside it is not yet converted.

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
| `order.txt` | Every module in import-DAG topological order; the order fragments are assembled in. |
| `standalone.tex` | One-fragment wrapper used to render a single module to its own PDF. |
| `build.sh` | Driver for both. Checks listings, then runs LuaLaTeX. |
| `check_fragment.py` | Checks quoted snippets, label namespacing, and local references. |
| `<Module>.tex` | The fragments, mirroring the `PrimeTensor/` tree. |

`build.sh --main` regenerates `modules.tex` from `order.txt`, keeping the
entries whose fragment exists, and `main.tex` inputs that. `modules.tex` is
generated and not committed. This is deliberate: adding a module means adding
one file and touching no shared file, so per-module branches never conflict
with one another.

## Building

Builds with **LuaLaTeX**, not pdfLaTeX. The Lean sources use 128 distinct
non-ASCII characters, and a Unicode engine lets the fragments quote them
literally rather than transliterating them; `preamble.tex` is built on
`fontspec` and `unicode-math`, and sets DejaVu Sans Mono for code, which
carries 119 of those 128 (the remaining nine have `literate` entries).

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
read exactly like the path under `PrimeTensor/`. Auxiliary files are written to
a temporary directory and discarded; only the PDF is left behind.

## Fragment rules

`check_fragment.py` enforces three things, and `build.sh` runs it before every
render, so a fragment that breaks one fails the build:

1. **Snippets are verbatim.** Every `lstlisting` block must be an excerpt of
   that module's `.lean` file, copied character for character, so a reader can
   trust the quoted code without diffing it by hand. A block that is
   deliberately not a quote opts out with `% listing:paraphrase` on the
   preceding line.
2. **Labels are namespaced by module**, as `<Module>:<name>` with `/` written
   as `:` — `Depth:def:fold`, `Bridge:Log:Scale:lem:main`. All 766 fragments
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
2. Run `./build.sh <Path>` and commit the `.tex` and the `.pdf`. Nothing else
   needs editing: `<Path>` is already listed in `order.txt`, so the aggregate
   document picks the fragment up on its next build.

One branch and one pull request per module, so that each conversion can be
reviewed against its source file on its own.
