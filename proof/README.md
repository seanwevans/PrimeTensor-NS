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

Only `Depth` is written so far. The rest of the tree is not yet converted.

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
| `main.tex` | The aggregate document. Add a module by adding one `\input` line. |
| `standalone.tex` | One-fragment wrapper used to render a single module to its own PDF. |
| `build.sh` | Driver for both. |
| `<Module>.tex` | The fragments, mirroring the `PrimeTensor/` tree. |

## Building

Requires a TeX installation with `amsmath`, `listings`, `hyperref` and
`lmodern` (on Debian/Ubuntu: `texlive-latex-base texlive-latex-recommended
texlive-latex-extra texlive-fonts-recommended lmodern`).

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

## Adding a module

1. Write `proof/<Path>.tex` as a fragment, mirroring `PrimeTensor/<Path>.lean`.
2. Add `\input{<Path>}` to `main.tex`, in dependency order. The repository's
   `out.pdf` renders the import DAG in topological order (766 modules, `Depth`
   first); that listing is the order `main.tex` follows.
3. Run `./build.sh <Path>` and commit the `.tex` and the `.pdf`.

One branch and one pull request per module, so that each conversion can be
reviewed against its source file on its own.
