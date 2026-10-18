# Exact positive-sector Fourier triple spectra

Checkpoint: `044110e8` (single-window isolation). The parent module proves the
complete third physical H³ commutator equals twice the sum of six disjoint
positive coherent sector integrals of the unphased imaginary Fourier kernel.

The six positive label pairs for the two free momenta `(p,r)` are:

| n | first p-label | middle q-label | last r-label |
|---|---|---|---|
| 0 | 0 | 1 | 2 |
| 1 | 2 | 1 | 0 |
| 2 | 1 | 0 | 2 |
| 3 | 2 | 0 | 1 |
| 4 | 1 | 2 | 0 |
| 5 | 0 | 2 | 1 |

Their phase factors are, by window label, `1`, `1`, `I`. Hence their
ordered cubic phase product is exactly `I` for every `n`, not an assumption
of cyclic invariance of the remaining multiplier.

## Mathematical result

Fix `ρ > 0`, `ρ ≤ lowNormalSixCenterSeparationRadius 1` and a sector radius
`δ` with `2δ ≤ 1`. If the actual Fourier-pair frequency lies in the `n`th
positive coherent sector and its actual real-velocity triple spectral mass is
nonzero, then the three frequencies `p`, `q=-p-r`, `r` lie in the unique
radius-`ρ` neighborhoods of the labels listed above. The argument uses:

1. The proved distinct-center unit gap to identify the first and third
   Fourier windows from the axis-sup sector, since `ρ + δ ≤ 1` and both
   frequency neighborhoods have strict radius inequalities.
2. Nonvanishing of all three actual spectral vectors, derived from nonzero
   triple mass, to classify the middle frequency with no assumption about
   where it lies.
3. The existing twelve-center exact momentum classification to force the
   remaining middle label to be the unique positive label.
4. The committed three primary-label single-window Fourier equalities,
   preserving the moving fixed-center polynomial transverse germ and its
   complex phase.

The penultimate theorem identifies the literal complex Fourier triple component
from the physical real Schwartz velocity with the corresponding product of
three isolated windowed polarization-germ components, for arbitrary ordered
coordinate labels. The final theorem multiplies that exact identity by the
actual seven-derivative frequency weight to identify each of the literal
3+3+1 physical gradient slots. The 3+2+2 interpolation channel and the
full sum remain to be contracted before any integrated sign conclusion.

**Scope:** These theorems are conditional on nonzero *actual* triple spectral
mass. They do not yet establish a strict sign of the full Schwartz integral;
they do not identify the entire seven-derivative physical multiplier with an
earlier sharp-order polynomial; and they do not claim an H³ Navier–Stokes
continuation theorem.
