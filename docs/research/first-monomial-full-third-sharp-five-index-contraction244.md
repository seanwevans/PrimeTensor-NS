# Actual five-index full-third physical core contraction

Baseline: `41ab72db` (bridged actual Schwartz full-third gradient and physical cores to sharp centers).

This module proves the seven-derivative Hilbert gradient weight equals its exact seven real physical coordinate factors, without discarding any index or normalizing away the Fourier phase. All four original `3+3+1` gradient axis slots are matched to their real coordinate monomials and then summed over all five axes.

An independent fivefold sum-separation identity factors each of the four coordinate monomials into products of dot contractions, giving the physical gradient total

`2 * ((dot U W * dot V r) * (dot p q)^3 + 3 * (dot U V * dot W q) * (dot p q)^2 * dot p r)`.

Adding the true `3+2+2` interpolation coefficient `6 * dot p r * (dot p q)^2 * dot r V * dot U W` yields exactly

`thirdFullSharpPhysicalOrderedCore244 z p q r U V W = 2 * thirdFullPhysicalOrderedSymbol244 p q r U V W`

for the correctly related Hilbert momentum pair. The final theorem transfers this directly to the actual moving-germ physical core at a coherent sharp center, with all center-transversality and nonzero center hypotheses explicit.

The existing corrected six-order values (-16, 28, 33, -81, -60, 0) thus predict the six twice-ordered full-core values (-32, 56, 66, -162, -120, 0) in the corrected-symbol order; the interpolation module's orientation order is (-32, 0, 66, -120, -162, 56). This module does not yet instantiate those numerals for the canonical explicit sharp fields, nor prove pointwise support sign or strict integral noncancellation.

**Verification**: local Lean 4/mathlib compilation remains required.
