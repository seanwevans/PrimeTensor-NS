# Six sharp centers: actual smooth frequency packets

Checkpoint: `b1663208` (reality-symmetric solenoidal packet algebra).

For each of the six centers `c_i(t)`, `t ≠ 0`, use Mathlib's finite-dimensional
`ContDiffBump` with inner radius `δ/2` and outer radius

`δ(t) = min(1, |t|)/4 > 0`.

The resulting scalar cutoff `χ_i` is smooth, compactly supported, Schwartz,
bounded between zero and one, and equals one at `c_i`. The support equals
the open radius-`δ` ball about its center. Since the norm on the finite
product `Fin 3 → ℝ` controls each coordinate, `χ_i(ξ) ≠ 0` implies precisely
the coordinatewise ball condition already covered by
`lowNormalSixCenterCoordinateBall_zero_sum_coherent`.

Therefore, if `χ_i(x) χ_j(y) χ_k(z)` can be nonzero with `x+y+z=0`, the labels
`i,j,k` must be a permutation of `0,1,2` or of `3,4,5`. No unintended
resonant triple survives compact smooth localization.

These three positive weights are substituted into the existing
`lowNormalSixPacketFourier` algebra, establishing an actual field with
pointwise zero Fourier divergence and Hermitian symmetry.

## Remaining obligations

1. Package the **vector-valued** weighted polynomial field as a Schwartz map,
   not just the scalar cutoffs.
2. Prove that the other packets (including reflected packets) vanish at each
   chosen center and hence the full field realizes `A`, `B`, `C` there.
3. Evaluate the integrated signed triad kernel for this family and prove a
   strictly nonzero value, including the Fourier phase and normalization.

No PDE nonregularity theorem is asserted by these localization results.
