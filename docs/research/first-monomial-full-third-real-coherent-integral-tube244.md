# Full-third real Schwartz velocity: exact 12-sector Fourier integral tube

**Base:** `9f132077` — coherent support of the actual recovered real Schwartz velocity.

This increment moves from the support theorem for the norm of the complete
three-frequency Fourier vector to a universal, complex-valued trilinear
Fourier integrand on the same `Axis Depth.three` carrier. The two free
momenta are `p` and `r`; the third is **exactly** `q=-p-r`.

The orbit is the twelve *coherent* ordered pairs (six simultaneous
permutations of `p,q,r`, and six reflected counterparts), indexed via the
existing theorem `lowNormalQuarterCoherentLabels_classify` rather than by
informal combinatorial symmetry. Its center set is finite and compact.

For every desired positive tube radius `δ`, choose

`ρ = min(δ, lowNormalSixCenterSeparationRadius 1) / 2`.

This is a positive width satisfying both quantitative nonresonance and
`ρ ≤ δ`. At this width, EVERY triple of nonzero Fourier amplitudes of the
constructed real Schwartz velocity lies inside the closed radius-`δ`
coherent tube, independent of which real polarizations `A,B,C` are used.

A general complex trilinear multiplier is defined by

`K_w(p,r) = Σ_a Σ_b Σ_c w(a,b,c,p,r) U_a(p) U_b(-p-r) U_c(r)`,

where `U` is **the actual Fourier spectrum** of the constructed real velocity.
It vanishes identically off the tube. For any **integrable** instance of
this multiplier (including the intended Schwartz-times-polynomial cases once
their analytic hypotheses are proved), its complete integral over the full
momentum plane equals the integral of its indicator-restricted kernel in the
coherent tube. This is an exact measure-theoretic equality (not a pointwise
approximation, an assumed Jacobian, or an estimate).

## Main declarations

- `thirdFullAxisCoherentPairCenterSet_isCompact244`
- `thirdFullAxisCoherentPairCenterSet_mem244`
- `thirdFullAxisRealSchwartz_exists_width_in_coherent_tube244`
- `thirdFullAxisRealSchwartzTripleComponent_zero_of_mass244`
- `thirdFullAxisRealSchwartzWeightedTrilinear_zero_off_tube244`
- `thirdFullAxisRealSchwartzWeightedTrilinear_integral_eq_tube244`
- `thirdFullAxisRealSchwartzWeightedTrilinear_exists_integral_tube244`

## Exact limits

The multiplier `w` is abstract. The **next** step must identify the actual
full-gradient and interpolation 7-derivative multiplier from
`fullThirdSchwartzFourierCoefficient244` with this trilinear form, preserving
all physical constants and component contractions. Then one must prove the
signed total over all 12 sectors (not only one local ball). Neither that
identification nor signed noncancellation is claimed here. No Navier–Stokes
continuation theorem follows from this static support result.

## Build/audit

Run the registration script, `python3 proof/generate_index.py`, its
`--check`, the fragment checker, individual Lean compilation, the theorem
axiom audit, and `lake build` before committing. The assistant-side archive
has not been typechecked with Lean or mathlib.
