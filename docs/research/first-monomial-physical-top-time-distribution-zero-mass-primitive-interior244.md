# Time distributions: compact primitive for zero-mean tests with interior bounds

Base: `62478a9e`.

Given a smooth real test `θ` supported within the strictly interior interval
`(ℓ,r) ⊂ (a,b)` with total integral zero, define

`P(t) = ∫ s in ℓ..t, θ(s)`.

The pinned mathlib theorem `Continuous.integral_hasStrictDerivAt` implies
`P'(t) = θ(t)` at all real times. The 1D characterization
`contDiff_infty_iff_deriv` and the smoothness of `θ` give global smoothness.

Because θ vanishes outside `(ℓ,r)`, the integral is zero for `t ≤ ℓ`. For
`t ≥ r`, additive interval integration and `∫ θ = 0` again give zero. Thus
`support P ⊆ [ℓ,r]`, hence also its topological support is contained in the
same closed interval. It follows that P is compactly supported and supported
in `(a,b)`, so it can be bundled as the required `TestFunction`. The
`TestFunction.lineDerivCLM` value is precisely θ.

This proves the constructive primitive **under an explicitly quantified
interior support bound**, not yet its existence for every test. The next proof
is the compactness/topology step: given `IsCompact (tsupport θ)` and
`tsupport θ ⊆ Ioo a b`, choose `ℓ,r` such that
`a < ℓ < r < b` and `tsupport θ ⊆ Ioo ℓ r`. It should then feed this theorem
to remove the last analytic premise from the homogeneous distribution kernel.

No physical momentum distributional PDE is deduced merely from the pointwise
old PDE. That interchange remains a separate obligation.
