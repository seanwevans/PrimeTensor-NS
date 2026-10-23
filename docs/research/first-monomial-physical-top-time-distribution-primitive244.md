# Projected physical source: genuine regular-distribution primitive

Base: `1a85736b` on `master`.

The analytic advance is the global integration-by-parts identity using
compact temporal test functions, *not* an assumption of the weak time equation.

For `R` continuous on `[a,b]`, the canonical `J(t)=∫_a^t R(s)ds`
has derivative `R(t)` at each interior point. For any smooth temporal
test `θ` supported compactly in `(a,b)`, the product `J θ`, and the
products `R θ` and `J θ'`, are globally integrable. This follows from
local integrability plus the supported-test bilinear integral lemma.
Thus the pinned mathlib global integration-by-parts theorem yields

`∫ J θ' = - ∫ R θ`.

Using the already registered regular time-distribution evaluation lemma,
this proves `∂_t T_J = T_R`. The result is then specialized to the
actual projected Navier–Stokes source pairing.

Crucially, no PDE-derived weak momentum equation is asserted here.
Deriving it and establishing a zero-distributional-derivative constant
criterion are independent remaining obligations.

Local Lean compilation is not available; the downstream Lake checks
must establish validity before committing.
