# Z³ finite Galerkin: closing the Picard restart seam

Base: `2c4388c407bc661e5cbf2d2069eccbc9cc2aebb1`.

The earlier theorem constructs a genuine preterminal solution `alpha`, its endpoint state `beta b`, and a restarted Picard solution `beta` of the **same complete Leray-Galerkin finite field** `F_S`. The assembled path `gamma` is `alpha` for `t < b` and `beta` for `t ≥ b`. At this point the open-side ODEs were established, but `HasDerivAt gamma (F_S (gamma b)) b` was not.

## Mathematical seam proof

The preterminal endpoint estimate gives `dist (alpha t) (beta b) ≤ 51000 dist t b`, so `gamma` approaches `gamma b` from the left. On `Ioo a b`, the actual finite field equation gives `deriv gamma t = F_S (gamma t)`. Since `F_S` is continuously differentiable as a real finite-dimensional polynomial map, its composition with `gamma` tends to `F_S (gamma b)` from the left. The mathlib endpoint extension theorem `hasDerivWithinAt_Iic_of_tendsto_deriv` yields the left derivative at `b`.

The restarted Picard solution has an actual derivative at `b` from the open interval `Ioo (b-delta) (b+delta)`. Since `gamma = beta` on `Ici b`, it yields the matching right derivative. `HasDerivWithinAt.union` and `Iic_union_Ici` then yield the full two-sided derivative of `gamma` at `b`.

No strict endpoint Wiener inequality, endpoint derivative, new global ODE trajectory, or altered vector field is assumed. The strong continuation theorem now constructs a pasted path satisfying the exact ODE at *every* `t ∈ Ico a (b+delta)`, including `b`, while retaining the initial state and endpoint analytic bounds.

## Proof boundary

This is a continuation theorem for **any already-given candidate** preterminal solution and finite cutoff `S`. It is not yet the theorem stating that maximal finite Galerkin solutions exist with a common cutoff-independent lifespan. The next step is construction of a maximal interval (or an equivalent continuation mechanism), application of this seam theorem, and elimination of a finite endpoint before `a + (log(10/9))/100`.

Lean source validity, kernel axiom provenance, and repository-wide build remain subject to the pinned local toolchain's compilation and audit.
