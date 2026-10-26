# Cofinal cubic annuli with actual physical projected-PDE persistence budgets

Base: `f796c45f`.

This step eliminates two *separate* a priori bounds from the cofinal-annulus
witness package. The starting spectral ceiling is supplied by the actual
finite weighted H³ state at each selected witness, and the uniform projected
physical `L²` source ceiling is obtained on a compact strict-time interval
using continuity of the genuine source.

Write `R=n+1`. The existing cubic sequence has `D_{≥R}(t_n)>R³`, and exact
fixed-time tail convergence selects `Q=N_n+1` such that the finite annulus
`B_{R,Q}(t_n)>3 R³/4`. Set `A=R³/2` and `g=B_{R,Q}(t_n)-A>0`.

With the actual starting spectral norm `K=‖S(t_n)‖` and a compact strict-time
source ceiling `C`, earlier proved polarization supplies

```
|B_{R,Q}(t_n+h)-B_{R,Q}(t_n)| ≤ Λ h + Ξ h²,
Λ = h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C,
Ξ = h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C.
```

Let `b=(t_n+T)/2` and `Z=Λ+Ξ+1`. A valid explicit construction is

```
δ = min ((b-t_n)/2) (min 1 (g/(2Z))).
```

Then `δ>0`, the entire window lies strictly before `T`, and
`Λ δ + Ξ δ² < g` (use `δ≤1`). Hence `B_{R,Q}>A` throughout the window, with

```
∫_{t_n}^{t_n+δ} B_{R,Q}(s) ds ≥ Aδ.
```

The sequence theorem chooses `N_n,K_n,C_n,δ_n` for every cofinal witness.
No uniform lower bound on `δ_n`, uniform upper bound on `N_n`, or terminal
integrated divergence has been established. The width can shrink if the
physical projected source or the selected frequency radius grows.

The Python registrar checks for placeholders and registers theorem checks and
axiom audits in the standard project entrypoints; regenerate the index after
registration and run the full Lean build.
