# Anchored physical PDE persistence for finite H³ annuli

Base commit: `bcac4edc` (projected PDE source controls annular H³ dissipation variation).

## Improvement over the previous theorem

The earlier Lipschitz annulus result assumes a common **full weighted H³ state**
coordinate ceiling at both time endpoints. Physical projected-source control in
unweighted L² **does not** supply that future H³ ceiling. The new theorem drops
that assumption and replaces the linear bound with a linear-plus-quadratic
polynomial in elapsed time.

Let `G = S(s)` be the actual starting Fourier state and `H = S(t)` at later
time `t`. Define `M_ρ` to be the already-verified sharp gradient cutoff and
`V_ρ(C) = (ρ+1) sqrt(3(1+ρ²+ρ⁴+ρ⁶)) C`. The previous checkpoint gives
`‖M_ρ(G_j-H_j)‖ ≤ V_ρ(C)(t-s)` from a bound `‖PDEsource(r)‖_{L²} ≤ C`.

If **only the starting snapshot** satisfies `‖G_j‖ ≤ K`, then
`‖M_ρ G_j‖ ≤ (ρ+1)K`. The triangle inequality gives the later *localized*
multiplier norm bound; no future full spectral envelope is required. From
`|‖x‖²-‖y‖²| ≤ (‖x‖+‖y‖)‖x-y‖`:

```
|D_<ρ(S(t)) - D_<ρ(S(s))|
  ≤ 6 (ρ+1) K V_ρ(C) (t-s) + 3 V_ρ(C)² (t-s)².
```

For the finite annulus `B_{R,Q}(r) = D_<Q(S(r))-D_<R(S(r))`, set

```
Λ = 6 K C [(Q+1)² sqrt(3W(Q)) + (R+1)² sqrt(3W(R))],
Ξ = 3[V_Q(C)² + V_R(C)²],     W(x)=1+x²+x⁴+x⁶.
```

Then `|B_{R,Q}(t)-B_{R,Q}(s)| ≤ Λ(t-s)+Ξ(t-s)²`. If `B_{R,Q}(s)>A` and
`Λδ+Ξδ² < B_{R,Q}(s)-A`, the annular dissipation stays above `A` on the
entire chosen preterminal window and integrates to at least `δ A`.

Both `C` and `K` may depend on the anchor/window. This is a **quantitative
conditional local estimate**, not a uniform terminal time-width bound, an
integral divergence theorem, or a solution to global 3D Navier–Stokes.

## Registered declarations

- `h3Path_lowRadialMultiplier_anchoredQuadraticStability244`
- `h3Path_lowRadialDissipation_anchoredGradientStability244`
- `h3PathLowRadialPDEGradientRate244`
- `h3Path_lowRadialPDEGradientRate_nonneg244`
- `h3Path_actualLowRadialDissipationVariation_anchoredPDE244`
- `h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244`
- `h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244`
- `h3Path_actualFiniteAnnulusVariation_anchoredPDE244`
- `h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244`
