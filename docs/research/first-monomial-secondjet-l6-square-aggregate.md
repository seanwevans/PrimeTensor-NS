# Complete 27-slot squared homogeneous Sobolev aggregate

**Base checkpoint:** `e94b93e6` — full physical second-jet Fréchet-square energy compared with E3.

For each ordered component/direction/direction tuple `(j,i,k)`, the already
proved homogeneous point3 estimate gives

    ‖∂ᵢ∂ₖ fⱼ‖_{L6(V3)} ≤ S · ‖D(∂ᵢ∂ₖ fⱼ)‖_{L2(Point3)}.

Squaring in `ℝ≥0∞` and summing over all 27 ordered triples proves

    Σ_{j,i,k} ‖∂ᵢ∂ₖ fⱼ‖₆²
       ≤ S² Σ_{j,i,k} ‖D(∂ᵢ∂ₖ fⱼ)‖₂².

The aggregation itself has no extra cardinality factor. The genuine factor
`card (Axis Depth.three) = 3` arises separately from the physical sup-norm
Fréchet-to-coordinate integral bound already committed in `e94b93e6`.

**Remaining analytic bridge:** convert the finite `eLpNorm`-squared terms to
`ENNReal.ofReal` of their Bochner square integrals and transport the existing
real-valued E3 inequality into the extended nonnegative reals. This bridge is
not assumed or asserted in the current patch.

No new axioms, placeholder lemmas, `sorry`, PDE hypotheses, or claims about
unconditional 3D Navier–Stokes regularity. Local Lean compilation required.
