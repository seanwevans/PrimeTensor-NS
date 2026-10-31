# Actual gradient logarithmic spikes occupy open spatial regions

Base commit `6fd6004a` — force actual physical velocity-gradient spikes from critical H3 radii.

## Spatial coercivity already available without a new hypothesis

The committed theorem shows, under the original conditional higher-moment majorant, projected-source ceiling, eighth-power cutoff and noncompressed terminal clock, that for any fixed physical `b` and `c ≥ 0` satisfying

    4 (T-b) 4422 c < 16m+3,

every sufficiently late canonical first-crossing anchor `t_k=τ(v k)` admits an actual time `s_k∈(b,t_k)`, axes `i,j` and point `x_k` such that

    c log(v k+1) < |∂ᵢuⱼ(s_k,x_k)|.

Pointwise spikes need not create dissipative expenditure by themselves. However the actual preterminal Navier–Stokes velocity is spatially `C³` on each strict time slice. The exact physical first derivative `∂ᵢuⱼ(s,·)` is therefore continuous. The strict inequality persists on **an actual nonempty open ball**:

    ∃ r_k > 0, ∀ y ∈ ball(x_k,r_k),
      c log(v k+1) < |∂ᵢuⱼ(s_k,y)|.

The proof takes the original same-anchor witnesses and upgrades only the spatial point, without selecting new times or weakening the sharp coefficient `4 (T-b) 4422`. No physical gradient upper majorant is substituted for the actual derivative.

## What finite dissipation does and does not constrain

A ball of positive radius has positive Lebesgue spatial measure. Thus, informally, the physical first-gradient dissipation at that fixed time is positive on this ball and its spatial integral is bounded below by `c² log²(R_k)` times the ball volume. **The Lean module does not claim or formalize this quantitative integral estimate.** Doing so would require an explicit measure/integral bridge. Even after that bridge, the radii `r_k` could decrease arbitrarily fast, and each spike may persist for arbitrarily short times. Neither a uniform spatial radius nor a positive temporal residence width follows merely from `C³` in space and the canonical H³ energy identities.

The next genuinely coercive step would be an independent Fourier H⁴/dissipation estimate for actual first gradients, or a quantitative time-persistence estimate with a width that finite dissipation cannot accommodate. Without either, open spatial superlevel regions are compatible with finite total viscous expenditure.

## Lean declarations

- `h3Path_actualVelocityGradient_spatialContinuous244`
- `h3Path_actualGradientSpike_persistsOnSpatialBall244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_actualGradientSpatialOpenBall244`

Static source and ZIP tests do not substitute for Lake compilation.
