# Critical terminal scaling of optimal inner-radius physical viscous clocks

Base: `19ce8a459c7e1268964b79a340b06ef7522424fc`.

The preceding physical theorem extracts a positive interval `[x_k,x_k+delta_k]` with the **true** optimized height

`h_k = epsilon_k / thirdFullPhysicalAnnularCapClockFactor244 u b (radiusMin k) epsilon_k`

and actual physical terminal-tail charge

`delta_k * h_k <= integral x_k..T (velocityH3DissipationAt u)`.

Let `tau_k = T-x_k`. Exact algebra (not a new PDE assumption) gives

`(delta_k/tau_k) * (tau_k*h_k) = delta_k*h_k`.

Consequently, the unconditionally smaller of the terminal-normalized width and height obeys

`min(delta_k/tau_k, tau_k*h_k) <= sqrt(integral x_k..T D_H3)`.

Since `D_H3` is nonnegative and interval-integrable over `[a,T]`, its terminal tail converges to zero when `x_k -> T`. This formalizes a necessary **critical-scaling bottleneck** for the genuine physical annular clocks.

Two separate conditional sharp consequences:

1. If `c>0` and `c <= tau_k*h_k` for every index (height at least critical inverse-time rate), then `delta_k/tau_k -> 0`; the windows occupy a vanishing **fraction** of the remaining horizon, not merely a vanishing absolute width.
2. If `c>0` and `c <= delta_k/tau_k` for every index (noncompressing relative time width), then `tau_k*h_k -> 0`; the physical clock heights are strictly subcritical compared to inverse terminal time.

These implications are presented with honest explicit assumptions. The PDE has not yet been proved to produce an eventual critical height or noncompressing width, so neither branch establishes terminal H3 continuation by itself. No `sorry`, `admit`, or new axiom is used.

## Lean 4 convergence combinator correction

The three `Tendsto.of_nonneg_of_le` calls in the first draft were not available in Lean v4.34.0-rc1. They are now direct applications of `squeeze_zero'`, given explicit eventual nonnegativity, eventual pointwise upper bounds, and `Tendsto` of the majorant to zero. All eight theorem statements and mathematical hypotheses are unchanged.
