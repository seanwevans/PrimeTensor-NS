# Attained H³ source maxima: quantitative local continuity-radius obstruction

**Base:** `f353c30f` (accepted source-peak anchor versus temporal excursion proof).

The accepted cofinal theorem selects pairwise separated source windows
`[t(v(k)), t(v(k))+w(v(k))]`, shorter calibrated dissipation windows of
width `δ(k)`, and attained spectral/source maxima at real times
`sState(k), sSource(k)` inside the *original* windows. The maxima may lie
outside the shorter calibrated windows.

The repository already proves strong positive-time continuity of the actual
projected momentum source and H³ spectral state:

- `h3Path_actualProjectedMomentumSource_continuousOnStrict244`;
- `h3Audit_initialActualSpectralVelocity_continuousOn`.

For **every** k and positive thresholds `εU, εR`, the new theorems select
actual positive radii `ηU(k,εU), ηR(k,εR)` such that the respective
physical differences from the peak are strictly below threshold whenever
an observation belongs to the original window and its time distance from
the peak is below the selected radius.

In particular, if an actual source/spectral temporal excursion at the
attained maximizing time exceeds the relevant positive threshold, then

    ηU(k, εU) ≤ w(v(k))  or  ηR(k, εR) ≤ w(v(k))

for the corresponding branch. Conversely, `w(v(k)) < ηU` or `< ηR`
forces the corresponding actual temporal increment below threshold.

The cofinal theorem selects these moduli on the **same** original witnesses,
preserves the strict cofinal peak clocks, disjointness, and full-H³
integrated viscous cost inequality, and requires no additional uniform
regularity or existence assumption. Its conclusion does not claim the
widths or the radii have a positive common lower bound, and therefore does
not establish terminal continuation or global regularity.

The next obstruction is to connect these local radii to explicit physical
PDE variation/integrated-source costs (or produce a terminal-uniform rate)
without smuggling in a Lipschitz bound for the H³-weighted spectral path.

Lean theorem declarations:

- `h3Critical_continuousOn_anchor_has_positiveTemporalRadius`
- `h3Critical_anchorExcursion_forces_windowWidth`
- `h3Critical_actualSourceSpectral_positiveAnchorRadii`
- `h3Critical_noL2Trace_cofinalFivefold_excursionForcesLocalWidth`

The package requires elaboration in the pinned Lean/mathlib repository;
static checks are not a claim of formal compilation.
