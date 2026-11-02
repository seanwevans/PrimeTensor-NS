# Quarter-cubic physical H³ annuli: energy versus outer-frequency escape

Baseline: `5f282666` (`force cofinal physical source or outer-frequency escape on noncompressed H3 annuli`).

This step uses the *same exact physical first-crossing annuli* from the no-L²-trace branch, including cofinality, strict temporal separation, their selected source envelope and local positive annular integral charges. Neither full terminal H³ L¹ dissipation nor noncompressed terminal cubic clocks nor source boundedness is assumed.

At a selected time `t(v(k))`, put `R=v(k)+1`, `Q=N(v(k))+1`, `E=velocityH3EnergyAt u (t(v(k)))`. The strict original gap gives

    R³/4 < (D_low(Q)-D_low(R)) - R³/2,
    hence 3 R³/4 < D_low(Q)-D_low(R).

Since `D_low(R)≥0`, `D_low(Q)≤3 (Q+1)² ‖U₃(t)‖²`, and `‖U₃(t)‖²≤E`, we obtain the *unconditional pointwise* bound on these annuli

    R³ < 4 (Q+1)² E.

For any real `D` with `Q+1 ≤ D R`, squaring the cutoff inequality and cancelling `R²>0` gives

    R < 4 D² E.

Consequently, if the selected anchor physical H³ energies are **eventually bounded by a fixed finite B**, then for **every fixed D≥1**, eventually

    D (v(k)+1) < N(v(k))+2.

The outer/inner ratio therefore tends to +∞, under that energy bound, and this is eventually, not merely cofinally. If instead relative outer cutoffs stay bounded along an infinite subsequence, the physical H³ energy must grow at least linearly along that subsequence. The theorem does NOT provide a uniform H³ energy bound and does NOT prove continuation or exclude the other (unbounded-energy) escape mechanism.

Declarations:

- `h3Critical_scalar_quarterCubicGap_forces_outerEnergy`
- `h3Critical_scalar_quarterCubic_relativeOuter_forces_energyGrowth`
- `h3Critical_quarterCubicPhysicalAnchor_forces_energyOuter`
- `h3Critical_noL2Trace_disjointQuarterCubic_boundedEnergy_forces_outerEscape`

The audit registrar adds each declaration's `#check` and `#print axioms` and registers the new import in `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`. It contains no extra shell files. Lean compile and full project audit must run locally.
