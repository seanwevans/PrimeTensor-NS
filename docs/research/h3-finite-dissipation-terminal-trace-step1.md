# H³ finite-dissipation terminal trace: step 1 (pointwise estimates)

Target local master: `f82c08a6`, already pushed; no source files are modified until the user explicitly applies the archive.

This prototype source (4 lemmas, no `sorry`, no `axiom`) combines previously formalized PrimeTensor estimates:

1. `mul_velocityH3Energy3At_le_dissipation3_add_quartic_remainder`, specialized to `K = ε = 1`, gives `E3(t) <= D3(t) + E0(t)`.
2. `velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path` and `velocityH3Dissipation3At_le_dissipationAt` imply `E(t) <= 1 + 6 E0(t) + 3 D(t)`.
3. `h3Audit_initialKineticEnergy_antitoneOn_positiveInterval` bounds `E0(t)` for all `b < t < T` by the kinetic anchor `E0(b)`.
4. `h3Path_physicalProjectedSource_norm_le_H3Energy244` implies `||R(t)||_2 <= (3+C_Leray)(1+6 E0(b)+3D(t))` on `(b,T)`.

**Remaining to formalize**: If `IntervalIntegrable D volume a T` holds, use the source's compact-strict-time continuity, scalar integrability, and the displayed domination to prove `IntegrableOn R (Ioo b T) volume`. Then use `h3Path_physicalHilbertFTC_betweenPositiveTimes244` and norm bounds on Bochner integral tails to construct a Cauchy filter as t approaches T and obtain the strong physical L² trace. This contradicts the `hNoTrace` premise of the higher-budget chain under its existing `hDInt` premise.

This prototype has been reviewed against the connected GitHub source declarations but **has not been compiled using the local Lean toolchain**. Run `lake env lean` on the new module before adding it to project indexes or committing.

The result would NOT prove unconditional smooth continuation, because finite integrated H³ dissipation is an additional hypothesis.
