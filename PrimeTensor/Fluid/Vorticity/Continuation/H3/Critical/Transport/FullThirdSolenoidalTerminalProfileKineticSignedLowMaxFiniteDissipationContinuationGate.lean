import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxActualTailSurplusPacking
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Integrability
import Mathlib.Tactic

/-!
# Finite full-H3 dissipation is already a conditional continuation criterion

The accepted terminal PDE estimate shows that hypothetical nonextension
forces the top H3 dissipation to dominate `1 / (T-t)` on a strict terminal
subinterval. The old pointwise comparison D3 <= D_full therefore makes
ordinary full H3 dissipation itself NONINTEGRABLE on every strict terminal
tail. This is incompatible with the `IntervalIntegrable` assumption repeatedly
used in the kinetic signed sixth-flux spectral packing chain.

The result is a conditional regularity/continuation criterion, not an
unconditional Navier--Stokes result: finite terminal full-H3 dissipation is
an additional, potentially singularity-excluding analytic hypothesis.

Unlike the vacuous tenth-power residual, the implication here uses a genuine
positive harmonic lower bound. It introduces no new axioms, continuum limit
assumptions, existential Fourier cutoffs, or arbitrary persistence widths.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Hypothetical failure of smooth continuation enforces the same
nonintegrable harmonic lower bound on the ENTIRE full physical H3
dissipation, not merely on its third-order component. -/
theorem thirdFullPhysical_noExtension_harmonicFullDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ, c ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        1 / (T - t) ≤ velocityH3DissipationAt u t := by
  obtain ⟨c, hc, hTop⟩ :=
    exists_terminalTail_one_div_terminalDistance_le_dissipation3_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  refine ⟨c, hc, ?_⟩
  intro t ht
  exact (hTop t ht).trans (velocityH3Dissipation3At_le_dissipationAt u t)

/-- The actual full-H3 dissipation is nonintegrable on EVERY strict
energy-class terminal subtail of a hypothetical nonextendible trajectory. -/
theorem thirdFullPhysical_noExtension_fullDissipation_nonintegrableStrictTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
        (velocityH3DissipationAt u) (Set.Ioo b T) := by
  obtain ⟨c, hc, hLower⟩ :=
    thirdFullPhysical_noExtension_harmonicFullDissipation244
      hH3 hNoExtension hClass b hb
  intro hFull
  have hTail : MeasureTheory.IntegrableOn
      (velocityH3DissipationAt u) (Set.Ioo c T) := by
    apply hFull.mono_set
    intro t ht
    exact ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hReciprocal : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / (T - t)) (Set.Ioo c T) := by
    apply Integrable.mono' hTail
    · exact (show Measurable (fun t : ℝ => 1 / (T - t)) by
        fun_prop).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hDist : 0 < T - t := by linarith only [ht.2]
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hDist)]
      exact hLower t ht
  exact not_integrableOn_one_div_terminalDistance hc.2 hReciprocal

/-- FINITE full-H3 dissipation on ANY strict terminal subinterval already
forces smooth continuation. No terminal energy bound, radial cutoff, or
signed-flux activity assumption is added. -/
theorem thirdFullPhysical_finiteFullDissipation_strictTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hDInt : IntervalIntegrable
      (velocityH3DissipationAt u) volume b T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  classical
  by_contra hNoExtension
  have hForbidden :=
    thirdFullPhysical_noExtension_fullDissipation_nonintegrableStrictTail244
      hH3 hNoExtension hClass b hb
  apply hForbidden
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mp hDInt

/-- The `IntervalIntegrable D_full a T` premise used across the kinetic
signed-sixth-flux series is already a continuation hypothesis for an
admissible H3 energy-class path. This does NOT prove that the premise holds
for arbitrary three-dimensional Navier--Stokes data. -/
theorem thirdFullPhysical_finiteFullDissipation_energyTail_forcesContinuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable
      (velocityH3DissipationAt u) volume a T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  let b : ℝ := h3BKMKineticTailMidpoint a T
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  have hFull : MeasureTheory.IntegrableOn
      (velocityH3DissipationAt u) (Set.Ioo a T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      hClass.terminal_start.2.le).mp hDInt
  have hTail : MeasureTheory.IntegrableOn
      (velocityH3DissipationAt u) (Set.Ioo b T) := by
    apply hFull.mono_set
    intro t ht
    exact ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hTailInt : IntervalIntegrable
      (velocityH3DissipationAt u) volume b T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).mpr hTail
  exact thirdFullPhysical_finiteFullDissipation_strictTail_forcesContinuation244
    hH3 hClass b hb hTailInt

end
end PrimeTensor.FirstMonomialTriad
