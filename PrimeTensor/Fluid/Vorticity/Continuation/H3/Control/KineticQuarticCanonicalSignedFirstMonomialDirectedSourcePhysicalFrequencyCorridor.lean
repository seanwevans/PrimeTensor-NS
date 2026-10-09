import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceIntrinsicFrequencyCorridor

/-!
# Full-terminal physical H³ frequency amplitude equivalence

The previously proved relative squared-frequency limit is

    (D₃/E₃) / (D/E) -> 1     as t approaches T from below.

This module translates that ratio into physical square-root frequencies:

    Ω₃ = sqrt (D₃/E₃),   Ω = sqrt (D/E),   Ω₃/Ω -> 1.

The conversion is exact whenever E₃ is positive. Under hypothetical
nonextension E₃ and D₃ diverge along the entire left terminal filter,
so the physical frequency ratios are eventually well-defined and positive.
The same limit is synchronized with the original fixed indexed directed-source
witness, including its critical clocks and neutral source alternative.

This is a relative frequency-amplitude limit. It says nothing about the
absolute difference Ω₃-Ω and does not exclude either PDE obstruction branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Physical fourth-to-third-order dissipation frequency amplitude. -/
noncomputable def h3PathCanonicalTopPhysicalFrequencyAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  Real.sqrt (velocityH3Dissipation3At u t / velocityH3Energy3At u t)

/-- Physical full-dissipation to full-energy frequency amplitude. -/
noncomputable def h3PathCanonicalFullPhysicalFrequencyAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  Real.sqrt (velocityH3DissipationAt u t / velocityH3EnergyAt u t)

/-- Ratio between the physical top and full H³ frequency amplitudes. -/
noncomputable def h3PathCanonicalTopToFullPhysicalFrequencyRatioAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  h3PathCanonicalTopPhysicalFrequencyAt u t /
    h3PathCanonicalFullPhysicalFrequencyAt u t

/-- Positive top-order dissipation makes the full physical frequency
amplitude strictly positive. -/
theorem h3PathCanonical_fullPhysicalFrequency_pos_of_topDissipation_pos
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hD3 : 0 < velocityH3Dissipation3At u t) :
    0 < h3PathCanonicalFullPhysicalFrequencyAt u t := by
  have hD : 0 < velocityH3DissipationAt u t :=
    lt_of_lt_of_le hD3
      (h3PathCanonical_topDissipation_le_fullDissipation u t)
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  unfold h3PathCanonicalFullPhysicalFrequencyAt
  exact Real.sqrt_pos.2 (div_pos hD hE)

/-- Exact conversion between the physical frequency-amplitude ratio and
the square root of the previously defined squared-frequency ratio. -/
theorem h3PathCanonical_physicalFrequencyRatio_eq_sqrt_squaredRatio
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hE3 : 0 < velocityH3Energy3At u t) :
    h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u t =
      Real.sqrt (h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t) := by
  have hNum :
      0 ≤ velocityH3Dissipation3At u t / velocityH3Energy3At u t :=
    div_nonneg (velocityH3Dissipation3At_nonneg u t) hE3.le
  unfold h3PathCanonicalTopToFullPhysicalFrequencyRatioAt
    h3PathCanonicalTopPhysicalFrequencyAt
    h3PathCanonicalFullPhysicalFrequencyAt
    h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt
  rw [Real.sqrt_div hNum
    (velocityH3DissipationAt u t / velocityH3EnergyAt u t)]

/-- Relative physical frequency AMPLITUDES agree on the complete left
terminal neighborhood of every hypothetical nonextendible admissible path. -/
theorem h3PathCanonical_physicalFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u)
      (𝓝[<] T) (𝓝 1) := by
  have hSquared :
      Tendsto (h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u)
        (𝓝[<] T) (𝓝 1) :=
    h3PathCanonical_intrinsicFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hRoot :
      Tendsto (fun t : ℝ =>
        Real.sqrt (h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t))
        (𝓝[<] T) (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hSquared
  have hTopT : Tendsto (velocityH3Energy3At u) (𝓝[<] T) atTop :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hEq :
      (fun t : ℝ =>
        Real.sqrt (h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t))
      =ᶠ[𝓝[<] T]
        h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u := by
    filter_upwards [(tendsto_atTop.1 hTopT) 1] with t hThird
    have hE3 : 0 < velocityH3Energy3At u t :=
      lt_of_lt_of_le zero_lt_one hThird
    exact (h3PathCanonical_physicalFrequencyRatio_eq_sqrt_squaredRatio
      u t hE3).symm
  exact hRoot.congr' hEq

/-- Every fixed relative tolerance eventually bounds the physical frequency
amplitude quotient above and below on the complete terminal tail. -/
theorem h3PathCanonical_physicalFrequencyRatio_eventually_strictCorridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      1 - ε < h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u t ∧
      h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u t < 1 + ε := by
  have hLimit :=
    h3PathCanonical_physicalFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hLower : 1 - ε < (1 : ℝ) := by linarith only [hε]
  have hUpper : (1 : ℝ) < 1 + ε := by linarith only [hε]
  filter_upwards [(tendsto_order.1 hLimit).1 (1 - ε) hLower,
    (tendsto_order.1 hLimit).2 (1 + ε) hUpper] with t hlo hhi
  exact ⟨hlo, hhi⟩

/-- The SAME fixed indexed directed-source witness carries both square-
frequency and genuine physical frequency-amplitude equivalence while
retaining all critical clocks and both source branches. -/
theorem h3PathCanonical_fixedDirectedSource_physicalFrequencyRatio_withPhysicalAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ,
        τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        velocityH3Energy3At u (τ n) / velocityH3EnergyAt u (τ n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u (τ n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u (τ n))
        atTop (𝓝 1) ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (τ n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientTopShareClockAt u T b (τ n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n))) := by
  obtain ⟨i, τ, hWitness, hτT, hTopT, hEnergyShare, hSquaredRatio,
    hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_intrinsicFrequencyRatio_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  have hτLT : Tendsto τ atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hτT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hPhysical :=
    (h3PathCanonical_physicalFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb).comp hτLT
  exact ⟨i, τ, hWitness, hτT, hTopT, hEnergyShare, hSquaredRatio,
    hPhysical, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
