import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFullTailDissipationShare

/-!
# Full-terminal physical intrinsic-frequency equivalence

On a hypothetical nonextendible admissible H³ path, the full physical
energy and full viscous dissipation each concentrate into their highest
order blocks on the ENTIRE left terminal tail:

    E₃/E -> 1,       D₃/D -> 1.

Their quotient identifies the two independently physical squared-frequency
scales asymptotically:

    (D₃/E₃) / (D/E) -> 1.

This is a relative comparison, not an additive estimate on these diverging
quantities. The same limit holds along the existing fixed indexed directed
source sequence, with all critical clocks and both adverse source alternatives
preserved. No new nonlinear transport sign or unconditional regularity claim
is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Ratio of the top physical squared frequency `D₃/E₃` to the full
physical squared frequency `D/E`. -/
noncomputable def h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  (velocityH3Dissipation3At u t / velocityH3Energy3At u t) /
    (velocityH3DissipationAt u t / velocityH3EnergyAt u t)

/-- The relative physical squared-frequency ratio is exactly the quotient
of the two top-order energy and dissipation shares. -/
theorem h3PathCanonical_topToFullIntrinsicFrequency_eq_shareQuotient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hE3 : 0 < velocityH3Energy3At u t)
    (hD : 0 < velocityH3DissipationAt u t) :
    h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t =
      (velocityH3Dissipation3At u t / velocityH3DissipationAt u t) /
        (velocityH3Energy3At u t / velocityH3EnergyAt u t) := by
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  unfold h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt
  field_simp [ne_of_gt hE3, ne_of_gt hE, ne_of_gt hD]

/-- Full physical and top-order intrinsic squared frequencies agree
asymptotically in their RELATIVE quotient throughout the left terminal tail. -/
theorem h3PathCanonical_intrinsicFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u)
      (𝓝[<] T) (𝓝 1) := by
  have hEnergyShare :
      Tendsto (fun t : ℝ =>
        velocityH3Energy3At u t / velocityH3EnergyAt u t)
        (𝓝[<] T) (𝓝 1) :=
    h3PathCanonical_topShare_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hDissShare :
      Tendsto (fun t : ℝ =>
        velocityH3Dissipation3At u t / velocityH3DissipationAt u t)
        (𝓝[<] T) (𝓝 1) :=
    h3PathCanonical_dissipationTopShare_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hQuotient :
      Tendsto (fun t : ℝ =>
        (velocityH3Dissipation3At u t / velocityH3DissipationAt u t) /
          (velocityH3Energy3At u t / velocityH3EnergyAt u t))
        (𝓝[<] T) (𝓝 1) := by
    have hPointwise :
        ((fun t : ℝ =>
          velocityH3Dissipation3At u t / velocityH3DissipationAt u t) /
          (fun t : ℝ =>
            velocityH3Energy3At u t / velocityH3EnergyAt u t)) =
          (fun t : ℝ =>
            (velocityH3Dissipation3At u t / velocityH3DissipationAt u t) /
              (velocityH3Energy3At u t / velocityH3EnergyAt u t)) := by
      funext t
      simp only [Pi.div_apply]
    rw [← hPointwise]
    simpa only [div_one] using
      (hDissShare.div hEnergyShare (by norm_num : (1 : ℝ) ≠ 0))
  have hE3T : Tendsto (velocityH3Energy3At u) (𝓝[<] T) atTop :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3T : Tendsto (velocityH3Dissipation3At u) (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hE3Pos : ∀ᶠ t : ℝ in 𝓝[<] T,
      0 < velocityH3Energy3At u t := by
    filter_upwards [(tendsto_atTop.1 hE3T) 1] with t ht
    linarith only [ht]
  have hDPos : ∀ᶠ t : ℝ in 𝓝[<] T,
      0 < velocityH3DissipationAt u t := by
    filter_upwards [(tendsto_atTop.1 hD3T) 1] with t ht
    have hLe := h3PathCanonical_topDissipation_le_fullDissipation u t
    linarith only [ht, hLe]
  have hEqual :
      h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u =ᶠ[𝓝[<] T]
        (fun t : ℝ =>
          (velocityH3Dissipation3At u t / velocityH3DissipationAt u t) /
            (velocityH3Energy3At u t / velocityH3EnergyAt u t)) := by
    filter_upwards [hE3Pos, hDPos] with t hE3 hD
    exact h3PathCanonical_topToFullIntrinsicFrequency_eq_shareQuotient
      u t hE3 hD
  exact hQuotient.congr' hEqual.symm

/-- For every tolerance, the physical top/full squared-frequency ratio
lies in a strict relative corridor on a sufficiently late terminal tail. -/
theorem h3PathCanonical_intrinsicFrequencyRatio_eventually_strictCorridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      1 - ε < h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t ∧
      h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u t < 1 + ε := by
  have hLimit :=
    h3PathCanonical_intrinsicFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hLower : 1 - ε < (1 : ℝ) := by linarith only [hε]
  have hUpper : (1 : ℝ) < 1 + ε := by linarith only [hε]
  filter_upwards [(tendsto_order.1 hLimit).1 (1 - ε) hLower,
    (tendsto_order.1 hLimit).2 (1 + ε) hUpper] with t hlo hhi
  exact ⟨hlo, hhi⟩

/-- The original fixed indexed directed source sequence also carries the
same physical frequency equivalence, with the gradient/ordered-monomial
alternatives and all three critical clocks unchanged. -/
theorem h3PathCanonical_fixedDirectedSource_intrinsicFrequencyRatio_withPhysicalAlternative
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
  obtain ⟨i, τ, hWitness, hτT, hTopT, hShare, _hUpper, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_topShareLimitOne_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  have hτLT : Tendsto τ atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hτT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hFrequency :=
    (h3PathCanonical_intrinsicFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb).comp hτLT
  exact ⟨i, τ, hWitness, hτT, hTopT, hShare,
    hFrequency, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
