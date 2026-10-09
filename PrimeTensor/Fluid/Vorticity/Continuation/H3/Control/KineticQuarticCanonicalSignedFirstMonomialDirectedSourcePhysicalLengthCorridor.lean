import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourcePhysicalFrequencyCorridor
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Normalized.Cascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Cascade

/-!
# Full-terminal H³ physical characteristic-length equivalence

Under hypothetical nonextension, the physical top-order frequency
`sqrt(D₃/E₃)` and full frequency `sqrt(D/E)` both diverge on the ENTIRE
left terminal neighborhood, not only on an extracted subsequence.
Their reciprocal physical lengths therefore both tend to zero.

The previously established frequency-amplitude ratio `Ω₃/Ω -> 1`
becomes an exact relative length-scale identity

  (ℓ_full / ℓ_top) = (Ω₃ / Ω) -> 1,

on the entire terminal tail. This holds along the SAME fixed indexed
signed-source witness with its critical clocks and neutral gradient / fixed
ordered-monomial alternatives. These are necessary conditions under
nonextension and do not assert that any singularity is realized.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Reciprocal full physical H³ characteristic frequency. -/
noncomputable def h3PathCanonicalFullPhysicalLengthAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  (h3PathCanonicalFullPhysicalFrequencyAt u t)⁻¹

/-- Ratio of the full characteristic length to the top characteristic
length. This orientation equals the previously proved top/full frequency
ratio whenever the two physical frequencies are positive. -/
noncomputable def h3PathCanonicalFullToTopPhysicalLengthRatioAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  h3PathCanonicalFullPhysicalLengthAt u t /
    h3TopCharacteristicLengthAt u t

/-- Under hypothetical nonextension the true third/fourth derivative
frequency amplitude diverges at EVERY sufficiently late physical time. -/
theorem h3PathCanonical_topPhysicalFrequency_tendsto_atTop_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto (h3PathCanonicalTopPhysicalFrequencyAt u)
      (𝓝[<] T) atTop := by
  change Tendsto (fun t : ℝ =>
      Real.sqrt (velocityH3Dissipation3At u t /
        velocityH3Energy3At u t)) (𝓝[<] T) atTop
  exact Real.tendsto_sqrt_atTop.comp
    (velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass)

/-- The full physical H³ dissipation/energy frequency amplitude likewise
diverges on the COMPLETE terminal tail. -/
theorem h3PathCanonical_fullPhysicalFrequency_tendsto_atTop_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto (h3PathCanonicalFullPhysicalFrequencyAt u)
      (𝓝[<] T) atTop := by
  change Tendsto (fun t : ℝ =>
      Real.sqrt (velocityH3DissipationAt u t /
        velocityH3EnergyAt u t)) (𝓝[<] T) atTop
  exact Real.tendsto_sqrt_atTop.comp
    (velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass)

/-- Both genuine characteristic lengths vanish on the same full
left-terminal neighborhood. No subsequence selection is involved. -/
theorem h3PathCanonical_bothPhysicalLengths_tendsto_zero_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto (h3TopCharacteristicLengthAt u) (𝓝[<] T) (𝓝 0) ∧
      Tendsto (h3PathCanonicalFullPhysicalLengthAt u) (𝓝[<] T) (𝓝 0) := by
  have hTop : Tendsto (h3TopCharacteristicFrequencyAt u)
      (𝓝[<] T) atTop := by
    change Tendsto (fun t : ℝ =>
      Real.sqrt (velocityH3Dissipation3At u t /
        velocityH3Energy3At u t)) (𝓝[<] T) atTop
    exact Real.tendsto_sqrt_atTop.comp
      (velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass)
  have hFull := h3PathCanonical_fullPhysicalFrequency_tendsto_atTop_nhdsLT
    hH3 hNoExtension hClass
  constructor
  · unfold h3TopCharacteristicLengthAt
    exact hTop.inv_tendsto_atTop
  · unfold h3PathCanonicalFullPhysicalLengthAt
    exact hFull.inv_tendsto_atTop

/-- Exactly, the relative full-to-top physical length is the top-to-full
physical frequency when top H³ energy and dissipation are positive. -/
theorem h3PathCanonical_fullToTopLengthRatio_eq_topToFullFrequencyRatio
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hE3 : 0 < velocityH3Energy3At u t)
    (hD3 : 0 < velocityH3Dissipation3At u t) :
    h3PathCanonicalFullToTopPhysicalLengthRatioAt u t =
      h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u t := by
  have hTopFreq : 0 < h3PathCanonicalTopPhysicalFrequencyAt u t := by
    unfold h3PathCanonicalTopPhysicalFrequencyAt
    exact Real.sqrt_pos.2 (div_pos hD3 hE3)
  have hFullFreq : 0 < h3PathCanonicalFullPhysicalFrequencyAt u t :=
    h3PathCanonical_fullPhysicalFrequency_pos_of_topDissipation_pos u t hD3
  unfold h3PathCanonicalFullToTopPhysicalLengthRatioAt
    h3PathCanonicalFullPhysicalLengthAt
    h3TopCharacteristicLengthAt
    h3PathCanonicalTopToFullPhysicalFrequencyRatioAt
  change (h3PathCanonicalFullPhysicalFrequencyAt u t)⁻¹ /
      (h3PathCanonicalTopPhysicalFrequencyAt u t)⁻¹ =
    h3PathCanonicalTopPhysicalFrequencyAt u t /
      h3PathCanonicalFullPhysicalFrequencyAt u t
  field_simp [ne_of_gt hTopFreq, ne_of_gt hFullFreq]

/-- Full-to-top physical length ratio converges to one on the entire
terminal tail. This is relative equivalence of two shrinking lengths,
not an absolute rate in the physical time T-t. -/
theorem h3PathCanonical_physicalLengthRatio_tendsto_one_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (h3PathCanonicalFullToTopPhysicalLengthRatioAt u)
      (𝓝[<] T) (𝓝 1) := by
  have hFrequency :=
    h3PathCanonical_physicalFrequencyRatio_tendsto_one_nhdsLT_of_noExtension
      hH3 hNoExtension hClass hb
  have hE3T : Tendsto (velocityH3Energy3At u) (𝓝[<] T) atTop :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3T : Tendsto (velocityH3Dissipation3At u) (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hEq :
      h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u =ᶠ[𝓝[<] T]
        h3PathCanonicalFullToTopPhysicalLengthRatioAt u := by
    filter_upwards [(tendsto_atTop.1 hE3T) 1,
      (tendsto_atTop.1 hD3T) 1] with t hE3One hD3One
    have hE3 : 0 < velocityH3Energy3At u t :=
      lt_of_lt_of_le zero_lt_one hE3One
    have hD3 : 0 < velocityH3Dissipation3At u t :=
      lt_of_lt_of_le zero_lt_one hD3One
    exact (h3PathCanonical_fullToTopLengthRatio_eq_topToFullFrequencyRatio
      u t hE3 hD3).symm
  exact hFrequency.congr' hEq

/-- Eventually the ratio of the two vanishing physical characteristic
lengths lies in any requested open relative corridor around one. -/
theorem h3PathCanonical_physicalLengthRatio_eventually_strictCorridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      1 - ε < h3PathCanonicalFullToTopPhysicalLengthRatioAt u t ∧
      h3PathCanonicalFullToTopPhysicalLengthRatioAt u t < 1 + ε := by
  have hLimit :=
    h3PathCanonical_physicalLengthRatio_tendsto_one_nhdsLT
      hH3 hNoExtension hClass hb
  have hLower : 1 - ε < (1 : ℝ) := by linarith only [hε]
  have hUpper : (1 : ℝ) < 1 + ε := by linarith only [hε]
  filter_upwards [(tendsto_order.1 hLimit).1 (1 - ε) hLower,
    (tendsto_order.1 hLimit).2 (1 + ε) hUpper] with t hlo hhi
  exact ⟨hlo, hhi⟩

/-- The unchanged fixed directed ten-source obstruction carries both
vanishing physical lengths and their relative equivalence, alongside all
three critical clocks and the original exhaustive PDE source alternative. -/
theorem h3PathCanonical_fixedDirectedSource_physicalLengthRatio_withPhysicalAlternative
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
      Tendsto (fun n : ℕ => h3TopCharacteristicLengthAt u (τ n))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => h3PathCanonicalFullPhysicalLengthAt u (τ n))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullToTopPhysicalLengthRatioAt u (τ n))
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
    hFrequencyRatio, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_physicalFrequencyRatio_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  have hτLT : Tendsto τ atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hτT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hLengths :=
    h3PathCanonical_bothPhysicalLengths_tendsto_zero_nhdsLT
      hH3 hNoExtension hClass
  have hLengthRatio :=
    h3PathCanonical_physicalLengthRatio_tendsto_one_nhdsLT
      hH3 hNoExtension hClass hb
  exact ⟨i, τ, hWitness, hτT, hTopT, hEnergyShare, hSquaredRatio,
    hFrequencyRatio, hLengths.1.comp hτLT, hLengths.2.comp hτLT,
    hLengthRatio.comp hτLT, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
