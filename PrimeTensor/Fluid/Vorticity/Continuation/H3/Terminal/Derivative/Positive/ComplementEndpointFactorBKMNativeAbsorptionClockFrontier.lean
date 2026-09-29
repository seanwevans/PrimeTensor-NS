import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeLandauScaleGap

/-!
# Physical clock frontier for a dissipation-aware transport estimate

Suppose the exact transport estimate absorbs one copy of dissipation:

    -T_H3(t) ≤ D(t) + c(t) E(t).

At a nondecreasing energy time, exact balance gives `D(t) ≤ c(t) E(t)`.
Thus hypothetical nonextension forces `c E` to meet the physical cubic
threshold on every late nondecreasing energy time. If the physical
cubic quantity of `c E` tends to zero, continuation follows. This
specifies the analytic rate needed of a sharpened transport estimate;
it does not construct such a coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Exact balance turns one-copy transport absorption into a raw
dissipation bound on nondecreasing energy times. -/
theorem rawDissipation_le_absorptionCoefficient_mul_energy_of_nonnegativeGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ} {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAbsorb : H3TransportDissipationAbsorptionAt u c t)
    (hDerivative : 0 ≤ deriv (velocityH3EnergyAt u) t) :
    velocityH3DissipationAt u t ≤ c t * velocityH3EnergyAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  unfold H3TransportDissipationAbsorptionAt at hAbsorb
  linarith

/-- Every global one-copy absorption coefficient meets the physical
cubic rate on late nondecreasing energy times under nonextension. -/
theorem exists_terminalTail_absorptionCoefficient_physicalCubicRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAbsorb : ∀ t : ℝ, t ∈ Set.Ioo a T →
      H3TransportDissipationAbsorptionAt u c t) :
    ∃ d : ℝ, d ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo d T →
        0 ≤ deriv (velocityH3EnergyAt u) t →
        1 ≤ h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 *
            (c t * velocityH3EnergyAt u t) ^ 3 := by
  obtain ⟨d, hd, hRaw⟩ :=
    exists_terminalTail_rawDissipation_physicalCubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  refine ⟨d, hd, ?_⟩
  intro t ht hDerivative
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hCube := pow_le_pow_left₀ hDNonneg
    (rawDissipation_le_absorptionCoefficient_mul_energy_of_nonnegativeGrowth
      hH3 hClass htClass (hAbsorb t htClass) hDerivative) 3
  have hPrefactor :
      0 ≤ h3NativePhysicalClockCubicCoefficient u b * (T - t) ^ 2 :=
    mul_nonneg
      (h3NativePhysicalClockCubicCoefficient_nonneg u b)
      (sq_nonneg (T - t))
  exact (hRaw t ht).trans
    (mul_le_mul_of_nonneg_left hCube hPrefactor)

/-- A dissipation-aware transport coefficient whose energy-weighted
physical cubic clock vanishes forces smooth continuation. -/
theorem smoothContinuationExtension_of_absorptionCoefficient_vanishingPhysicalCubic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAbsorb : ∀ t : ℝ, t ∈ Set.Ioo a T →
      H3TransportDissipationAbsorptionAt u c t)
    (hVanishing : Tendsto
      (fun t : ℝ =>
        h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 * (c t * velocityH3EnergyAt u t) ^ 3)
      (𝓝[<] T) (𝓝 (0 : ℝ))) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨d, hd, hThreshold⟩ :=
    exists_terminalTail_absorptionCoefficient_physicalCubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb hAbsorb
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    exists_terminal_positiveGrowth_quantitativeNativeData_on_subtail
      hH3 hNoExtension hClass hb
  have hTauLT : Tendsto τ atTop (𝓝[<] T) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hData.2.1,
        Eventually.of_forall (fun n => (hData.1 n).1.2)⟩
  have hBelow : ∀ᶠ n : ℕ in atTop,
      h3NativePhysicalClockCubicCoefficient u b *
        (T - τ n) ^ 2 *
          (c (τ n) * velocityH3EnergyAt u (τ n)) ^ 3 < 1 :=
    (hVanishing.comp hTauLT).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hInTail : ∀ᶠ n : ℕ in atTop, τ n ∈ Set.Ioo d T := by
    filter_upwards [hData.2.1.eventually (Ioi_mem_nhds hd.2)] with n hn
    exact ⟨hn, (hData.1 n).1.2⟩
  obtain ⟨n, hnTail, hnBelow⟩ := (hInTail.and hBelow).exists
  have hDerivative : 0 ≤ deriv (velocityH3EnergyAt u) (τ n) :=
    (by positivity : 0 ≤ (n : ℝ)).trans
      (le_of_lt (hData.1 n).2.2.1)
  exact (not_lt_of_ge (hThreshold (τ n) hnTail hDerivative)) hnBelow

end

end Euclidean
end Bridge
end PrimeTensor
