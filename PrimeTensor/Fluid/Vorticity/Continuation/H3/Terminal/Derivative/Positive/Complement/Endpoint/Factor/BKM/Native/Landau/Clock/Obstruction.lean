import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Physical.Transport.Threshold
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.Loop

/-!
# Testing the current Landau transport bound against the physical clock

The existing Landau commutator estimate absorbs one copy of H³
dissipation and leaves the majorant `c_L(t) E(t)`. Exact balance shows
that this majorant bounds raw dissipation at nondecreasing energy
times. On a hypothetical nonextending path, it must therefore satisfy
the same physical cubic lower rate at all such late times. Native
positive-growth times occur arbitrarily close to the endpoint, so
the cubic quantity for this majorant cannot tend to zero there.
This identifies a concrete limitation of the current commutator bound,
without asserting a limit for the actual adverse transport.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- At a nondecreasing H³ energy time, exact balance and the current
Landau absorption estimate bound raw dissipation by `c_L E`. -/
theorem rawDissipation_le_canonicalLandau_majorant_of_nonnegativeGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDerivative : 0 ≤ deriv (velocityH3EnergyAt u) t) :
    velocityH3DissipationAt u t ≤
      h3PathCanonicalLandauTransportCoefficient u t *
        velocityH3EnergyAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hAbsorption :=
    h3TransportDissipationAbsorptionAt_of_currentLandau hH3 hClass ht
  unfold H3TransportDissipationAbsorptionAt at hAbsorption
  linarith

/-- Under hypothetical nonextension, the PDE-derived Landau majorant
meets the physical cubic threshold at every sufficiently late
nondecreasing energy time. -/
theorem exists_terminalTail_canonicalLandau_majorant_physicalCubicRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ, c ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        0 ≤ deriv (velocityH3EnergyAt u) t →
        1 ≤ h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 *
            (h3PathCanonicalLandauTransportCoefficient u t *
              velocityH3EnergyAt u t) ^ 3 := by
  obtain ⟨c, hc, hRaw⟩ :=
    exists_terminalTail_rawDissipation_physicalCubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  refine ⟨c, hc, ?_⟩
  intro t ht hDerivative
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hc.1 ht.1), ht.2⟩
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hCube := pow_le_pow_left₀ hDNonneg
    (rawDissipation_le_canonicalLandau_majorant_of_nonnegativeGrowth
      hH3 hClass htClass hDerivative) 3
  have hPrefactor :
      0 ≤ h3NativePhysicalClockCubicCoefficient u b * (T - t) ^ 2 :=
    mul_nonneg
      (h3NativePhysicalClockCubicCoefficient_nonneg u b)
      (sq_nonneg (T - t))
  exact (hRaw t ht).trans
    (mul_le_mul_of_nonneg_left hCube hPrefactor)

/-- The current Landau majorant cannot have a vanishing physical
cubic clock under hypothetical nonextension. -/
theorem not_canonicalLandau_majorant_physicalCubicVanishing_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ¬ Tendsto
      (fun t : ℝ =>
        h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 *
            (h3PathCanonicalLandauTransportCoefficient u t *
              velocityH3EnergyAt u t) ^ 3)
      (𝓝[<] T) (𝓝 (0 : ℝ)) := by
  intro hVanishing
  obtain ⟨c, hc, hLate⟩ :=
    exists_terminalTail_canonicalLandau_majorant_physicalCubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
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
          (h3PathCanonicalLandauTransportCoefficient u (τ n) *
            velocityH3EnergyAt u (τ n)) ^ 3 < 1 :=
    (hVanishing.comp hTauLT).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hInTail : ∀ᶠ n : ℕ in atTop, τ n ∈ Set.Ioo c T := by
    filter_upwards [hData.2.1.eventually (Ioi_mem_nhds hc.2)] with n hn
    exact ⟨hn, (hData.1 n).1.2⟩
  obtain ⟨n, hnTail, hnBelow⟩ := (hInTail.and hBelow).exists
  have hDerivative : 0 ≤ deriv (velocityH3EnergyAt u) (τ n) :=
    (by positivity : 0 ≤ (n : ℝ)).trans
      (le_of_lt (hData.1 n).2.2.1)
  exact (not_lt_of_ge (hLate (τ n) hnTail hDerivative)) hnBelow

end

end Euclidean
end Bridge
end PrimeTensor
