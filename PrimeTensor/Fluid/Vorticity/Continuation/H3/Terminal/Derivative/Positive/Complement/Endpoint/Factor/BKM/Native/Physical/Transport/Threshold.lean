import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Physical.Cubic.Threshold
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact

/-!
# Physical adverse transport threshold on nondecreasing energy times

The exact H³ balance implies that adverse transport dominates raw
dissipation whenever the H³ energy derivative is nonnegative. Thus
the necessary physical cubic dissipation rate under hypothetical
nonextension transfers to adverse transport on that set. A recurrent
strict violation of this physical threshold forces continuation.
This statement uses physical time and no indexed witness ceiling.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Under hypothetical nonextension, adverse transport meets the raw
dissipation cubic threshold at every sufficiently late time with
nonnegative H³ energy growth. -/
theorem exists_terminalTail_physicalAdverseTransport_cubicRate_of_noH3PathExtension
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
            (-velocityH3TransportDerivativeAt u t) ^ 3 := by
  obtain ⟨c, hc, hRaw⟩ :=
    exists_terminalTail_rawDissipation_physicalCubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  refine ⟨c, hc, ?_⟩
  intro t ht hDerivative
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hc.1 ht.1), ht.2⟩
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass htClass
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hDLeTransport :
      velocityH3DissipationAt u t ≤
        -velocityH3TransportDerivativeAt u t := by
    linarith
  have hCube := pow_le_pow_left₀ hDNonneg hDLeTransport 3
  have hPrefactor :
      0 ≤ h3NativePhysicalClockCubicCoefficient u b * (T - t) ^ 2 :=
    mul_nonneg
      (h3NativePhysicalClockCubicCoefficient_nonneg u b)
      (sq_nonneg (T - t))
  exact (hRaw t ht).trans
    (mul_le_mul_of_nonneg_left hCube hPrefactor)

/-- Recurrent subcritical physical adverse transport at times of
nonnegative H³ energy growth forces smooth continuation. -/
theorem smoothContinuationExtension_of_recurrent_subcriticalPhysicalAdverseTransport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hSubcritical : ∀ c : ℝ, c ∈ Set.Ioo b T →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        0 ≤ deriv (velocityH3EnergyAt u) t ∧
        h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 *
            (-velocityH3TransportDerivativeAt u t) ^ 3 < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨c, hc, hLate⟩ :=
    exists_terminalTail_physicalAdverseTransport_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  obtain ⟨t, ht, hDerivative, hSmall⟩ := hSubcritical c hc
  exact (not_lt_of_ge (hLate t ht hDerivative)) hSmall

end

end Euclidean
end Bridge
end PrimeTensor
