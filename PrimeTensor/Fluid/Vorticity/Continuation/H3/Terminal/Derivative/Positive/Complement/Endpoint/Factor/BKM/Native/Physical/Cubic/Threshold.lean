import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Physical.Clock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Normalized.Dissipation.Rate

/-!
# A physical clock threshold for raw dissipation

The normalized H³ dissipation rate already gives a necessary cubic
terminal bound under hypothetical nonextension. Since H³ energy is at
least one, raw dissipation satisfies the same bound. Any physical time
ceiling for raw dissipation must therefore satisfy that cubic bound on
a late tail. An arbitrarily late strict violation forces continuation.
The condition is expressed at physical times, independent of a native
witness or its index.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The coefficient in the existing full-energy normalized cubic
terminal rate, with the same anchor `b`. -/
def h3NativePhysicalClockCubicCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b : ℝ) : ℝ :=
  3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
    (velocityH3Energy0At u b + 1) *
      (4 + 3 * velocityH3Energy0At u b) ^ 3

theorem h3NativePhysicalClockCubicCoefficient_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b : ℝ) :
    0 ≤ h3NativePhysicalClockCubicCoefficient u b := by
  unfold h3NativePhysicalClockCubicCoefficient
  have hE0 : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  positivity

/-- Hypothetical nonextension forces the cubic physical terminal
rate for raw full H³ dissipation on a strict tail. -/
theorem exists_terminalTail_rawDissipation_physicalCubicRate_of_noH3PathExtension
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
        1 ≤ h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 * (velocityH3DissipationAt u t) ^ 3 := by
  obtain ⟨c, hc, hNormalized⟩ :=
    exists_terminalTail_normalized_dissipation_cubic_rate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  refine ⟨c, hc, ?_⟩
  intro t ht
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hEnergyOne : 1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t
  have hRatioNonneg :
      0 ≤ velocityH3DissipationAt u t / velocityH3EnergyAt u t :=
    div_nonneg hDNonneg (by linarith)
  have hRatioLeRaw :
      velocityH3DissipationAt u t / velocityH3EnergyAt u t ≤
        velocityH3DissipationAt u t :=
    dissipation_div_energy_le_raw_of_energy_one _ _ hDNonneg hEnergyOne
  have hCube := pow_le_pow_left₀ hRatioNonneg hRatioLeRaw 3
  have hPrefactor :
      0 ≤ h3NativePhysicalClockCubicCoefficient u b * (T - t) ^ 2 :=
    mul_nonneg
      (h3NativePhysicalClockCubicCoefficient_nonneg u b)
      (sq_nonneg (T - t))
  have hNormalizedRate :
      1 ≤ h3NativePhysicalClockCubicCoefficient u b *
        (T - t) ^ 2 *
          (velocityH3DissipationAt u t / velocityH3EnergyAt u t) ^ 3 := by
    simpa only [h3NativePhysicalClockCubicCoefficient] using
      hNormalized t ht
  exact hNormalizedRate.trans
    (mul_le_mul_of_nonneg_left hCube hPrefactor)

/-- A physical raw dissipation ceiling on a nonextending path must
itself meet the cubic terminal threshold on a strict tail. -/
theorem exists_terminalTail_physicalRawCeiling_cubicRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {F : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeiling : H3TerminalPhysicalRawDissipationCeiling u b T F) :
    ∃ c : ℝ, c ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        1 ≤ h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 * (F (T - t)) ^ 3 := by
  obtain ⟨c, hc, hRaw⟩ :=
    exists_terminalTail_rawDissipation_physicalCubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  refine ⟨c, hc, ?_⟩
  intro t ht
  have htB : t ∈ Set.Ioo b T :=
    ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hRawNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hCube := pow_le_pow_left₀ hRawNonneg
    (hCeiling t htB) 3
  have hPrefactor :
      0 ≤ h3NativePhysicalClockCubicCoefficient u b * (T - t) ^ 2 :=
    mul_nonneg
      (h3NativePhysicalClockCubicCoefficient_nonneg u b)
      (sq_nonneg (T - t))
  exact (hRaw t ht).trans
    (mul_le_mul_of_nonneg_left hCube hPrefactor)

/-- If the physical ceiling falls strictly below the necessary cubic
threshold arbitrarily close to the endpoint, the path continues. -/
theorem smoothContinuationExtension_of_physicalRawCeiling_subcubic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {F : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeiling : H3TerminalPhysicalRawDissipationCeiling u b T F)
    (hSubcubic : ∀ c : ℝ, c ∈ Set.Ioo b T →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 * (F (T - t)) ^ 3 < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨c, hc, hLower⟩ :=
    exists_terminalTail_physicalRawCeiling_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb hCeiling
  obtain ⟨t, ht, hUpper⟩ := hSubcubic c hc
  exact (not_lt_of_ge (hLower t ht)) hUpper

end

end Euclidean
end Bridge
end PrimeTensor
