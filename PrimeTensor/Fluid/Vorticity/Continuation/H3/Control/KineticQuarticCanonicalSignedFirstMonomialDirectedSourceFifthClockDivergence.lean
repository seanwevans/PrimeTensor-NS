import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceCanonicalKineticLimitClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Physical.Clocks

/-!
# Fifth-power physical H³ dissipation clock

Hypothetical nonextension already forces both

    (T-t) E(t) -> +infinity

and, under canonical H³ energy data, the sharp terminal kinetic-clock
threshold

    C_* (T-t)^2 (D(t)/E(t))^3 >= 1/2

eventually throughout the *whole* physical left terminal neighborhood.
The exact algebraic product of this cubic rate with the cube of the
physical energy clock is

    (T-t)^5 D(t)^3.

Because the energy clock diverges, the fifth-power cubic dissipation
clock diverges as well. This is stronger than mere divergence of
`(T-t) D(t)`; it is an exponent-free formulation of dissipation growing
faster than the critical `(T-t)^(-5/3)` scale. Its negation as an
eventual (or sampled) finite ceiling is a sufficient continuation test.
The original fixed directed ten-source witness and both PDE source
alternatives remain intact. No PDE sign or blowup existence is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Fifth-power physical width multiplied by the cube of full H³
dissipation. The exponent pair `(5,3)` avoids fractional powers. -/
noncomputable def h3PathCanonicalFullDissipationFifthClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : ℝ :=
  (T - t) ^ 5 * velocityH3DissipationAt u t ^ 3

/-- Algebraic bridge: the cubic frequency-rate clock multiplied by the
cube of the physical full-energy clock is exactly the fifth-power
physical dissipation clock. Full energy is at least one, so division
is legitimate at every physical time. -/
theorem h3PathCanonical_fullCubicRate_mul_energyClock_cube_eq_fifthClock
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) :
    h3PathCanonicalFullCubicRateAt u T t *
        ((T - t) * velocityH3EnergyAt u t) ^ 3 =
      h3PathCanonicalFullDissipationFifthClockAt u T t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u t)
  have hENe : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEPos
  unfold h3PathCanonicalFullCubicRateAt
    h3PathCanonicalFullDissipationFifthClockAt
  field_simp [hENe] <;> ring

/-- Under hypothetical nonextension, canonical kinetic-energy data
force the full physical fifth-power dissipation clock to diverge on
the ENTIRE strict left terminal tail, not just an extracted sequence. -/
theorem h3PathCanonical_fullDissipationFifthClock_tendsto_atTop_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T) :
    Tendsto (h3PathCanonicalFullDissipationFifthClockAt u T)
      (𝓝[<] T) atTop := by
  let C : ℝ := h3PathCanonicalKineticLimitCubicCoefficient
    (h3PathCanonicalTerminalKineticEnergyAt u a T)
  have hCPos : 0 < C := by
    dsimp only [C]
    exact h3PathCanonical_kineticLimitCubicCoefficient_pos _
      (h3PathCanonical_terminalKineticEnergy_nonneg hClass)
  have hFloor : ∀ᶠ t : ℝ in 𝓝[<] T,
      (1 / 2 : ℝ) ≤ C * h3PathCanonicalFullCubicRateAt u T t := by
    simpa only [C] using
      (h3PathCanonical_canonicalKineticLimit_sharpCubicClock
        hH3 hNoExtension hClass hData (1 / 2) (by norm_num))
  have hEnergyClock : Tendsto
      (fun t : ℝ => (T - t) * velocityH3EnergyAt u t)
      (𝓝[<] T) atTop :=
    velocityH3EnergyPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hCube : Tendsto
      (fun t : ℝ => ((T - t) * velocityH3EnergyAt u t) ^ 3)
      (𝓝[<] T) atTop := by
    have hPower : Tendsto (fun x : ℝ => x ^ 3) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)
    exact hPower.comp hEnergyClock
  refine tendsto_atTop.2 ?_
  intro M
  have hLarge : ∀ᶠ t : ℝ in 𝓝[<] T,
      2 * C * max M 0 ≤
        ((T - t) * velocityH3EnergyAt u t) ^ 3 :=
    (tendsto_atTop.1 hCube) (2 * C * max M 0)
  filter_upwards [hFloor, hLarge] with t ht hLargeT
  have hMNonneg : 0 ≤ max M 0 := le_max_right M 0
  have hLowerNonneg : 0 ≤ 2 * C * max M 0 := by
    exact mul_nonneg (mul_nonneg (by norm_num) hCPos.le) hMNonneg
  have hCubeNonneg : 0 ≤ ((T - t) * velocityH3EnergyAt u t) ^ 3 :=
    le_trans hLowerNonneg hLargeT
  have hScale := mul_le_mul_of_nonneg_right ht hCubeNonneg
  have hHalf : C * max M 0 ≤
      (1 / 2 : ℝ) * ((T - t) * velocityH3EnergyAt u t) ^ 3 := by
    nlinarith only [hLargeT]
  have hIdentity :
      (C * h3PathCanonicalFullCubicRateAt u T t) *
          ((T - t) * velocityH3EnergyAt u t) ^ 3 =
        C * h3PathCanonicalFullDissipationFifthClockAt u T t := by
    calc
      (C * h3PathCanonicalFullCubicRateAt u T t) *
          ((T - t) * velocityH3EnergyAt u t) ^ 3 =
        C * (h3PathCanonicalFullCubicRateAt u T t *
          ((T - t) * velocityH3EnergyAt u t) ^ 3) := by ring
      _ = C * h3PathCanonicalFullDissipationFifthClockAt u T t := by
        rw [h3PathCanonical_fullCubicRate_mul_energyClock_cube_eq_fifthClock]
  have hScaled : C * max M 0 ≤
      C * h3PathCanonicalFullDissipationFifthClockAt u T t := by
    calc
      C * max M 0 ≤
          (1 / 2 : ℝ) * ((T - t) * velocityH3EnergyAt u t) ^ 3 := hHalf
      _ ≤ (C * h3PathCanonicalFullCubicRateAt u T t) *
          ((T - t) * velocityH3EnergyAt u t) ^ 3 := hScale
      _ = C * h3PathCanonicalFullDissipationFifthClockAt u T t := hIdentity
  have hRight : max M 0 * C ≤
      h3PathCanonicalFullDissipationFifthClockAt u T t * C := by
    calc
      max M 0 * C = C * max M 0 := by ring
      _ ≤ C * h3PathCanonicalFullDissipationFifthClockAt u T t := hScaled
      _ = h3PathCanonicalFullDissipationFifthClockAt u T t * C := by ring
  have hBound : max M 0 ≤ h3PathCanonicalFullDissipationFifthClockAt u T t :=
    (mul_le_mul_iff_of_pos_right hCPos).mp hRight
  exact (le_max_left M 0).trans hBound

/-- An eventual finite ceiling on the physical fifth-power cubic
dissipation clock contradicts the necessary nonextension divergence,
so it gives smooth continuation with canonical H³ energy data. -/
theorem h3PathCanonical_smoothExtension_of_fifthDissipationClock_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hCeiling : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullDissipationFifthClockAt u T t ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hDiverges :=
    h3PathCanonical_fullDissipationFifthClock_tendsto_atTop_of_noExtension
      hH3 hNoExtension hClass hData
  have hAbove : ∀ᶠ t : ℝ in 𝓝[<] T,
      B + 1 ≤ h3PathCanonicalFullDissipationFifthClockAt u T t :=
    hDiverges.eventually (eventually_ge_atTop (B + 1))
  obtain ⟨t, htAbove, htBelow⟩ := (hAbove.and hCeiling).exists
  linarith only [htAbove, htBelow]

/-- A finite fifth-power cubic dissipation ceiling even along a
preselected left-terminal sequence forces continuation. -/
theorem h3PathCanonical_smoothExtension_of_sequence_fifthDissipationClock_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (hCeiling : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalFullDissipationFifthClockAt u T (tau n) ≤ B) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hDiverges :=
    (h3PathCanonical_fullDissipationFifthClock_tendsto_atTop_of_noExtension
      hH3 hNoExtension hClass hData).comp hTau
  have hAbove : ∀ᶠ n : ℕ in atTop,
      B + 1 ≤ h3PathCanonicalFullDissipationFifthClockAt u T (tau n) :=
    hDiverges.eventually (eventually_ge_atTop (B + 1))
  obtain ⟨n, hnAbove, hnBelow⟩ := (hAbove.and hCeiling).exists
  linarith only [hnAbove, hnBelow]

/-- The unchanged directed ten-source obstruction witness also exhibits
the fifth-power physical dissipation escape, together with the sharp
kinetic-limit cubic floor, three critical clocks and both exhaustive
source alternatives. -/
theorem h3PathCanonical_fixedDirectedSource_fifthDissipationClock_withPhysicalAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (tau : ℕ → ℝ),
      (∀ n : ℕ,
        tau n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (tau n) i /
            (9 * velocityH3EnergyAt u (tau n))) ∧
      Tendsto tau atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (tau n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullToTopPhysicalLengthRatioAt u (tau n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullDissipationFifthClockAt u T (tau n))
        atTop atTop ∧
      (∀ q : ℝ, q < 1 →
        ∀ᶠ n : ℕ in atTop,
          q ≤ h3PathCanonicalKineticLimitCubicCoefficient
            (h3PathCanonicalTerminalKineticEnergyAt u a T) *
              h3PathCanonicalFullCubicRateAt u T (tau n)) ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (tau n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (tau n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientTopShareClockAt u T b (tau n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (tau n) j r) /
                  velocityH3EnergyAt u (tau n))) := by
  obtain ⟨i, tau, hWitness, hTauT, hTopT, hLengthRatioT,
    hSharp, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_canonicalKineticLimitSharpCubicClock
      hH3 hNoExtension hClass hData hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hFifth :=
    (h3PathCanonical_fullDissipationFifthClock_tendsto_atTop_of_noExtension
      hH3 hNoExtension hClass hData).comp hTauLT
  exact ⟨i, tau, hWitness, hTauT, hTopT, hLengthRatioT,
    hFifth, hSharp, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
