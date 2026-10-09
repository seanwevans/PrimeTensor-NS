import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceSharpCubicThreshold
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Energy.Kinetic.Monotonicity

/-!
# Full physical cubic-rate ceilings and kinetically improved anchors

The previously proved sharp necessary nonextension clock says, for every `q < 1`,

  q <= 3 K^2 (E₀(b)+1) (T-t)^2 (D(t)/E(t))^3

throughout a sufficiently late physical left-terminal tail. Here the raw
frequency rate `(T-t)^2 (D/E)^3` is separated from its kinetic anchor.

A terminal rate ceiling with anchored product STRICTLY below one therefore
forces continuation. The same argument works along ANY preselected terminal
sequence, including the existing fixed directed ten-source witness, without
selecting a different obstruction index. When canonical H³ energy data are
available, zeroth-order kinetic energy is antitone, so later anchors only
improve the threshold coefficient.

No new nonlinear sign or singularity-existence assertion is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The physical, anchor-independent normalized cubic-frequency rate. -/
noncomputable def h3PathCanonicalFullCubicRateAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : ℝ :=
  (T - t) ^ 2 *
    (velocityH3DissipationAt u t / velocityH3EnergyAt u t) ^ 3

/-- The strictly positive kinetic coefficient of the full cubic clock. -/
noncomputable def h3PathCanonicalKineticCubicCoefficientAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b : ℝ) : ℝ :=
  3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
    (velocityH3Energy0At u b + 1)

/-- The cubic rate is nonnegative at every physical time. -/
theorem h3PathCanonical_fullCubicRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) :
    0 ≤ h3PathCanonicalFullCubicRateAt u T t := by
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans (by norm_num) (one_le_velocityH3EnergyAt u t)
  unfold h3PathCanonicalFullCubicRateAt
  exact mul_nonneg (sq_nonneg (T - t))
    (pow_nonneg (div_nonneg hD hE) 3)

/-- The kinetic cubic coefficient is nonnegative with no terminal hypothesis. -/
theorem h3PathCanonical_kineticCubicCoefficient_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b : ℝ) :
    0 ≤ h3PathCanonicalKineticCubicCoefficientAt u b := by
  have hE0 : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  unfold h3PathCanonicalKineticCubicCoefficientAt
  positivity

/-- The sharp anchored terminal clock factors exactly into a kinetic
coefficient and the anchor-independent physical cubic rate. -/
theorem h3PathCanonical_fullCubicClock_eq_coefficient_mul_rate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) :
    h3PathCanonicalFullCubicTerminalClockAt u T b t =
      h3PathCanonicalKineticCubicCoefficientAt u b *
        h3PathCanonicalFullCubicRateAt u T t := by
  unfold h3PathCanonicalFullCubicTerminalClockAt
    h3PathCanonicalKineticCubicCoefficientAt
    h3PathCanonicalFullCubicRateAt
  ring

/-- A genuinely subcritical upper ceiling on the full physical cubic rate
rules out nonextension, with no assumptions about the signed-source branch. -/
theorem h3PathCanonical_smoothExtension_of_subcritical_fullCubicRateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (B : ℝ)
    (hUpper : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullCubicRateAt u T t ≤ B)
    (hSubcritical :
      h3PathCanonicalKineticCubicCoefficientAt u b * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  let q : ℝ :=
    (h3PathCanonicalKineticCubicCoefficientAt u b * B + 1) / 2
  have hq : q < 1 := by
    dsimp only [q]
    linarith only [hSubcritical]
  have hGap : h3PathCanonicalKineticCubicCoefficientAt u b * B < q := by
    dsimp only [q]
    linarith only [hSubcritical]
  have hFloor :=
    h3PathCanonical_fullCubicTerminalClock_eventually_ge_subunit
      hH3 hNoExtension hClass hb q hq
  have hCoefficient := h3PathCanonical_kineticCubicCoefficient_nonneg u b
  have hCeiling : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullCubicTerminalClockAt u T b t ≤
        h3PathCanonicalKineticCubicCoefficientAt u b * B := by
    filter_upwards [hUpper] with t ht
    rw [h3PathCanonical_fullCubicClock_eq_coefficient_mul_rate]
    exact mul_le_mul_of_nonneg_left ht hCoefficient
  obtain ⟨t, hFloorAt, hCeilingAt⟩ := (hFloor.and hCeiling).exists
  exact (not_lt_of_ge (le_trans hFloorAt hCeilingAt)) hGap

/-- A subcritical cubic-rate ceiling just along one *preselected* physical
terminal sequence is sufficient for smooth continuation. In particular the
sequence may be the original fixed directed signed-source witness. -/
theorem h3PathCanonical_smoothExtension_of_sequence_subcritical_fullCubicRateCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (tau : ℕ → ℝ)
    (hTau : Tendsto tau atTop (𝓝[<] T))
    (B : ℝ)
    (hUpper : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalFullCubicRateAt u T (tau n) ≤ B)
    (hSubcritical :
      h3PathCanonicalKineticCubicCoefficientAt u b * B < 1) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  let q : ℝ :=
    (h3PathCanonicalKineticCubicCoefficientAt u b * B + 1) / 2
  have hq : q < 1 := by
    dsimp only [q]
    linarith only [hSubcritical]
  have hGap : h3PathCanonicalKineticCubicCoefficientAt u b * B < q := by
    dsimp only [q]
    linarith only [hSubcritical]
  have hFloor := hTau.eventually
    (h3PathCanonical_fullCubicTerminalClock_eventually_ge_subunit
      hH3 hNoExtension hClass hb q hq)
  have hCoefficient := h3PathCanonical_kineticCubicCoefficient_nonneg u b
  have hCeiling : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalFullCubicTerminalClockAt u T b (tau n) ≤
        h3PathCanonicalKineticCubicCoefficientAt u b * B := by
    filter_upwards [hUpper] with n hn
    rw [h3PathCanonical_fullCubicClock_eq_coefficient_mul_rate]
    exact mul_le_mul_of_nonneg_left hn hCoefficient
  obtain ⟨n, hFloorAt, hCeilingAt⟩ := (hFloor.and hCeiling).exists
  exact (not_lt_of_ge (le_trans hFloorAt hCeilingAt)) hGap

/-- Later kinetic anchors have no larger cubic-clock coefficient, provided
the canonical H³ energy data supplying kinetic monotonicity are available. -/
theorem h3PathCanonical_kineticCubicCoefficient_antitoneOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T) :
    AntitoneOn (h3PathCanonicalKineticCubicCoefficientAt u)
      (Set.Ioo a T) := by
  intro b hb c hc hbc
  have hE0 :=
    (antitoneOn_velocityH3Energy0At_of_energyClass_canonical
      hClass hData) hb hc hbc
  unfold h3PathCanonicalKineticCubicCoefficientAt
  have hShift :
      velocityH3Energy0At u c + 1 ≤ velocityH3Energy0At u b + 1 := by
    linarith only [hE0]
  exact mul_le_mul_of_nonneg_left hShift (by positivity)

/-- Under canonical kinetic monotonicity, advancing the kinetic anchor
can only decrease the dimensionless clock at the same physical time. -/
theorem h3PathCanonical_fullCubicClock_antitone_in_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (hData : CanonicalH3EnergyDataOnTail u a T)
    {b c : ℝ}
    (hb : b ∈ Set.Ioo a T)
    (hc : c ∈ Set.Ioo a T)
    (hbc : b ≤ c)
    (t : ℝ) :
    h3PathCanonicalFullCubicTerminalClockAt u T c t ≤
      h3PathCanonicalFullCubicTerminalClockAt u T b t := by
  have hCoeff :=
    h3PathCanonical_kineticCubicCoefficient_antitoneOn
      hClass hData hb hc hbc
  have hRate := h3PathCanonical_fullCubicRate_nonneg u T t
  simpa only [h3PathCanonical_fullCubicClock_eq_coefficient_mul_rate] using
    (mul_le_mul_of_nonneg_right hCoeff hRate)

end
end Euclidean
end Bridge
end PrimeTensor
