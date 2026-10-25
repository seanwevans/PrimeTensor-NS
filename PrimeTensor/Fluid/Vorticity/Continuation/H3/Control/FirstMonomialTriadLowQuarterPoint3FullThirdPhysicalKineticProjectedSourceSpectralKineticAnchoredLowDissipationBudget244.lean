import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralQuantitativeTemporalDissipationWindow244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralMovingRadialDissipation244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Actual low-radial physical H³ dissipation has an anchored kinetic budget

The difficulty in promoting high-frequency terminal snapshots to a terminal
integral is not solved by continuity alone: narrow windows can carry
arbitrarily little integral. Here we use the low-frequency kinetic anchor
instead of assuming any high-order temporal continuity.

At each fixed physical radius ρ and strict anchor b, the physical low H³
dissipation is bounded at ALL later times by

  ρ² * K(ρ) * E₀(b),

where K(ρ) is the already-proved Sobolev spectral weight ceiling and E₀(b)
is actual kinetic energy. Hence the low-frequency dissipation integral on
any compact strict subinterval has an explicit length-times-ceiling upper
bound, provided its interval integrability is known.

By the exact physical partition, the integral of full H³ dissipation is at
most that explicit low-frequency budget plus integrated high-frequency
dissipation, when both integrals exist. No temporal continuity or lower
bound for an integrated high-frequency cost is hidden in this inequality.

Separately, the already-proved no-strong-kinetic-L²-trace moving-radial
sequence has HIGH radial physical dissipation strictly above (n+1)^3 on
that same sequence. This is an absolute, not merely normalized, lower bound.
It does not force any time-window lower bound without a persistence scale.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3KineticLowBudget244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3KineticLowBudget244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- At every strict later time, the actual low-frequency H³ viscous
square-mass is bounded by a kinetic anchor, uniformly in physical time. -/
theorem h3Path_actualLowRadialDissipation_le_kineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ t : ℝ, t ∈ Set.Ioo b T →
      h3PathActualLowRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
        ρ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b) := by
  intro t ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hLow := h3Path_actualLowRadialDissipation_le_squareLowMass244
    hH3 hClass t htClass ρ hρ
  have hMass :=
    h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
      hH3 hClass b hb ρ hρ t ht
  exact le_trans hLow (mul_le_mul_of_nonneg_left hMass (sq_nonneg ρ))

/-- The physical low-radial H³ dissipation integrated over any positive-time
interval has a uniform kinetic upper budget. The existing path class alone
is not used to assert the needed interval integrability of this scalar. -/
theorem h3Path_actualLowRadialDissipation_integral_le_kineticBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t : ℝ) (hs : s ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo b T) (hst : s ≤ t)
    (hInt : IntervalIntegrable
      (fun r : ℝ => h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) volume s t) :
    (∫ r in s..t, h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) ≤
      (t - s) * (ρ ^ 2 *
        (h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b)) := by
  let C : ℝ := ρ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling ρ *
      velocityH3Energy0At u b)
  have hCeiling : ∀ r : ℝ, r ∈ Set.Icc s t →
      h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r) ≤ C := by
    intro r hr
    have hrTail : r ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    exact h3Path_actualLowRadialDissipation_le_kineticAnchor244
      hH3 hClass b hb ρ hρ r hrTail
  have hConst : IntervalIntegrable (fun _ : ℝ => C) volume s t :=
    intervalIntegrable_const
  have hBound := intervalIntegral.integral_mono_on
    hst hInt hConst hCeiling
  dsimp only [C] at hBound ⊢
  simpa [mul_assoc, mul_left_comm, mul_comm] using hBound

/-- On any compact strict tail interval, the full physical H³ dissipation
budget is no larger than high-radial dissipation plus the explicit anchored
low-frequency cost. The two interval-integrability inputs remain visible. -/
theorem h3Path_physicalDissipation_integral_le_highPlusKineticBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t : ℝ) (hs : s ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo b T) (hst : s ≤ t)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume s t)
    (hHighInt : IntervalIntegrable
      (fun r : ℝ => h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) volume s t) :
    (∫ r in s..t, velocityH3DissipationAt u r) ≤
      (t - s) * (ρ ^ 2 *
        (h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b)) +
      (∫ r in s..t, h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) := by
  let C : ℝ := ρ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling ρ *
      velocityH3Energy0At u b)
  let H : ℝ → ℝ := fun r => h3PathActualHighRadialDissipation244 ρ
    (h3AuditActualSpectralVelocityTotal hH3 r)
  have hAbove : ∀ r : ℝ, r ∈ Set.Icc s t →
      velocityH3DissipationAt u r ≤ C + H r := by
    intro r hr
    have hrTail : r ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hrTail.1, hrTail.2⟩
    have hLow := h3Path_actualLowRadialDissipation_le_kineticAnchor244
      hH3 hClass b hb ρ hρ r hrTail
    have hPart := h3Path_actualRadialDissipation_partition244
      hH3 hClass r hrClass ρ
    dsimp only [C, H] at *
    linarith only [hLow, hPart]
  have hSumInt : IntervalIntegrable (fun r : ℝ => C + H r) volume s t :=
    intervalIntegrable_const.add hHighInt
  have hBound := intervalIntegral.integral_mono_on
    hst hDInt hSumInt hAbove
  rw [intervalIntegral.integral_add intervalIntegrable_const hHighInt] at hBound
  dsimp only [C, H] at hBound ⊢
  simpa [mul_assoc, mul_left_comm, mul_comm] using hBound

/-- The previously selected no-strong-kinetic-trace spectral escape witness
already has a cubic absolute lower bound on the HIGH radial component of
physical H³ dissipation, rather than only on the full dissipation. -/
theorem h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) := by
  obtain ⟨τ, hτ, hNear, hLimit, hMassEscape, _hFullD⟩ :=
    h3Path_physicalNoL2Trace_forces_movingRadialDissipationSequence244
      hH3 hClass hMass hNoTrace
  refine ⟨τ, hτ, hNear, hLimit, ?_⟩
  intro n
  let R : ℝ := (n : ℝ) + 1
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 (τ n)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hSpectral : R < h3PathActualSpectralHighRadialRemainder244 R G := by
    rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
    exact hMassEscape n
  have hHigh := h3Path_actualHighRadialDissipation_ge_squareHighMass244
    hH3 hClass (τ n) (hτ n) R hR.le
  have hScaled : R ^ 2 * R <
      R ^ 2 * h3PathActualSpectralHighRadialRemainder244 R G :=
    mul_lt_mul_of_pos_left hSpectral (pow_pos hR 2)
  have hCube : R ^ 3 <
      h3PathActualHighRadialDissipation244 R G := by
    calc
      R ^ 3 = R ^ 2 * R := by ring
      _ < R ^ 2 * h3PathActualSpectralHighRadialRemainder244 R G := hScaled
      _ ≤ h3PathActualHighRadialDissipation244 R G := hHigh
  exact hCube

end
end PrimeTensor.FirstMonomialTriad
