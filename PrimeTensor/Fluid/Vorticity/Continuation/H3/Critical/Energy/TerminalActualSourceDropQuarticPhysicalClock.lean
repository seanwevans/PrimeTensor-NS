import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropCofinalGradientEnergyGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropEndpointDissipationTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceSpectralPersistence
import Mathlib.Tactic

/-!
# Quartic-frequency physical PDE clock for actual H³ spectral velocity

The exact finite-radial physical momentum FTC and actual endpoint Fourier
H³ dissipation coercivity together control the *whole* weighted spectral
velocity increment on a radius-dependent time scale. For R >= 1 and
R^4 (s-t) <= 1, the Fourier weight polynomial W₃(R) <= 4 R^6 gives

  R² ‖U(t)-U(s)‖² <= 12 C² + 2 (D_{>R}(t) + D_{>R}(s)).

Here C is a physical projected-momentum source ceiling on [t,s]. This is
not an assumed full-H³ time-derivative or temporal Lipschitz estimate:
the physical PDE controls the low band and actual endpoint fourth-order
viscous dissipation controls the complementary Fourier difference.

The same estimate transfers to the ACTUAL highpass Fourier source difference
and simplifies the source-drop physical dissipation budget. No terminal-
uniform source ceiling or endpoint dissipation bound is inferred.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSourceDropQuartic
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSourceDropQuartic :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact H³ radial Sobolev polynomial grows at most as 4 R^6 above R=1.
The power is six, not eight: the extra R² in the spectral coercivity
produces the quartic physical-time scale. -/
theorem h3Critical_quarticClock_radialWeight_le_fourSixth
    (R : ℝ) (hR : 1 ≤ R) :
    h3TerminalRadialSobolevWeightSquareCeiling R ≤ 4 * R ^ 6 := by
  have hR2 : 1 ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R - 1)]
  have hR4 : R ^ 2 ≤ R ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hR2 (sq_nonneg R)
    nlinarith only [h]
  have hR6 : R ^ 4 ≤ R ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hR2 (sq_nonneg (R ^ 2))
    nlinarith only [h]
  dsimp only [h3TerminalRadialSobolevWeightSquareCeiling]
  linarith only [hR2, hR4, hR6]

/-- On the quartic clock R^4 Δ <= 1, the finite-band projected-PDE square
cost becomes independent of R after multiplication by R². -/
theorem h3Critical_quarticClock_scaledFiniteBandCost_le_twelve
    (R C Δ : ℝ) (hR : 1 ≤ R) (hΔ : 0 ≤ Δ)
    (hClock : R ^ 4 * Δ ≤ 1) :
    R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
      (C * Δ) ^ 2) ≤ 12 * C ^ 2 := by
  have hW := h3Critical_quarticClock_radialWeight_le_fourSixth R hR
  have hCoeff : R ^ 2 *
      (3 * h3TerminalRadialSobolevWeightSquareCeiling R) ≤
      12 * R ^ 8 := by
    have h3W := mul_le_mul_of_nonneg_left hW (by norm_num : 0 ≤ (3 : ℝ))
    calc
      R ^ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling R) ≤
          R ^ 2 * (3 * (4 * R ^ 6)) :=
        mul_le_mul_of_nonneg_left h3W (sq_nonneg R)
      _ = 12 * R ^ 8 := by ring
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR
  have hClockNonneg : 0 ≤ R ^ 4 * Δ :=
    mul_nonneg (pow_nonneg hRnonneg _) hΔ
  have hClockSq : (R ^ 4 * Δ) ^ 2 ≤ 1 := by
    simpa using (pow_le_pow_left₀ hClockNonneg hClock 2)
  have hScale : R ^ 8 * Δ ^ 2 ≤ 1 := by
    calc
      R ^ 8 * Δ ^ 2 = (R ^ 4 * Δ) ^ 2 := by ring
      _ ≤ 1 := hClockSq
  calc
    R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
      (C * Δ) ^ 2) =
        (R ^ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling R)) *
          (C * Δ) ^ 2 := by ring
    _ ≤ (12 * R ^ 8) * (C * Δ) ^ 2 :=
      mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _)
    _ = (12 * C ^ 2) * (R ^ 8 * Δ ^ 2) := by ring
    _ ≤ (12 * C ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hScale (by positivity)
    _ = 12 * C ^ 2 := by ring

/-- No full-H³ time-Lipschitz premise: on a quartic clock the actual
projected momentum equation controls the low Fourier band, while the
physical endpoint H³ viscous dissipation controls the entire high band.
This supplies an unconditional (relative to the energy class and local
source ceiling) spectral displacement budget at actual physical times. -/
theorem h3Critical_quarticClock_actualSpectralDisplacement_le_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s : ℝ) (ht : t ∈ Set.Ioo a T) (hs : s ∈ Set.Ioo a T)
    (hts : t ≤ s) (R C : ℝ) (hR : 1 ≤ R)
    (hClock : R ^ 4 * (s - t) ≤ 1)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    R ^ 2 *
      ‖h3AuditActualSpectralVelocityTotal hH3 t -
        h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 ≤
      12 * C ^ 2 +
        2 * (h3PathActualHighRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 t) +
          h3PathActualHighRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let U : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  let V : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 s
  let Low : ℝ := h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V
  let High : ℝ := h3Path_spectralTemporalHighRadialIntegral244 R U V
  let Cost : ℝ := (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
    (C * (s - t)) ^ 2
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hLow : Low ≤ Cost :=
    h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
      hH3 R (le_trans (by norm_num) hR) t s C ht0 hs0 hts hCeil
  have hFull : ‖U - V‖ ^ 2 ≤ Low + High := by
    dsimp only [Low, High]
    rw [h3Path_spectralTemporal_low_add_high_eq_total244]
    exact h3Path_spectralSupNorm_sq_le_squareEnergy244 (U - V)
  have hHigh : R ^ 2 * High ≤
      2 * (h3PathActualHighRadialDissipation244 R U +
        h3PathActualHighRadialDissipation244 R V) := by
    dsimp only [High, U, V]
    exact h3Critical_highTemporalMass_radiusSq_le_endpointDissipation
      hH3 hClass t s ht hs R (le_trans (by norm_num) hR)
  have hCost : R ^ 2 * Cost ≤ 12 * C ^ 2 := by
    dsimp only [Cost]
    exact h3Critical_quarticClock_scaledFiniteBandCost_le_twelve
      R C (s - t) hR (sub_nonneg.mpr hts) hClock
  have hLowScaled := mul_le_mul_of_nonneg_left hLow (sq_nonneg R)
  change R ^ 2 * ‖U - V‖ ^ 2 ≤
    12 * C ^ 2 +
      2 * (h3PathActualHighRadialDissipation244 R U +
        h3PathActualHighRadialDissipation244 R V)
  calc
    R ^ 2 * ‖U - V‖ ^ 2 ≤ R ^ 2 * (Low + High) :=
      mul_le_mul_of_nonneg_left hFull (sq_nonneg R)
    _ = R ^ 2 * Low + R ^ 2 * High := by ring
    _ ≤ 12 * C ^ 2 +
        2 * (h3PathActualHighRadialDissipation244 R U +
          h3PathActualHighRadialDissipation244 R V) := by
      linarith only [hLowScaled, hCost, hHigh]

/-- Actual Fourier highpass physical source inherits the quartic PDE
clock. Its spectral-state source coefficient A is exactly the established
nonlinear Lipschitz coefficient, not an assumed source time rate. -/
theorem h3Critical_quarticClock_highpassSourceTemporalDisplacement_le_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s : ℝ) (ht : t ∈ Set.Ioo a T) (hs : s ∈ Set.Ioo a T)
    (hts : t ≤ s) (ρ R C : ℝ) (i : Fin 3) (hR : 1 ≤ R)
    (hClock : R ^ 4 * (s - t) ≤ 1)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    R ^ 2 *
      ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t -
        h3CriticalActualProjectedHighpassFourierSource hH3 ρ i s‖ ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (12 * C ^ 2 +
          2 * (h3PathActualHighRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 t) +
            h3PathActualHighRadialDissipation244 R
              (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  let U : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  let V : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 s
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient * (‖U‖ + ‖V‖)
  let P : ℝ := ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t -
    h3CriticalActualProjectedHighpassFourierSource hH3 ρ i s‖
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have hP : P ≤ A * ‖U - V‖ := by
    dsimp only [P, A, U, V]
    exact h3Critical_actualHighpassSource_temporalSub_norm_le_spectral
      hH3 ρ i t s ht0 hs0
  have hSquare : P ^ 2 ≤ A ^ 2 * ‖U - V‖ ^ 2 := by
    calc
      P ^ 2 ≤ (A * ‖U - V‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hP 2
      _ = A ^ 2 * ‖U - V‖ ^ 2 := by ring
  have hState := h3Critical_quarticClock_actualSpectralDisplacement_le_physical
    hH3 hClass t s ht hs hts R C hR hClock hCeil
  have hA : 0 ≤ A ^ 2 := sq_nonneg A
  change R ^ 2 * P ^ 2 ≤ A ^ 2 *
    (12 * C ^ 2 +
      2 * (h3PathActualHighRadialDissipation244 R U +
        h3PathActualHighRadialDissipation244 R V))
  calc
    R ^ 2 * P ^ 2 ≤ R ^ 2 * (A ^ 2 * ‖U - V‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hSquare (sq_nonneg R)
    _ = A ^ 2 * (R ^ 2 * ‖U - V‖ ^ 2) := by ring
    _ ≤ A ^ 2 * (12 * C ^ 2 +
        2 * (h3PathActualHighRadialDissipation244 R U +
          h3PathActualHighRadialDissipation244 R V)) :=
      mul_le_mul_of_nonneg_left hState hA

/-- Source-driven high-radial dissipation collapse has a scale-normalized
physical PDE budget on any quartic-frequency time interval. No terminal
source ceiling or endpoint dissipation bound is asserted or hidden. -/
theorem h3Critical_sourceDrop_quarticClock_endpointDissipationBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C : ℝ) (hR : 1 ≤ R)
    (hClock : R ^ 4 * (s - t) ≤ 1)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    R ^ 2 *
      (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (12 * C ^ 2 +
          2 * (h3PathActualHighRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 t) +
            h3PathActualHighRadialDissipation244 R
              (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient *
    (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
  let Ccost : ℝ := (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
    (C * (s - t)) ^ 2
  let D : ℝ :=
    h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 t) +
    h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 s)
  have hOriginal := h3Critical_sourceDrop_forces_endpointPhysicalDissipationBudget
    hH3 hClass b hb ρ σ R hσ (le_trans (by norm_num) hR) i
    t s ht hs hts M C hCeil hPeak hDrop
  have hCost : R ^ 2 * Ccost ≤ 12 * C ^ 2 :=
    h3Critical_quarticClock_scaledFiniteBandCost_le_twelve
      R C (s - t) hR (sub_nonneg.mpr hts) hClock
  have hA : 0 ≤ A ^ 2 := sq_nonneg A
  change R ^ 2 *
    (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M) ^ 2 ≤
    A ^ 2 * (12 * C ^ 2 + 2 * D)
  calc
    _ ≤ A ^ 2 * (R ^ 2 * Ccost + 2 * D) := hOriginal
    _ ≤ A ^ 2 * (12 * C ^ 2 + 2 * D) := by
      apply mul_le_mul_of_nonneg_left _ hA
      linarith only [hCost]

end
end PrimeTensor.Bridge.Euclidean
