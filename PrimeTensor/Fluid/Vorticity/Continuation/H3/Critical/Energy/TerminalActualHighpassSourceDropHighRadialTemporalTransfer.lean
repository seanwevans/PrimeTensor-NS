import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceSpectralDropObstruction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFourierTransfer244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialTemporalMass244
import Mathlib.Tactic

/-!
# The physical PDE forces high-frequency H³ spectral motion at source collapse

A projected highpass source peak cannot drop to its dissipation barrier without
moving the actual weighted H³ spectral velocity. The genuine Fourier square
energy of that temporal displacement is the sum of its low- and high-radial
parts. The physical projected momentum FTC provides an *automatic* rate bound
for the low-radial part from a local source ceiling. Thus the high-radial
part must absorb any deficit that the finite-band PDE clock cannot pay.

Unlike a full-H³ spectral-time Lipschitz hypothesis, the finite-band estimate
is already proved from the physical PDE. No terminal-uniform source ceiling,
full spectral derivative, or lower persistence width is inferred.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SourceDropHighMotion
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SourceDropHighMotion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact Fourier low/high alternative at two actual physical times.
The square of the actual source excess is paid by the full temporal spectral
square energy, with the genuine PDE source-difference coefficient. The radial
cutoff for this velocity difference is independent of both source and
high-dissipation cutoffs. -/
theorem h3Critical_sourceDrop_forces_temporalSpectralLowHighBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (M : ℝ)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (h3TerminalWeightedSpectralVelocityRadialSquareDefect R
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 s) +
        h3Path_spectralTemporalHighRadialIntegral244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let V : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 s
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient * (‖U‖ + ‖V‖)
  let P : ℝ :=
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M
  have hP : 0 ≤ P := sub_nonneg.mpr hPeak
  have hSource : P ≤ A * ‖U - V‖ := by
    dsimp only [P, A, U, V]
    exact h3Critical_sourceDriven_dissipationDrop_forces_spectralDisplacement
      hH3 hClass b hb ρ σ hσ i t s ht hs M hDrop
  have hSquare : P ^ 2 ≤ (A * ‖U - V‖) ^ 2 :=
    pow_le_pow_left₀ hP hSource 2
  have hState : ‖U - V‖ ^ 2 ≤
      h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V +
        h3Path_spectralTemporalHighRadialIntegral244 R U V := by
    rw [h3Path_spectralTemporal_low_add_high_eq_total244]
    exact h3Path_spectralSupNorm_sq_le_squareEnergy244 (U - V)
  change P ^ 2 ≤ A ^ 2 *
    (h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V +
      h3Path_spectralTemporalHighRadialIntegral244 R U V)
  calc
    P ^ 2 ≤ (A * ‖U - V‖) ^ 2 := hSquare
    _ = A ^ 2 * ‖U - V‖ ^ 2 := by ring
    _ ≤ A ^ 2 *
        (h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V +
          h3Path_spectralTemporalHighRadialIntegral244 R U V) :=
      mul_le_mul_of_nonneg_left hState (sq_nonneg A)

/-- A *physical* projected momentum source ceiling bounds the finite-radial
velocity motion by the already-established genuine PDE FTC. A source peak
whose high-H³ dissipation has fallen must therefore be explained by either
that explicitly priced low-frequency motion or the actual complementary
high-frequency Fourier squared difference. No full H³ temporal rate premise. -/
theorem h3Critical_sourceDrop_forces_highRadialSpectralMotion_or_PDEClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2 +
        h3Path_spectralTemporalHighRadialIntegral244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let V : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 s
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient * (‖U‖ + ‖V‖)
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 ht.1), ht.2⟩
  have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hs.1), hs.2⟩
  have hLow : h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
        (C * (s - t)) ^ 2 :=
    h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
      hH3 R hR t s C ht0 hs0 hts hCeil
  have hTotal :=
    h3Critical_sourceDrop_forces_temporalSpectralLowHighBudget
      hH3 hClass b hb ρ σ R hσ i t s ht hs M hPeak hDrop
  change (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      A ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2 +
        h3Path_spectralTemporalHighRadialIntegral244 R U V)
  calc
    _ ≤ A ^ 2 *
        (h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V +
          h3Path_spectralTemporalHighRadialIntegral244 R U V) := hTotal
    _ ≤ A ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2 +
        h3Path_spectralTemporalHighRadialIntegral244 R U V) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_left hLow
          (h3Path_spectralTemporalHighRadialIntegral244 R U V))
        (sq_nonneg A)

/-- Contrapositive persistence criterion: if finite-band PDE motion and the
actual high-frequency spectral temporal displacement together cannot pay the
squared highpass source margin, the high-H³ dissipation CANNOT have dropped.
The high-frequency displacement ceiling J is deliberately explicit; the PDE
has supplied only the finite-band time modulus, not a global fourth-order
control on the complementary band. -/
theorem h3Critical_sourceDrop_PDEClock_and_highRadialCeiling_preclude_drop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C J : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hHigh : h3Path_spectralTemporalHighRadialIntegral244 R
      (h3AuditActualSpectralVelocityTotal hH3 t)
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ J)
    (hGap :
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2 + J) <
      (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2) :
    M < h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) := by
  by_contra hNot
  have hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M :=
    le_of_not_gt hNot
  have hBound :=
    h3Critical_sourceDrop_forces_highRadialSpectralMotion_or_PDEClock
      hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C hCeil
      hPeak hDrop
  have hA : 0 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 :=
    sq_nonneg _
  have hUpper := mul_le_mul_of_nonneg_left
    (add_le_add_right hHigh
      ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
        (C * (s - t)) ^ 2)) hA
  exact (not_lt_of_ge (hBound.trans hUpper)) hGap

end
end PrimeTensor.Bridge.Euclidean
