import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceSpectralPersistence
import Mathlib.Tactic

/-!
# Source-driven dissipation drop forces actual H³ spectral velocity motion

The previous module provides a quantitative upper bound for changes of the
actual Fourier highpass projected source, in terms of the genuine weighted H³
spectral state difference. Here the kinetic-anchored Navier--Stokes projected
source estimate is used in the opposite direction: if actual high-radial H³
dissipation falls at time s to M or below, the genuine Fourier source norm at
s cannot exceed the explicit kinetic barrier B. Therefore a preceding highpass
source peak V>B forces an actual spectral H³ displacement of at least

  (V-B) / (3+C_L (‖U(t)‖+‖U(s)‖)).

Under additional *endpoint* spectral-amplitude and spectral temporal-increment
bounds this also gives a lower bound for the time needed for such a drop.
Neither a uniform terminal spectral rate nor a lower bound on already selected
source-driven interval widths is claimed; those are still missing PDE inputs.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SourceSpectralDrop
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SourceSpectralDrop :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact pointwise barrier in the reverse direction. If high-radial physical
H³ dissipation is at most M, the ACTUAL source highpass Fourier norm lies
below the kinetic-anchored budget, for arbitrary independent radii ρ, σ. -/
theorem h3Critical_sourceDriven_dissipationDrop_highpassNorm_le_barrier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (s : ℝ) (hs : s ∈ Set.Ioo b T) (M : ℝ)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i s‖ ≤
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M := by
  have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have h := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [h]
  have hInner :
      1 + 6 * velocityH3Energy0At u b +
        3 * (σ ^ 2 *
          (h3TerminalRadialSobolevWeightSquareCeiling σ *
            velocityH3Energy0At u b) +
          h3PathActualHighRadialDissipation244 σ
            (h3AuditActualSpectralVelocityTotal hH3 s)) ≤
      1 + 6 * velocityH3Energy0At u b +
        3 * (σ ^ 2 *
          (h3TerminalRadialSobolevWeightSquareCeiling σ *
            velocityH3Energy0At u b) + M) := by
    linarith only [hDrop]
  calc
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i s‖ ≤
        (3 + h3AuditInitialLerayEnergyCoefficient) *
          (1 + 6 * velocityH3Energy0At u b +
            3 * (σ ^ 2 *
              (h3TerminalRadialSobolevWeightSquareCeiling σ *
                velocityH3Energy0At u b) +
              h3PathActualHighRadialDissipation244 σ
                (h3AuditActualSpectralVelocityTotal hH3 s))) :=
      h3Critical_actualHighpassFourierSource_norm_le_highRadialDissipation
        hH3 hClass b hb ρ σ hσ i s hs
    _ ≤ (3 + h3AuditInitialLerayEnergyCoefficient) *
          (1 + 6 * velocityH3Energy0At u b +
            3 * (σ ^ 2 *
              (h3TerminalRadialSobolevWeightSquareCeiling σ *
                velocityH3Energy0At u b) + M)) :=
      mul_le_mul_of_nonneg_left hInner hCoeff
    _ ≤ h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M :=
      le_max_left _ _

/-- A genuine physical high-radial dissipation drop necessarily consumes the
preceding highpass Fourier SOURCE excess by moving the ACTUAL weighted H³
spectral velocity. The coefficient is the established nonlinear PDE source
Lipschitz constant, evaluated at the two actual physical times. No temporal
rate or spectral-amplitude ceiling is assumed. -/
theorem h3Critical_sourceDriven_dissipationDrop_forces_spectralDisplacement
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (M : ℝ)
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) *
        ‖h3AuditActualSpectralVelocityTotal hH3 t -
          h3AuditActualSpectralVelocityTotal hH3 s‖ := by
  let H : ℝ → H3FourierComplexL2 := fun r =>
    h3CriticalActualProjectedHighpassFourierSource hH3 ρ i r
  let B : ℝ := h3CriticalSourceDrivenHighDissipationBarrier
    (velocityH3Energy0At u b) σ M
  have hLow : ‖H s‖ ≤ B :=
    h3Critical_sourceDriven_dissipationDrop_highpassNorm_le_barrier
      hH3 hClass b hb ρ σ hσ i s hs M hDrop
  have hTriangle : ‖H t‖ ≤ ‖H s‖ + ‖H t - H s‖ := by
    calc
      ‖H t‖ = ‖H s + (H t - H s)‖ := by
        congr 1
        abel
      _ ≤ ‖H s‖ + ‖H t - H s‖ := norm_add_le _ _
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 ht.1), ht.2⟩
  have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hs.1), hs.2⟩
  have hSourceDiff : ‖H t - H s‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) *
        ‖h3AuditActualSpectralVelocityTotal hH3 t -
          h3AuditActualSpectralVelocityTotal hH3 s‖ :=
    h3Critical_actualHighpassSource_temporalSub_norm_le_spectral
      hH3 ρ i t s ht0 hs0
  dsimp only [H, B] at hLow hTriangle hSourceDiff ⊢
  linarith only [hLow, hTriangle, hSourceDiff]

/-- Endpoint amplitude ceilings and a spectral-time increment estimate force
a definite elapsed time before the high-radial physical dissipation can fall
to M. This isolates the remaining hard PDE issue: proving a sufficiently
small RATE L, without assuming its terminal uniformity. -/
theorem h3Critical_sourceDriven_dissipationDrop_forces_temporalCost
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (M E L : ℝ) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hEt : ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ≤ E)
    (hEs : ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hMotion : ‖h3AuditActualSpectralVelocityTotal hH3 t -
      h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ L * (s - t))
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M ≤
      (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) *
        L * (s - t) := by
  have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
    h3AuditInitialLerayEnergyCoefficient_nonneg
  have hSum :
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ 2 * E := by
    linarith only [hEt, hEs]
  have hCoeff :
      3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖) ≤
      3 + h3AuditInitialLerayEnergyCoefficient * (2 * E) := by
    have hm := mul_le_mul_of_nonneg_left hSum hCL
    linarith only [hm]
  have hCoeffNonneg :
      0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient * (2 * E) := by
    have hMul : 0 ≤ h3AuditInitialLerayEnergyCoefficient * (2 * E) :=
      mul_nonneg hCL (by positivity)
    linarith only [hMul]
  calc
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) *
        ‖h3AuditActualSpectralVelocityTotal hH3 t -
          h3AuditActualSpectralVelocityTotal hH3 s‖ :=
      h3Critical_sourceDriven_dissipationDrop_forces_spectralDisplacement
        hH3 hClass b hb ρ σ hσ i t s ht hs M hDrop
    _ ≤ (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) *
        ‖h3AuditActualSpectralVelocityTotal hH3 t -
          h3AuditActualSpectralVelocityTotal hH3 s‖ :=
      mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)
    _ ≤ (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) *
        (L * (s - t)) :=
      mul_le_mul_of_nonneg_left hMotion hCoeffNonneg
    _ = (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) *
        L * (s - t) := by ring

/-- If L is positive, the PDE obstruction supplies an explicit *lower* bound
on the elapsed time necessary for a dissipation drop. This applies to any
two actual strict physical times, not just a selected common interval. -/
theorem h3Critical_sourceDriven_dissipationDrop_minimalElapsedTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (M E L : ℝ) (hE : 0 ≤ E) (hL : 0 < L)
    (hEt : ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ≤ E)
    (hEs : ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E)
    (hMotion : ‖h3AuditActualSpectralVelocityTotal hH3 t -
      h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ L * (s - t))
    (hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M) :
    (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) /
        ((3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L) ≤
      s - t := by
  have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
    h3AuditInitialLerayEnergyCoefficient_nonneg
  have hMul : 0 ≤ h3AuditInitialLerayEnergyCoefficient * (2 * E) :=
    mul_nonneg hCL (by positivity)
  have hCoeff : 0 < 3 + h3AuditInitialLerayEnergyCoefficient * (2 * E) := by
    linarith only [hMul]
  have hDen : 0 <
      (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L :=
    mul_pos hCoeff hL
  apply (div_le_iff₀ hDen).2
  calc
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M ≤
      (3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L * (s - t) :=
      h3Critical_sourceDriven_dissipationDrop_forces_temporalCost
        hH3 hClass b hb ρ σ hσ i t s ht hs M E L hE hL.le
        hEt hEs hMotion hDrop
    _ = (s - t) *
        ((3 + h3AuditInitialLerayEnergyCoefficient * (2 * E)) * L) := by ring

end
end PrimeTensor.Bridge.Euclidean
