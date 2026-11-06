import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMinimalAttainedClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFirstCrossingShellPigeonhole244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFirstCrossingLastShell244
import Mathlib.Tactic

/-!
# Exact kinetic carrier at the first arbitrary-profile annular crossing

The last integer shell carries positive raw kinetic Fourier mass, but the
strict overshoot beyond M/2 can be arbitrarily small. In addition, a shell
inside the first crossing carries a width-averaged M/2 dissipation cost.
The shell-frequency eighth-power factor is the actual old physical one.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeProfileFirstShell244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceProfileFirstShell244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Scalar first crossing at an arbitrary positive height A/2. The last
shell pays the exact (possibly arbitrarily small) crossing overshoot. -/
theorem thirdFull_profileFirstCrossing_lastShellOvershoot244
    (D : ℕ → ℝ) (n N : ℕ) (A : ℝ)
    (hnN : n ≤ N) (hA : 0 < A)
    (hCross : A / 2 < D N - D n)
    (hMinimal : ∀ m : ℕ, n ≤ m → m < N → D m - D n ≤ A / 2) :
    ∃ m : ℕ, N = m + 1 ∧ n ≤ m ∧
      0 < D N - D m ∧
      (D N - D n) - A / 2 ≤ D N - D m := by
  have hnNstrict : n < N := by
    by_contra hNot
    have hNle : N ≤ n := Nat.le_of_not_gt hNot
    have hEq : N = n := Nat.le_antisymm hNle hnN
    rw [hEq] at hCross
    linarith only [hCross, hA]
  let m : ℕ := N - 1
  have hmN : N = m + 1 := by
    dsimp only [m]
    omega
  have hnm : n ≤ m := by
    dsimp only [m]
    omega
  have hmLt : m < N := by omega
  have hBelow := hMinimal m hnm hmLt
  refine ⟨m, hmN, hnm, ?_, ?_⟩
  · linarith only [hCross, hBelow]
  · linarith only [hBelow]

/-- Positive raw physical kinetic mass in the very last shell of the
minimal outer crossing, with the exact nonuniform overshoot cost. -/
theorem thirdFullPhysical_profileFirstCrossing_lastShellKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n N : ℕ) (A : ℝ) (hA : 0 < A)
    (hnN : n ≤ N)
    (hCross : A / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t))
    (hMinimal : ∀ m : ℕ, n ≤ m → m < N →
      h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤ A / 2) :
    ∃ m : ℕ, N = m + 1 ∧ n ≤ m ∧
      0 < h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      0 < h3PathActualBandRawKineticMass244
        ((m : ℝ) + 1) ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t)) - A / 2 ≤
        4 * (((N : ℝ) + 2) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((m : ℝ) + 1) ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let D : ℕ → ℝ := fun j =>
    h3PathActualLowRadialDissipation244 ((j : ℝ) + 1) G
  have hC : A / 2 < D N - D n := by
    simpa only [D, G] using hCross
  have hMin : ∀ m : ℕ, n ≤ m → m < N → D m - D n ≤ A / 2 := by
    intro m hnm hmN
    simpa only [D, G] using hMinimal m hnm hmN
  obtain ⟨m, hmN, hnm, hJump, hOver⟩ :=
    thirdFull_profileFirstCrossing_lastShellOvershoot244
      D n N A hnN hA hC hMin
  have hmLt : m < N := by omega
  have hmCast : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmLt.le
  have hRQ : ((m : ℝ) + 1) ≤ ((N : ℝ) + 1) := by
    linarith only [hmCast]
  have hQ : 0 ≤ ((N : ℝ) + 1) := by positivity
  have hShell := h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    hH3 hClass t ht ((m : ℝ) + 1) ((N : ℝ) + 1) hRQ hQ
  have hShellBound : D N - D m ≤
      4 * (((N : ℝ) + 2) ^ 8) *
        h3PathActualBandRawKineticMass244
          ((m : ℝ) + 1) ((N : ℝ) + 1) G := by
    dsimp only [D, G] at hShell ⊢
    convert hShell using 1 <;> ring
  have hFactor : 0 ≤ 4 * (((N : ℝ) + 2) ^ 8) := by positivity
  have hMassPos : 0 < h3PathActualBandRawKineticMass244
      ((m : ℝ) + 1) ((N : ℝ) + 1) G := by
    by_contra hNot
    have hMassLe : h3PathActualBandRawKineticMass244
        ((m : ℝ) + 1) ((N : ℝ) + 1) G ≤ 0 := le_of_not_gt hNot
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos hFactor hMassLe
    linarith only [hJump, hShellBound, hNonpos]
  refine ⟨m, hmN, hnm, ?_, ?_, ?_⟩
  · simpa only [D, G] using hJump
  · simpa only [G] using hMassPos
  · have hCombined := hOver.trans hShellBound
    simpa only [D, G] using hCombined

/-- Somewhere in the minimal crossing annulus the actual kinetic Fourier
mass pays the positive M/2 height, divided by bandwidth and an eighth
power of that shell's upper frequency. This is stronger than positivity
alone, though not a frequency-independent mass floor. -/
theorem thirdFullPhysical_profileFirstCrossing_averagedKineticShell244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n N : ℕ) (A : ℝ) (hA : 0 < A)
    (hnN : n ≤ N)
    (hCross : A / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ m : ℕ, n ≤ m ∧ m < N ∧
      0 < h3PathActualBandRawKineticMass244
        ((m : ℝ) + 1) ((m : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      A / 2 < ((N - n : ℕ) : ℝ) *
        (4 * (((m : ℝ) + 3) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((m : ℝ) + 1) ((m : ℝ) + 2)
              (h3AuditActualSpectralVelocityTotal hH3 t)) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let D : ℕ → ℝ := fun j =>
    h3PathActualLowRadialDissipation244 ((j : ℝ) + 1) G
  have hnNstrict : n < N := by
    by_contra hNot
    have hNle : N ≤ n := Nat.le_of_not_gt hNot
    have hEq : N = n := Nat.le_antisymm hNle hnN
    rw [hEq] at hCross
    linarith only [hCross, hA]
  have hCrossD : A / 2 < D N - D n := by
    simpa only [D, G] using hCross
  obtain ⟨m, hnm, hmN, hAvg⟩ :=
    h3Path_finiteCrossing_exists_widthAveragedShell244
      D n N hnNstrict (A / 2) hCrossD
  have hShell := h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    hH3 hClass t ht ((m : ℝ) + 1) ((m : ℝ) + 2)
    (by linarith) (by positivity)
  have hShellBound : D (m + 1) - D m ≤
      4 * (((m : ℝ) + 3) ^ 8) *
        h3PathActualBandRawKineticMass244
          ((m : ℝ) + 1) ((m : ℝ) + 2) G := by
    dsimp only [D, G] at hShell ⊢
    convert hShell using 1 <;> push_cast <;> ring
  have hL : 0 ≤ ((N - n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hCost : A / 2 < ((N - n : ℕ) : ℝ) *
      (4 * (((m : ℝ) + 3) ^ 8) *
        h3PathActualBandRawKineticMass244
          ((m : ℝ) + 1) ((m : ℝ) + 2) G) :=
    lt_of_lt_of_le hAvg (mul_le_mul_of_nonneg_left hShellBound hL)
  have hMassPos : 0 < h3PathActualBandRawKineticMass244
      ((m : ℝ) + 1) ((m : ℝ) + 2) G := by
    by_contra hNot
    have hLe : h3PathActualBandRawKineticMass244
        ((m : ℝ) + 1) ((m : ℝ) + 2) G ≤ 0 := le_of_not_gt hNot
    have hFactor : 0 ≤ ((N - n : ℕ) : ℝ) *
        (4 * (((m : ℝ) + 3) ^ 8)) := by positivity
    have hNonpos : ((N - n : ℕ) : ℝ) *
        (4 * (((m : ℝ) + 3) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((m : ℝ) + 1) ((m : ℝ) + 2) G) ≤ 0 := by
      calc
        _ = (((N - n : ℕ) : ℝ) * (4 * (((m : ℝ) + 3) ^ 8))) *
          h3PathActualBandRawKineticMass244
            ((m : ℝ) + 1) ((m : ℝ) + 2) G := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hFactor hLe
    linarith only [hCost, hNonpos, hA]
  exact ⟨m, hnm, hmN, by simpa only [G] using hMassPos,
    by simpa only [G] using hCost⟩

end
end PrimeTensor.FirstMonomialTriad
