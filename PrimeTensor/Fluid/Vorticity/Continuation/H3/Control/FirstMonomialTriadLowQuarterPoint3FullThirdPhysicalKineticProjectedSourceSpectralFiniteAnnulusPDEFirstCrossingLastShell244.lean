import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalBandKineticNinthEighth244
import Mathlib.Tactic

/-!
# Kinetic cost of the last shell at the canonical first annular crossing

Minimality identifies the *last integer Fourier shell* carrying a strictly
positive dissipation increment. What is quantitatively forced is the
overshoot past the three-quarter-cubic threshold. That overshoot can be
arbitrarily small: a uniform quarter-cubic floor on the last shell does NOT
follow from first-crossing minimality.

We localize that exact overshoot to the raw Fourier kinetic mass of the
single shell and retain it on actual strictly interior physical snapshots.
The previous full annular ninth/eighth bound remains conditional and does
not by itself lower-bound the last shell's mass uniformly.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

-- Imported instances declared `local` do not cross module boundaries.
noncomputable local instance axisFintypeFirstCrossingLastShell244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceFirstCrossingLastShell244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Pure first-crossing arithmetic: the last integer shell has a strictly
positive increment, at least as large as the strict crossing overshoot.
No false fixed-fraction lower bound is introduced. -/
theorem h3Path_firstCrossing_lastShellOvershoot244
    (D : ℕ → ℝ) (n N : ℕ)
    (hnN : n ≤ N)
    (hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 < D N - D n)
    (hMinimal : ∀ m : ℕ, n ≤ m → m < N →
      D m - D n ≤ 3 * (((n : ℝ) + 1) ^ 3) / 4) :
    ∃ m : ℕ, N = m + 1 ∧ n ≤ m ∧
      0 < D N - D m ∧
      (D N - D n) - 3 * (((n : ℝ) + 1) ^ 3) / 4 ≤
        D N - D m := by
  have hnNstrict : n < N := by
    by_contra hNot
    have hNle : N ≤ n := Nat.le_of_not_gt hNot
    have hEq : N = n := Nat.le_antisymm hNle hnN
    rw [hEq] at hCross
    have hThreshold : 0 ≤ 3 * (((n : ℝ) + 1) ^ 3) / 4 := by
      positivity
    linarith only [hCross, hThreshold]
  let m : ℕ := N - 1
  have hmN : N = m + 1 := by
    dsimp only [m]
    omega
  have hnm : n ≤ m := by
    dsimp only [m]
    omega
  have hmLt : m < N := by
    omega
  have hBelow := hMinimal m hnm hmLt
  refine ⟨m, hmN, hnm, ?_, ?_⟩
  · linarith only [hCross, hBelow]
  · linarith only [hBelow]

/-- The physical dissipation of *any* finite Fourier annulus costs at most
four times the outer shifted eighth power times raw kinetic mass on exactly
that annulus. This retains the annular, not global, kinetic density. -/
theorem h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (R Q : ℝ) (hRQ : R ≤ Q) (hQ : 0 ≤ Q) :
    h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      4 * (Q + 1) ^ 8 *
        h3PathActualBandRawKineticMass244 R Q
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hBandNonneg : 0 ≤ h3PathActualBandRawKineticMass244 R Q G := by
    unfold h3PathActualBandRawKineticMass244
    apply integral_nonneg
    intro ξ
    unfold h3TerminalRawVelocityFourierTotalSquareDensity
    positivity
  have hQ2 : Q ^ 2 ≤ (Q + 1) ^ 2 := by
    nlinarith only [hQ]
  have hWeight := h3Path_radialSobolevCeiling_le_fourShiftSixth244 Q hQ
  have hWNonneg := (h3TerminalRadialSobolevWeightSquareCeiling_pos Q).le
  have hProduct : Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q ≤
      4 * (Q + 1) ^ 8 := by
    calc
      _ ≤ (Q + 1) ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q :=
        mul_le_mul_of_nonneg_right hQ2 hWNonneg
      _ ≤ (Q + 1) ^ 2 * (4 * (Q + 1) ^ 6) :=
        mul_le_mul_of_nonneg_left hWeight (sq_nonneg _)
      _ = 4 * (Q + 1) ^ 8 := by ring
  have hOriginal := h3Path_actualAnnularDissipation_le_bandRawKinetic244
    hH3 hClass t ht R Q hRQ hQ
  have hScaled := mul_le_mul_of_nonneg_right hProduct hBandNonneg
  dsimp only [G] at hScaled
  calc
    _ ≤ (Q ^ 2 * h3TerminalRadialSobolevWeightSquareCeiling Q) *
        h3PathActualBandRawKineticMass244 R Q
          (h3AuditActualSpectralVelocityTotal hH3 t) := hOriginal
    _ ≤ 4 * (Q + 1) ^ 8 *
        h3PathActualBandRawKineticMass244 R Q
          (h3AuditActualSpectralVelocityTotal hH3 t) := hScaled

/-- The actual *last* integer shell of a strict physical first crossing has
positive raw Fourier kinetic mass. The overshoot above the cubic threshold
is bounded by that shell's shifted eighth-power kinetic cost. -/
theorem h3Path_physicalFirstCrossing_lastShellKineticOvershoot244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n N : ℕ) (hnN : n ≤ N)
    (hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t))
    (hMinimal : ∀ m : ℕ, n ≤ m → m < N →
      h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
        3 * (((n : ℝ) + 1) ^ 3) / 4) :
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
          (h3AuditActualSpectralVelocityTotal hH3 t)) -
          3 * (((n : ℝ) + 1) ^ 3) / 4 ≤
        4 * (((N : ℝ) + 2) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((m : ℝ) + 1) ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let D : ℕ → ℝ := fun j =>
    h3PathActualLowRadialDissipation244 ((j : ℝ) + 1) G
  have hC : 3 * (((n : ℝ) + 1) ^ 3) / 4 < D N - D n := by
    simpa only [D, G] using hCross
  have hMin : ∀ m : ℕ, n ≤ m → m < N →
      D m - D n ≤ 3 * (((n : ℝ) + 1) ^ 3) / 4 := by
    intro m hnm hmN
    simpa only [D, G] using hMinimal m hnm hmN
  obtain ⟨m, hmN, hnm, hJump, hOver⟩ :=
    h3Path_firstCrossing_lastShellOvershoot244 D n N hnN hC hMin
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
  have hFactorNonneg : (0 : ℝ) ≤ 4 * (((N : ℝ) + 2) ^ 8) := by
    positivity
  have hMassPos : 0 < h3PathActualBandRawKineticMass244
      ((m : ℝ) + 1) ((N : ℝ) + 1) G := by
    by_contra hNot
    have hMassLe : h3PathActualBandRawKineticMass244
        ((m : ℝ) + 1) ((N : ℝ) + 1) G ≤ 0 := le_of_not_gt hNot
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos hFactorNonneg hMassLe
    linarith only [hJump, hShellBound, hNonpos]
  refine ⟨m, hmN, hnm, ?_, ?_, ?_⟩
  · simpa only [D, G] using hJump
  · simpa only [G] using hMassPos
  · have hCombined := hOver.trans hShellBound
    simpa only [D, G] using hCombined

/-- The genuine no-terminal-L²-trace first-crossing selector already
supplies the strict physical times needed for the last-shell cost.
All the statements refer to the same selected N and physical spectral G. -/
theorem h3Path_noL2Trace_minimalFirstCrossing_lastShellKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ),
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, ∃ m : ℕ, N n = m + 1 ∧ n ≤ m ∧
        0 < h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ∧
        0 < h3PathActualBandRawKineticMass244
          ((m : ℝ) + 1) ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ∧
        (h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          3 * (((n : ℝ) + 1) ^ 3) / 4 ≤
          4 * (((N n : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244
              ((m : ℝ) + 1) ((N n : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (τ n))) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_minimalQuadraticSharpClocks_retain_quarterHighTail244
      hH3 hClass hMass hNoTrace
  refine ⟨τ, N, hLimit, hTime, ?_⟩
  intro n
  rcases hAll n with ⟨hnN, _, _, _, _, _, _, hGap, hMinimal, _⟩
  have hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) := by
    dsimp only [h3PathCubicAnnulusActualGap244] at hGap
    linarith only [hGap]
  exact h3Path_physicalFirstCrossing_lastShellKineticOvershoot244
    hH3 hClass (τ n) (hTime n) n (N n) hnN hCross hMinimal

end
end PrimeTensor.FirstMonomialTriad
