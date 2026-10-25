import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedCubicFixedCorridor244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralNormalizedDissipationClock244
import Mathlib.Tactic

/-!
# Synchronizing the cofinal high-H³-energy branch with moving radial mass

The fixed four-channel corridor is a disjunction of COFINAL phenomena, not
an intersection theorem for independently selected terminal witnesses.
The high-physical-H³-energy arm is different: the kinetic anchor bounds
low-radial weighted Fourier mass on every strict terminal subtail.
Consequently an appropriately high *physical* energy threshold forces
high-radial mass dominance AND a cubic physical dissipation clock at the
SAME time. We choose that threshold BEFORE selecting the terminal time.

This yields a single moving-cutoff sequence on the cofinal high-energy arm
whose normalized physical dissipation D_H3/E_H3 tends to infinity.
No assertion is made that the gradient or interpolation cofinal sequences
intersect the separately obtained radial-mass witness, and neither
nonextension nor strong L²-trace failure is inferred from this lemma.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A deliberately generous cofinal H³-energy request, calibrated to the
exact Sobolev-weight radial low-mass ceiling and a fixed kinetic anchor. -/
noncomputable def h3PathHighEnergyRadialRequest244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b ρ : ℝ) : ℝ :=
  (48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
    ((ρ + 2) *
        (h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b + 2) + 1)

/-- The high-energy-corridor inequality, with a sufficiently high requested
threshold, pays for the low-frequency ceiling in the TOTAL physical H³
energy. This is algebra and nonnegativity, not PDE compactness. -/
theorem h3Path_highEnergyRequest_forces_spectralThreshold244
    (R C E A : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hE : 0 ≤ E) (hA : 0 < A)
    (hLarge : A * ((R + 2) * (C + 2) + 1) ≤
      A * Real.sqrt E) :
    1 + (R + 1) * (C + 1) < E := by
  let Q : ℝ := (R + 2) * (C + 2)
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg (by linarith) (by linarith)
  have hGap : (R + 1) * (C + 1) < Q := by
    dsimp only [Q]
    nlinarith only [hR, hC]
  have hCancel : Q + 1 ≤ Real.sqrt E := by
    by_contra hNot
    have hReverse : Real.sqrt E < Q + 1 := lt_of_not_ge hNot
    have hStrict : A * Real.sqrt E < A * (Q + 1) :=
      mul_lt_mul_of_pos_left hReverse hA
    have hL : A * (Q + 1) ≤ A * Real.sqrt E := by
      simpa only [Q] using hLarge
    exact (not_lt_of_ge hL) hStrict
  have hSquare : (Q + 1) ^ 2 ≤ E := by
    have hNonneg : 0 ≤ Q + 1 := by linarith
    have hSq := (sq_le_sq₀ hNonneg (Real.sqrt_nonneg E)).mpr hCancel
    rwa [Real.sq_sqrt hE] at hSq
  have hBelow : Q + 1 ≤ (Q + 1) ^ 2 := by
    have hProd : 0 ≤ Q * (Q + 1) :=
      mul_nonneg hQ (by linarith)
    nlinarith only [hProd]
  linarith only [hGap, hBelow, hSquare]

/-- At ONE actual Navier–Stokes time, sufficiently large physical H³ energy
synchronizes (i) dominance of high-radial weighted spectral mass and
(ii) the normalized full physical H³ dissipation clock. -/
theorem h3Path_highEnergyRequest_forces_jointRadialClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (n : ℕ)
    (hLarge :
      h3PathHighEnergyRadialRequest244 u b ((n : ℝ) + 1) ≤
        (48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t)) :
    ((n : ℝ) + 2) *
        h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) >
      ((n : ℝ) + 1) *
        h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
    ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u t <
      ((n : ℝ) + 3) * velocityH3DissipationAt u t := by
  let R : ℝ := (n : ℝ) + 1
  let C : ℝ := h3TerminalRadialSobolevWeightSquareCeiling R *
    velocityH3Energy0At u b
  let A : ℝ := 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let H : ℝ := h3PathActualSpectralHighRadialRemainder244 R G
  let E : ℝ := velocityH3EnergyAt u t
  let D : ℝ := velocityH3DissipationAt u t
  have hR : 0 < R := by dsimp only [R]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (h3TerminalRadialSobolevWeightSquareCeiling_pos R).le
      (velocityH3Energy0At_nonneg u b)
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (by norm_num)
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
  have hE : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u t)
  have hRequest : A * ((R + 2) * (C + 2) + 1) ≤
      A * Real.sqrt E := by
    change A * ((R + 2) * (C + 2) + 1) ≤ A * Real.sqrt E at hLarge
    exact hLarge
  have hThreshold : 1 + (R + 1) * (C + 1) < E :=
    h3Path_highEnergyRequest_forces_spectralThreshold244
      R C E A hR.le hC hE.le hA hRequest
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 htClass.1, htClass.2⟩
  have hEnergy : 1 + h3SpectralVelocitySquareEnergy G = E := by
    dsimp only [G, E]
    exact h3AuditActualSpectralVelocityTotal_energy_exact hH3 t htAbs
  have hLow : h3PathActualSpectralLowRadialSquareMass244 R G ≤ C := by
    dsimp only [G, C]
    exact h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
      hH3 hClass b hb R hR.le t ht
  have hHigh : R * (C + 1) < H := by
    dsimp only [H, h3PathActualSpectralHighRadialRemainder244]
    nlinarith only [hThreshold, hEnergy, hLow]
  have hDom : (R + 1) * H > R * h3SpectralVelocitySquareEnergy G := by
    have h := h3Path_highRadialDominates_total_of_lowCeiling244
      G R C (n : ℝ) (Nat.cast_nonneg n) hLow (by
        simpa only [R, H] using hHigh)
    dsimp only [R, H] at h ⊢
    nlinarith only [h]
  have hRadial : R ^ 2 * H ≤ D := by
    dsimp only [H, G, D]
    rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
    exact h3Path_physicalDissipation_ge_highRadialSpectralMass244
      hH3 hClass t htClass R hR.le
  have hHlower : R < H := by
    have hProduct : 0 ≤ R * C := mul_nonneg hR.le hC
    have hRlower : R ≤ R * (C + 1) := by
      nlinarith only [hProduct]
    exact lt_of_le_of_lt hRlower hHigh
  have hCube : R ^ 3 < D := by
    calc
      R ^ 3 = R ^ 2 * R := by ring
      _ < R ^ 2 * H := mul_lt_mul_of_pos_left hHlower (pow_pos hR 2)
      _ ≤ D := hRadial
  have hSpectralClock :
      R ^ 3 * h3SpectralVelocitySquareEnergy G < (R + 1) * D :=
    h3Path_dominantRadialMass_forces_cubicDissipationEnergyClock244
      (h3SpectralVelocitySquareEnergy G) H D R hR hDom hRadial
  have hFullClock : R ^ 3 * E < (R + 2) * D := by
    calc
      R ^ 3 * E = R ^ 3 * (h3SpectralVelocitySquareEnergy G + 1) := by
        rw [← hEnergy]
        ring
      _ = R ^ 3 * h3SpectralVelocitySquareEnergy G + R ^ 3 := by ring
      _ < (R + 1) * D + D := add_lt_add hSpectralClock hCube
      _ = (R + 2) * D := by ring
  constructor
  · simpa only [R, H, G, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using hDom
  · simpa only [R, E, D, show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
      using hFullClock

/-- If the HIGH-ENERGY member of the fixed four-channel corridor is
cofinal, then the same selected times witness high radial H³ spectral
concentration and the cubic physical dissipation clock. Both estimates
are synchronized; no intersection of two cofinal sets is assumed. -/
theorem h3Path_cofinalHighEnergy_forces_jointRadialSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hHigh : ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        B ≤ 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 2) *
          h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
        ((n : ℝ) + 1) *
          h3SpectralVelocitySquareEnergy
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u (τ n) <
          ((n : ℝ) + 3) * velocityH3DissipationAt u (τ n)) ∧
      Tendsto (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          velocityH3EnergyAt u (τ n)) atTop atTop := by
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [hClass.terminal_start.2]
  have hCofinal : ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        h3PathHighEnergyRadialRequest244 u b B ≤
          48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t) := by
    intro c hc B hB
    have hC : 0 ≤ h3TerminalRadialSobolevWeightSquareCeiling B *
        velocityH3Energy0At u b :=
      mul_nonneg (h3TerminalRadialSobolevWeightSquareCeiling_pos B).le
        (velocityH3Energy0At_nonneg u b)
    have hA : 0 ≤ 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
      mul_nonneg (by norm_num)
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
    have hM : 0 ≤ (B + 2) *
        (h3TerminalRadialSobolevWeightSquareCeiling B *
          velocityH3Energy0At u b + 2) :=
      mul_nonneg (by linarith) (by linarith)
    have hRequestNonneg : 0 ≤ h3PathHighEnergyRadialRequest244 u b B := by
      unfold h3PathHighEnergyRadialRequest244
      exact mul_nonneg hA (by linarith only [hM])
    have hcClass : c ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hc.1, hc.2⟩
    exact hHigh c hcClass _ hRequestNonneg
  obtain ⟨τ, hτ, hNear, hLimit, hLarge⟩ :=
    h3Path_cofinalThreshold_diagonalPredicate244
      hb.2
      (fun t B =>
        h3PathHighEnergyRadialRequest244 u b B ≤
          48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) hCofinal
  have hJoint (n : ℕ) :
      ((n : ℝ) + 2) *
          h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
        ((n : ℝ) + 1) *
          h3SpectralVelocitySquareEnergy
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ∧
      ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u (τ n) <
          ((n : ℝ) + 3) * velocityH3DissipationAt u (τ n) :=
    h3Path_highEnergyRequest_forces_jointRadialClock244
      hH3 hClass b hb (τ n) (hτ n) n (hLarge n)
  have hRatio : Tendsto (fun n : ℕ =>
      velocityH3DissipationAt u (τ n) /
        velocityH3EnergyAt u (τ n)) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    obtain ⟨N, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hnOne : 1 ≤ n := (le_max_right N 1).trans hn
    let R : ℝ := (n : ℝ) + 1
    have hR : 2 ≤ R := by
      have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnOne
      dsimp only [R]
      linarith
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (one_le_velocityH3EnergyAt u (τ n))
    have hClock : R ^ 3 * velocityH3EnergyAt u (τ n) <
        (R + 2) * velocityH3DissipationAt u (τ n) := by
      simpa only [R, show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
        using (hJoint n).2
    have hNorm : R < velocityH3DissipationAt u (τ n) /
        velocityH3EnergyAt u (τ n) :=
      h3Path_cubicDissipationEnergyClock_forces_ratio_gt_radius244
        (velocityH3EnergyAt u (τ n))
        (velocityH3DissipationAt u (τ n)) R hR hE hClock
    have hMn : M < (n : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hnN)
    have hnR : (n : ℝ) < R := by dsimp only [R]; linarith
    exact le_of_lt (lt_trans (lt_trans hMn hnR) hNorm)
  exact ⟨τ, (fun n => ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩),
    hNear, hLimit, (fun n => (hJoint n).1), (fun n => (hJoint n).2), hRatio⟩

end
end PrimeTensor.FirstMonomialTriad
