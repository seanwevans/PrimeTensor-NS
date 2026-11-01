import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDropHighRadialTemporalTransfer
import Mathlib.Tactic

/-!
# Replace the remaining Fourier temporal displacement by actual endpoint H³ dissipation

The source-drop spectral transport theorem forces a complementary-band
weighted H³ temporal square displacement. The genuine three-coordinate
Fourier integrals obey a sharp elementary endpoint inequality:

  H_R(G-H) ≤ 2 (HighMass_R(G) + HighMass_R(H)).

The existing physical high-radial dissipation coercivity supplies
  R² HighMass_R(U(t)) ≤ D_{>R}(t)
pointwise at each strict energy-class time. Combining them closes an exact
endpoint dissipation budget for the source-drop obstruction without assuming
that the *full* H³ spectral state is time-Lipschitz, or that endpoint
high-radial dissipation is bounded uniformly near the terminal time.

The endpoint bound does not establish global regularity: its right side
contains the genuine, potentially divergent physical endpoint dissipation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeSourceDropEndpoint
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSourceDropEndpoint :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Pointwise quadratic difference inequality in a complex Fourier L²
representative. It is only used under integrals and hence does not select
canonical representatives at individual Fourier frequencies. -/
theorem h3Critical_fourierDifference_normSq_le_twoEndpointSquares
    (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hTri : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hTri 2
  nlinarith only [hSq, sq_nonneg (‖x‖ - ‖y‖)]

/-- The ACTUAL integrated Fourier high-band square of a difference is at
most twice the sum of the two actual endpoint high-band square masses.
No temporal differentiability or physical PDE hypothesis is required. -/
theorem h3Critical_highTemporalMass_le_twoEndpointHighMass
    (R : ℝ) (G H : H3SpectralVelocityState) :
    h3Path_spectralTemporalHighRadialIntegral244 R G H ≤
      2 * (h3PathActualSpectralHighRadialRemainder244 R G +
        h3PathActualSpectralHighRadialRemainder244 R H) := by
  let S : Set H3FourierPoint3 := (h3TerminalRadialFrequencyBelow R)ᶜ
  let F : H3FourierPoint3 → ℝ :=
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity G H
  let A : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralStateSquareAmplitude G
  let B : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralStateSquareAmplitude H
  let K : H3FourierPoint3 → ℝ := fun ξ => 2 * (A ξ + B ξ)
  have hFInt : Integrable F volume :=
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_integrable G H
  have hAInt : Integrable A volume :=
    h3TerminalSpectralStateSquareAmplitude_integrable G
  have hBInt : Integrable B volume :=
    h3TerminalSpectralStateSquareAmplitude_integrable H
  have hKInt : Integrable K volume := (hAInt.add hBInt).const_mul 2
  have hPoint (ξ : H3FourierPoint3) : F ξ ≤ K ξ := by
    have h0 := h3Critical_fourierDifference_normSq_le_twoEndpointSquares
      ((G 0) ξ) ((H 0) ξ)
    have h1 := h3Critical_fourierDifference_normSq_le_twoEndpointSquares
      ((G 1) ξ) ((H 1) ξ)
    have h2 := h3Critical_fourierDifference_normSq_le_twoEndpointSquares
      ((G 2) ξ) ((H 2) ξ)
    dsimp only [F, K, A, B,
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity,
      h3TerminalSpectralStateSquareAmplitude,
      h3TerminalSpectralDifferenceAt]
    linarith only [h0, h1, h2]
  have hIntegral :
      (∫ ξ in S, F ξ ∂volume) ≤ ∫ ξ in S, K ξ ∂volume :=
    integral_mono_ae
      (hFInt.mono_measure Measure.restrict_le_self)
      (hKInt.mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall hPoint)
  rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244,
    h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
  change (∫ ξ in S, F ξ ∂volume) ≤
    2 * ((∫ ξ in S, A ξ ∂volume) + (∫ ξ in S, B ξ ∂volume))
  calc
    (∫ ξ in S, F ξ ∂volume) ≤ ∫ ξ in S, K ξ ∂volume := hIntegral
    _ = 2 * ((∫ ξ in S, A ξ ∂volume) +
        (∫ ξ in S, B ξ ∂volume)) := by
      dsimp only [K]
      rw [integral_const_mul,
        integral_add
          (hAInt.mono_measure Measure.restrict_le_self)
          (hBInt.mono_measure Measure.restrict_le_self)]

/-- The spectral temporal cost outside R can be paid by the *actual* high-H³
physical viscous dissipation at its two endpoints. This is an unconditional
strict-time PDE estimate: the only temporal input is two admissible snapshots. -/
theorem h3Critical_highTemporalMass_radiusSq_le_endpointDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s : ℝ) (ht : t ∈ Set.Ioo a T) (hs : s ∈ Set.Ioo a T)
    (R : ℝ) (hR : 0 ≤ R) :
    R ^ 2 * h3Path_spectralTemporalHighRadialIntegral244 R
      (h3AuditActualSpectralVelocityTotal hH3 t)
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤
    2 * (h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 t) +
      h3PathActualHighRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let G : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  let H : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 s
  have hTemporal := h3Critical_highTemporalMass_le_twoEndpointHighMass R G H
  have htCoercive := h3Path_actualHighRadialDissipation_ge_squareHighMass244
    hH3 hClass t ht R hR
  have hsCoercive := h3Path_actualHighRadialDissipation_ge_squareHighMass244
    hH3 hClass s hs R hR
  have hTemporalScaled := mul_le_mul_of_nonneg_left hTemporal (sq_nonneg R)
  change R ^ 2 * h3Path_spectralTemporalHighRadialIntegral244 R G H ≤
    2 * (h3PathActualHighRadialDissipation244 R G +
      h3PathActualHighRadialDissipation244 R H)
  calc
    R ^ 2 * h3Path_spectralTemporalHighRadialIntegral244 R G H ≤
        R ^ 2 * (2 * (h3PathActualSpectralHighRadialRemainder244 R G +
          h3PathActualSpectralHighRadialRemainder244 R H)) := hTemporalScaled
    _ = 2 * (R ^ 2 * h3PathActualSpectralHighRadialRemainder244 R G +
        R ^ 2 * h3PathActualSpectralHighRadialRemainder244 R H) := by ring
    _ ≤ 2 * (h3PathActualHighRadialDissipation244 R G +
        h3PathActualHighRadialDissipation244 R H) := by
          have hSum := add_le_add htCoercive hsCoercive
          exact mul_le_mul_of_nonneg_left hSum (by norm_num)

/-- Closed endpoint dissipation alternative for a physical projected-source
collapse. The finite-frequency temporal motion is controlled by the ACTUAL
physical momentum source; the complementary Fourier motion is controlled by
actual H³ viscous dissipation at the two physical endpoints. In particular,
there is no uncharged high-frequency temporal motion term remaining. -/
theorem h3Critical_sourceDrop_forces_endpointPhysicalDissipationBudget
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
    R ^ 2 *
      (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) σ M) ^ 2 ≤
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) +
          2 * (h3PathActualHighRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 t) +
            h3PathActualHighRadialDissipation244 R
              (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  let G : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  let H : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 s
  let A : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient * (‖G‖ + ‖H‖)
  let P : ℝ :=
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
      h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M
  let L : ℝ := (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
    (C * (s - t)) ^ 2
  let D : ℝ := h3PathActualHighRadialDissipation244 R G +
    h3PathActualHighRadialDissipation244 R H
  let X : ℝ := h3Path_spectralTemporalHighRadialIntegral244 R G H
  have hOriginal : P ^ 2 ≤ A ^ 2 * (L + X) := by
    dsimp only [P, A, L, X, G, H]
    exact h3Critical_sourceDrop_forces_highRadialSpectralMotion_or_PDEClock
      hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C hCeil
      hPeak hDrop
  have hRadial : R ^ 2 * X ≤ 2 * D := by
    dsimp only [X, D, G, H]
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 ht.1, ht.2⟩
    have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hs.1, hs.2⟩
    exact h3Critical_highTemporalMass_radiusSq_le_endpointDissipation
      hH3 hClass t s htClass hsClass R hR
  have hCombined : R ^ 2 * (L + X) ≤ R ^ 2 * L + 2 * D := by
    calc
      R ^ 2 * (L + X) = R ^ 2 * L + R ^ 2 * X := by ring
      _ ≤ R ^ 2 * L + 2 * D := add_le_add_right hRadial _
  change R ^ 2 * P ^ 2 ≤ A ^ 2 * ((R ^ 2) * L + 2 * D)
  calc
    R ^ 2 * P ^ 2 ≤ R ^ 2 * (A ^ 2 * (L + X)) :=
      mul_le_mul_of_nonneg_left hOriginal (sq_nonneg R)
    _ = A ^ 2 * (R ^ 2 * (L + X)) := by ring
    _ ≤ A ^ 2 * (R ^ 2 * L + 2 * D) :=
      mul_le_mul_of_nonneg_left hCombined (sq_nonneg A)


/-- A physical two-endpoint dissipation ceiling that is too small to pay the
source excess and the explicitly priced low-frequency momentum clock
precludes a high-radial dissipation drop. No independent high-frequency
temporal-displacement premise is needed: its budget has been discharged by
the genuine endpoint fourth-order dissipation. -/
theorem h3Critical_sourceDrop_endpointDissipationCeilings_preclude_drop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ R : ℝ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (i : Fin 3)
    (t s : ℝ) (ht : t ∈ Set.Ioo b T) (hs : s ∈ Set.Ioo b T)
    (hts : t ≤ s) (M C Dt Ds : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc t s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : h3CriticalSourceDrivenHighDissipationBarrier
        (velocityH3Energy0At u b) σ M ≤
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖)
    (hDt : h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤ Dt)
    (hDs : h3PathActualHighRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ Ds)
    (hGap :
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) ^ 2 *
        (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (s - t)) ^ 2) + 2 * (Dt + Ds)) <
      R ^ 2 *
        (‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ -
          h3CriticalSourceDrivenHighDissipationBarrier
            (velocityH3Energy0At u b) σ M) ^ 2) :
    M < h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) := by
  by_contra hNot
  have hDrop : h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤ M :=
    le_of_not_gt hNot
  have hBound := h3Critical_sourceDrop_forces_endpointPhysicalDissipationBudget
    hH3 hClass b hb ρ σ R hσ hR i t s ht hs hts M C hCeil
      hPeak hDrop
  have hSum := add_le_add hDt hDs
  have hHigh := mul_le_mul_of_nonneg_left hSum (by norm_num : 0 ≤ (2 : ℝ))
  have hUpper := mul_le_mul_of_nonneg_left
    (add_le_add_right hHigh
      (R ^ 2 * ((3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
        (C * (s - t)) ^ 2)))
    (sq_nonneg
      (3 + h3AuditInitialLerayEnergyCoefficient *
        (‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖)))
  exact (not_lt_of_ge (hBound.trans hUpper)) hGap

end
end PrimeTensor.Bridge.Euclidean
