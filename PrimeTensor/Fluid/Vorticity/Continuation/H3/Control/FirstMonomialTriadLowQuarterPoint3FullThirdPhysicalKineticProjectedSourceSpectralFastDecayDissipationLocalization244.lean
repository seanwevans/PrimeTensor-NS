import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFastDecayRadialSynchronization244
import Mathlib.Tactic

/-!
# Moving-frequency localization of the physical H³ dissipation

The fast-negative-energy-slope branch had an exact physical dissipation
clock, but its direct viscous arm did not yet locate that dissipation in
frequency. This module distinguishes high-radial *dissipation* from the
stronger requirement of high-radial weighted H³ *energy mass*.

At radius R, the true Fourier dissipation splits into its integrals inside
and outside the ball |D(ξ)| < R. The lower-frequency dissipation is bounded
by R² times the weighted spectral energy inside the ball. The existing
high-frequency estimate bounds high dissipation below by R² times high
weighted mass. Consequently either (i) D/E is sufficiently large or (ii)
high-radial H³ energy dominates at factor R; in BOTH cases the dissipation
beyond the radius is more than R times the low-frequency dissipation.

The fast-decay cofinal selection chooses an enlarged derivative threshold
BEFORE selecting its time. It therefore yields a single sequence t_n -> T
with high/low dissipation ratio > n+1, without intersecting two unrelated
cofinal sets. This is NOT high-radial H³ energy domination in the direct arm.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3FastDecayDissipationLocalization244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3FastDecayDissipationLocalization244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Dissipation densities are those of the actual weighted spectral state,
not a separate artificially constructed Fourier family. -/
noncomputable def h3PathActualLowRadialDissipation244
    (ρ : ℝ) (G : H3SpectralVelocityState) : ℝ :=
  ∫ ξ in h3TerminalRadialFrequencyBelow ρ,
    h3TerminalSpectralDissipationSingleDensity G ξ ∂volume

noncomputable def h3PathActualHighRadialDissipation244
    (ρ : ℝ) (G : H3SpectralVelocityState) : ℝ :=
  ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
    h3TerminalSpectralDissipationSingleDensity G ξ ∂volume

/-- On the radial ball, the actual spectral dissipation density is bounded
by the square radius times the weighted H³ energy density. -/
theorem h3Path_lowRadialDissipationDensity_le_squareEnergy244
    (G : H3SpectralVelocityState) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {ξ : H3FourierPoint3}
    (hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ) :
    h3TerminalSpectralDissipationSingleDensity G ξ ≤
      ρ ^ 2 * h3TerminalSpectralStateSquareAmplitude G ξ := by
  have hInside : h3FourierGradientMagnitude ξ < ρ := by
    simpa only [h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq] using hξ
  have hSquare : (h3FourierGradientMagnitude ξ) ^ 2 ≤ ρ ^ 2 :=
    pow_le_pow_left₀ (h3FourierGradientMagnitude_nonneg ξ) hInside.le 2
  rw [h3TerminalSpectralDissipationSingleDensity_eq_gradientMagnitude_sq_mul_stateSquareAmplitude]
  exact mul_le_mul_of_nonneg_right hSquare
    (h3TerminalSpectralStateSquareAmplitude_nonneg G ξ)

/-- Exact partition of physical H³ viscous dissipation into low and high
radial Fourier regions at a genuine Navier–Stokes time. -/
theorem h3Path_actualRadialDissipation_partition244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (ρ : ℝ) :
    h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) +
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) =
      velocityH3DissipationAt u t := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  let G : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let D : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralDissipationSingleDensity G
  have hInt : Integrable D volume := by
    dsimp only [D, G]
    exact h3TerminalSpectralDissipationSingleDensity_integrable hH3 hClass ht
  have hExact : (∫ ξ : H3FourierPoint3, D ξ ∂volume) =
      velocityH3DissipationAt u t := by
    dsimp only [D, G]
    exact integral_h3TerminalSpectralDissipationSingleDensity_eq_dissipation
      hH3 hClass ht
  have hS : MeasurableSet (h3TerminalRadialFrequencyBelow ρ) :=
    measurableSet_h3TerminalRadialFrequencyBelow ρ
  change (∫ ξ in h3TerminalRadialFrequencyBelow ρ, D ξ ∂volume) +
      (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ, D ξ ∂volume) =
        velocityH3DissipationAt u t
  rw [setIntegral_compl hS hInt]
  rw [hExact]
  ring

/-- Integrated low-radial dissipation is at most radius squared times the
actual integrated low-radial weighted H³ energy. -/
theorem h3Path_actualLowRadialDissipation_le_squareLowMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    h3PathActualLowRadialDissipation244 ρ
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      ρ ^ 2 * h3PathActualSpectralLowRadialSquareMass244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  rw [h3Path_actualSpectralLowRadialSquareMass_eq_integral244]
  let G : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  let A : H3FourierPoint3 → ℝ := h3TerminalSpectralStateSquareAmplitude G
  let D : H3FourierPoint3 → ℝ := h3TerminalSpectralDissipationSingleDensity G
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_h3TerminalRadialFrequencyBelow ρ
  have hAInt : Integrable A volume := by
    dsimp only [A]
    exact h3TerminalSpectralStateSquareAmplitude_integrable G
  have hDInt : Integrable D volume := by
    dsimp only [D, G]
    exact h3TerminalSpectralDissipationSingleDensity_integrable hH3 hClass ht
  have hScaledInt : Integrable (fun ξ => ρ ^ 2 * A ξ) volume :=
    hAInt.const_mul (ρ ^ 2)
  have hPoint : ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
      D ξ ≤ ρ ^ 2 * A ξ := by
    rw [ae_restrict_iff' hS]
    filter_upwards with ξ
    intro hξ
    dsimp only [D, A, S]
    exact h3Path_lowRadialDissipationDensity_le_squareEnergy244 G hρ hξ
  have hIntBound : (∫ ξ in S, D ξ ∂volume) ≤
      ∫ ξ in S, ρ ^ 2 * A ξ ∂volume :=
    integral_mono_ae
      (hDInt.mono_measure Measure.restrict_le_self)
      (hScaledInt.mono_measure Measure.restrict_le_self)
      hPoint
  change (∫ ξ in S, D ξ ∂volume) ≤
    ρ ^ 2 * (∫ ξ in S, A ξ ∂volume)
  calc
    (∫ ξ in S, D ξ ∂volume) ≤
        ∫ ξ in S, ρ ^ 2 * A ξ ∂volume := hIntBound
    _ = ρ ^ 2 * (∫ ξ in S, A ξ ∂volume) := by
      rw [integral_const_mul]

/-- High radial dissipation includes all of the radius-squared weighted
H³ spectral mass outside the radius, without invoking full dissipation. -/
theorem h3Path_actualHighRadialDissipation_ge_squareHighMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ ^ 2 * h3PathActualSpectralHighRadialRemainder244 ρ
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
  let G : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let S : Set H3FourierPoint3 := (h3TerminalRadialFrequencyBelow ρ)ᶜ
  let A : H3FourierPoint3 → ℝ := h3TerminalSpectralStateSquareAmplitude G
  let D : H3FourierPoint3 → ℝ := h3TerminalSpectralDissipationSingleDensity G
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact (measurableSet_h3TerminalRadialFrequencyBelow ρ).compl
  have hAInt : Integrable A volume := by
    dsimp only [A]
    exact h3TerminalSpectralStateSquareAmplitude_integrable G
  have hDInt : Integrable D volume := by
    dsimp only [D, G]
    exact h3TerminalSpectralDissipationSingleDensity_integrable hH3 hClass ht
  have hScaledInt : Integrable (fun ξ => ρ ^ 2 * A ξ) volume :=
    hAInt.const_mul (ρ ^ 2)
  have hPoint : ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
      ρ ^ 2 * A ξ ≤ D ξ := by
    rw [ae_restrict_iff' hS]
    filter_upwards with ξ
    intro hξ
    dsimp only [D, A, S]
    exact h3Path_highRadialSpectralSquare_le_dissipationDensity244 G hρ hξ
  have hIntBound : (∫ ξ in S, ρ ^ 2 * A ξ ∂volume) ≤
      ∫ ξ in S, D ξ ∂volume :=
    integral_mono_ae
      (hScaledInt.mono_measure Measure.restrict_le_self)
      (hDInt.mono_measure Measure.restrict_le_self)
      hPoint
  change ρ ^ 2 * (∫ ξ in S, A ξ ∂volume) ≤
    ∫ ξ in S, D ξ ∂volume
  calc
    ρ ^ 2 * (∫ ξ in S, A ξ ∂volume) =
        ∫ ξ in S, ρ ^ 2 * A ξ ∂volume := by
          rw [integral_const_mul]
    _ ≤ ∫ ξ in S, D ξ ∂volume := hIntBound

/-- A fixed radial dominance inequality in weighted H³ mass, together
with the genuine dissipation density, forces the same radial dominance
in *dissipation*, even though dissipation has one extra Fourier derivative. -/
theorem h3Path_radialMassDominance_forces_dissipationDominance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hDom : (ρ + 1) * h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) >
      ρ * h3SpectralVelocitySquareEnergy
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ρ * h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) <
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let L : ℝ := h3PathActualSpectralLowRadialSquareMass244 ρ G
  let H : ℝ := h3PathActualSpectralHighRadialRemainder244 ρ G
  let DL : ℝ := h3PathActualLowRadialDissipation244 ρ G
  let DH : ℝ := h3PathActualHighRadialDissipation244 ρ G
  have hEq : h3SpectralVelocitySquareEnergy G = L + H := by
    dsimp only [H, h3PathActualSpectralHighRadialRemainder244, L]
    ring
  have hMass : ρ * L < H := by
    change (ρ + 1) * H > ρ * h3SpectralVelocitySquareEnergy G at hDom
    rw [hEq] at hDom
    nlinarith only [hDom]
  have hLo : DL ≤ ρ ^ 2 * L := by
    dsimp only [DL, L]
    exact h3Path_actualLowRadialDissipation_le_squareLowMass244
      hH3 hClass t ht ρ hρ.le
  have hHi : ρ ^ 2 * H ≤ DH := by
    dsimp only [DH, H]
    exact h3Path_actualHighRadialDissipation_ge_squareHighMass244
      hH3 hClass t ht ρ hρ.le
  have hScaledLo : ρ * DL ≤ ρ * (ρ ^ 2 * L) :=
    mul_le_mul_of_nonneg_left hLo hρ.le
  have hScaledMass : ρ ^ 2 * (ρ * L) < ρ ^ 2 * H :=
    mul_lt_mul_of_pos_left hMass (pow_pos hρ 2)
  calc
    ρ * DL ≤ ρ * (ρ ^ 2 * L) := hScaledLo
    _ = ρ ^ 2 * (ρ * L) := by ring
    _ < ρ ^ 2 * H := hScaledMass
    _ ≤ DH := hHi

/-- A sufficiently large *normalized total* physical dissipation ratio
also forces the same high/low radial dissipation domination. This does not
claim high-radial H³ square-mass dominance. -/
theorem h3Path_largePhysicalDissipation_forces_radialDissipationShare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHuge : ((ρ + 1) * ρ ^ 2) * velocityH3EnergyAt u t <
      velocityH3DissipationAt u t) :
    ρ * h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) <
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let DL : ℝ := h3PathActualLowRadialDissipation244 ρ G
  let DH : ℝ := h3PathActualHighRadialDissipation244 ρ G
  let E : ℝ := velocityH3EnergyAt u t
  let D : ℝ := velocityH3DissipationAt u t
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hE : 1 + h3SpectralVelocitySquareEnergy G = E := by
    dsimp only [G, E]
    exact h3AuditActualSpectralVelocityTotal_energy_exact hH3 t htAbs
  have hMassNonneg : 0 ≤ h3SpectralVelocitySquareEnergy G := by
    rw [h3Path_spectralSquareEnergy_eq_totalFourierIntegral244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralStateSquareAmplitude_nonneg G ξ
  have hSpectralLe : h3SpectralVelocitySquareEnergy G ≤ E := by
    linarith only [hE]
  have hLowMassLe : h3PathActualSpectralLowRadialSquareMass244 ρ G ≤
      h3SpectralVelocitySquareEnergy G := by
    have hRem := h3Path_actualSpectralHighRadialRemainder_nonneg244 ρ G
    dsimp only [h3PathActualSpectralHighRadialRemainder244] at hRem
    linarith only [hRem]
  have hLo : DL ≤ ρ ^ 2 * E := by
    have hBound := h3Path_actualLowRadialDissipation_le_squareLowMass244
      hH3 hClass t ht ρ hρ
    change DL ≤ ρ ^ 2 * h3PathActualSpectralLowRadialSquareMass244 ρ G at hBound
    have hScaled := mul_le_mul_of_nonneg_left
      (le_trans hLowMassLe hSpectralLe) (sq_nonneg ρ)
    exact le_trans hBound hScaled
  have hPartition : DL + DH = D := by
    dsimp only [DL, DH, D, G]
    exact h3Path_actualRadialDissipation_partition244 hH3 hClass t ht ρ
  have hScaled : (ρ + 1) * DL ≤ (ρ + 1) * (ρ ^ 2 * E) :=
    mul_le_mul_of_nonneg_left hLo (by linarith)
  have hStrict : (ρ + 1) * DL < D := by
    calc
      (ρ + 1) * DL ≤ (ρ + 1) * (ρ ^ 2 * E) := hScaled
      _ = ((ρ + 1) * ρ ^ 2) * E := by ring
      _ < D := hHuge
  rw [← hPartition] at hStrict
  change ρ * DL < DH
  nlinarith only [hStrict]


/-- Enlarge the fast-decay request so that the direct viscous arm alone
forces high frequency dissipation to overwhelm low frequency dissipation. -/
noncomputable def h3PathFastDecayLocalizedDissipationThreshold244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b ρ : ℝ) : ℝ :=
  2 * ((ρ + 1) * ρ ^ 2) + 4422 * (1 +
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      h3PathFastDecayRadialRootRequest244 u b ρ)

/-- At one fast-decay Navier–Stokes time, the enlarged logarithmic
slope forces dominance of the *actual high radial dissipation integral*.
This does not imply that the high radial H³ energy mass dominates. -/
theorem h3Path_fastDecaySnapshot_forces_highRadialDissipationShare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (n : ℕ)
    (hFast : h3PathFastDecayLocalizedDissipationThreshold244 u b
        ((n : ℝ) + 1) * velocityH3EnergyAt u t <
        -deriv (velocityH3EnergyAt u) t) :
    ((n : ℝ) + 1) * h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let R : ℝ := (n : ℝ) + 1
  let P : ℝ := (R + 1) * R ^ 2
  let E : ℝ := velocityH3EnergyAt u t
  let D : ℝ := velocityH3DissipationAt u t
  let F : ℝ := deriv (velocityH3EnergyAt u) t
  let W : ℝ := velocityH3TransportDerivativeAt u t
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let Q : ℝ := h3PathFastDecayRadialRootRequest244 u b R
  have hR : 0 < R := by dsimp only [R]; positivity
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hE : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le (by norm_num) (one_le_velocityH3EnergyAt u t)
  have hK : 0 ≤ 4422 * C :=
    mul_nonneg (by norm_num)
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hBalance : F + 2 * D = -W := by
    dsimp only [F, D, W]
    exact deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass htClass
  have hAbs := h3Path_physicalFullTransport_abs_le_sqrtEnergy244
    hH3 hClass htClass
  have hTransport : W ≤ (4422 + (4422 * C) * Real.sqrt E) * E := by
    have hW : W ≤ |W| := le_abs_self W
    have hWBound : |W| ≤ (4422 + (4422 * C) * Real.sqrt E) * E := by
      dsimp only [W, C, E] at hAbs ⊢
      convert hAbs using 1 <;> ring
    exact hW.trans hWBound
  have hThreshold : (2 * P + 4422 + (4422 * C) * Q) * E < -F := by
    dsimp only [h3PathFastDecayLocalizedDissipationThreshold244,
      R, P, E, F, C, Q] at hFast ⊢
    convert hFast using 1 <;> ring
  rcases h3Path_fastSlope_largeDissipation_or_largeEnergyRoot244
      E D F W P (4422 * C) Q hE hK hBalance hTransport hThreshold with
    hHuge | hRoot
  · have hScaled : ((R + 1) * R ^ 2) * E < D := by
      simpa only [P] using hHuge
    have hShare :=
      h3Path_largePhysicalDissipation_forces_radialDissipationShare244
        hH3 hClass t htClass R hR.le (by
          dsimp only [E, D] at hScaled
          exact hScaled)
    simpa only [R] using hShare
  · have hA : 0 ≤ 48 * C :=
      mul_nonneg (by norm_num)
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
    have hHigh :
        h3PathHighEnergyRadialRequest244 u b R ≤
          (48 * C) * Real.sqrt E := by
      change (48 * C) * Q ≤ (48 * C) * Real.sqrt E
      exact mul_le_mul_of_nonneg_left hRoot hA
    have hJoint := h3Path_highEnergyRequest_forces_jointRadialClock244
      hH3 hClass b hb t ht n (by
        dsimp only [R, C, E] at hHigh
        convert hHigh using 1 <;> ring)
    have hShare :=
      h3Path_radialMassDominance_forces_dissipationDominance244
        hH3 hClass t htClass R hR (by
          simpa only [R, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
            using hJoint.1)
    simpa only [R] using hShare

/-- An abstract real inequality: when the high-frequency dissipation
exceeds R times its low-frequency counterpart, the low-frequency share
of total dissipation is strictly smaller than 1/(R+1). -/
theorem h3Path_highDissipationDominance_lowShare_bound244
    (R L H : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hHigh : R * L < H) :
    0 < L + H ∧
      0 ≤ L / (L + H) ∧
      L / (L + H) < 1 / (R + 1) := by
  have hHPos : 0 < H :=
    lt_of_le_of_lt (mul_nonneg hR hL) hHigh
  have hTotal : 0 < L + H := add_pos_of_nonneg_of_pos hL hHPos
  have hR1 : 0 < R + 1 := by linarith
  have hBound : (R + 1) * L < L + H := by
    nlinarith only [hHigh]
  refine ⟨hTotal, div_nonneg hL hTotal.le, ?_⟩
  apply (div_lt_div_iff₀ hTotal hR1).2
  nlinarith only [hBound]

/-- A fixed cofinal fast-negative-energy-slope channel has ONE terminal
sequence on which its high-frequency physical H³ dissipation occupies
asymptotically all physical dissipation. High-radial H³ *energy* dominance
is not asserted for the direct-viscous arm. -/
theorem h3Path_cofinalFastDecay_forces_highRadialDissipationLocalization244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hFast : ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        B * velocityH3EnergyAt u t < -deriv (velocityH3EnergyAt u) t) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        h3PathFastDecayLocalizedDissipationThreshold244 u ((a + T) / 2)
          ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
            -deriv (velocityH3EnergyAt u) (τ n)) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) *
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
          h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      Tendsto (fun n : ℕ =>
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) /
            velocityH3DissipationAt u (τ n)) atTop (𝓝 1) := by
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [hClass.terminal_start.2]
  have hChoice : ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        h3PathFastDecayLocalizedDissipationThreshold244 u b B *
          velocityH3EnergyAt u t < -deriv (velocityH3EnergyAt u) t := by
    intro c hc B hB
    have hC : 0 ≤ h3TerminalRadialSobolevWeightSquareCeiling B *
        velocityH3Energy0At u b :=
      mul_nonneg (h3TerminalRadialSobolevWeightSquareCeiling_pos B).le
        (velocityH3Energy0At_nonneg u b)
    have hRoot : 0 ≤ h3PathFastDecayRadialRootRequest244 u b B := by
      unfold h3PathFastDecayRadialRootRequest244
      have hProd : 0 ≤ (B + 2) *
          (h3TerminalRadialSobolevWeightSquareCeiling B *
            velocityH3Energy0At u b + 2) :=
        mul_nonneg (by linarith) (by linarith)
      linarith only [hProd]
    have hThreshold : 0 ≤ h3PathFastDecayLocalizedDissipationThreshold244
        u b B := by
      unfold h3PathFastDecayLocalizedDissipationThreshold244
      have hR : 0 ≤ (B + 1) * B ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg B)
      have hProd : 0 ≤
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            h3PathFastDecayRadialRootRequest244 u b B :=
        mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
          hRoot
      nlinarith only [hR, hProd]
    have hcClass : c ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hc.1, hc.2⟩
    exact hFast c hcClass _ hThreshold
  obtain ⟨τ, hτ, hNear, hLimit, hSlope⟩ :=
    h3Path_cofinalThreshold_diagonalPredicate244 hb.2
      (fun t B => h3PathFastDecayLocalizedDissipationThreshold244 u b B *
        velocityH3EnergyAt u t < -deriv (velocityH3EnergyAt u) t) hChoice
  have hDom (n : ℕ) :
      ((n : ℝ) + 1) *
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) <
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n)) :=
    h3Path_fastDecaySnapshot_forces_highRadialDissipationShare244
      hH3 hClass b hb (τ n) (hτ n) n (hSlope n)
  let L : ℕ → ℝ := fun n =>
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))
  let H : ℕ → ℝ := fun n =>
    h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n))
  let D : ℕ → ℝ := fun n => velocityH3DissipationAt u (τ n)
  have hLNonneg (n : ℕ) : 0 ≤ L n := by
    dsimp only [L, h3PathActualLowRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ξ
  have hPartition (n : ℕ) : L n + H n = D n := by
    dsimp only [L, H, D]
    exact h3Path_actualRadialDissipation_partition244
      hH3 hClass (τ n)
      ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩ ((n : ℝ) + 1)
  have hTotalPositive (n : ℕ) : 0 < D n := by
    have hShare := h3Path_highDissipationDominance_lowShare_bound244
      ((n : ℝ) + 1) (L n) (H n) (by positivity)
      (hLNonneg n) (hDom n)
    rw [← hPartition n]
    exact hShare.1
  have hLowShare (n : ℕ) :
      0 ≤ L n / D n ∧ L n / D n < 1 / ((n : ℝ) + 2) := by
    have hShare := h3Path_highDissipationDominance_lowShare_bound244
      ((n : ℝ) + 1) (L n) (H n) (by positivity)
      (hLNonneg n) (hDom n)
    rw [← hPartition n]
    simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using hShare.2
  have hLowBound (n : ℕ) :
      ‖L n / D n‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hDen : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
    have hInvBound : (1 : ℝ) / ((n : ℝ) + 2) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hR hDen
    rw [Real.norm_eq_abs, abs_of_nonneg (hLowShare n).1]
    exact le_trans (le_of_lt (hLowShare n).2) hInvBound
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hLowTendsto : Tendsto (fun n : ℕ => L n / D n)
      atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (by simpa only [sub_zero] using
        (squeeze_zero'
          (Filter.Eventually.of_forall (fun n => norm_nonneg (L n / D n)))
          (Filter.Eventually.of_forall hLowBound)
          hInv))
  have hHighRatio (n : ℕ) : H n / D n = 1 - L n / D n := by
    have hD : D n ≠ 0 := ne_of_gt (hTotalPositive n)
    have hDH : H n = D n - L n := by
      linarith only [hPartition n]
    rw [hDH]
    field_simp [hD]
    <;> ring
  have hHighTendsto : Tendsto (fun n : ℕ => H n / D n)
      atTop (𝓝 1) := by
    have hSub : Tendsto (fun n : ℕ => 1 - L n / D n)
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hLowTendsto
    simpa only [sub_zero, ← hHighRatio] using hSub
  exact ⟨τ, (fun n => ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩),
    hNear, hLimit, (fun n => hSlope n), hDom, hHighTendsto⟩

end
end PrimeTensor.FirstMonomialTriad
