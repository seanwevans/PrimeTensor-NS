import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalHighpassFifthPhasePhysicalBridge
import Mathlib.Tactic

/-!
# The genuine signed phase is an exact physical fourth-radial temporal square

At an actual strict physical time the fourth-radial Fourier PDE is

    ∂t V4_j(ξ) = -q(ξ)^3 û_j(ξ) - q(ξ)^2 N_j(ξ),

with `q(ξ)=(2π)^2 |ξ|²`. The signed Young phase defect from the exact
third-order H³ energy identity is not a free independent quantity:

    Phase(q,z,f) = q³ |q z + f|².

Consequently the *physical* fourth-radial temporal square density is exactly
`q * Phase`. On the highpass `sqrt(q) ≥ ρ`, this supplies

    ρ² PhaseHigh(ρ,t) ≤ TemporalFourthHigh(ρ,t).

The critical dyadic highpass fifth/phase charge can therefore be transferred
to real fourth-radial temporal expenditure, without a sixth-velocity Fourier
moment. This is a necessary spectral-payment inequality, NOT a terminal-uniform
estimate or a continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeCriticalPhaseTemporal244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalPhaseTemporal244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact square completion of the previously established signed Fourier
phase density. The complex inner product retains the physical phase. -/
theorem thirdFullKinetic_signedPhase_eq_temporalResidualSquare244
    (q : ℝ) (hq : 0 ≤ q) (z f : ℂ) :
    h3GlobalSignedPhaseDensity244 q z f =
      q ^ 3 * ‖(q : ℂ) * z + f‖ ^ 2 := by
  have hInner :
      (inner ℂ ((q : ℂ) * z) f).re =
        q * (inner ℂ z f).re := by
    change (inner ℂ ((q : ℂ) • z) f).re = _
    rw [inner_smul_left]
    simp [Complex.mul_re, Complex.conj_ofReal]
  have hNorm :
      ‖(q : ℂ) * z + f‖ ^ 2 =
        q ^ 2 * ‖z‖ ^ 2 +
          2 * q * (inner ℂ z f).re + ‖f‖ ^ 2 := by
    calc
      ‖(q : ℂ) * z + f‖ ^ 2 =
          ‖(q : ℂ) * z‖ ^ 2 +
            2 * (inner ℂ ((q : ℂ) * z) f).re + ‖f‖ ^ 2 := by
        simpa only [RCLike.re_to_complex] using
          (norm_add_sq (𝕜 := ℂ) ((q : ℂ) * z) f)
      _ = q ^ 2 * ‖z‖ ^ 2 +
            2 * q * (inner ℂ z f).re + ‖f‖ ^ 2 := by
        rw [hInner, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hq]
        ring
  rw [hNorm]
  unfold h3GlobalSignedPhaseDensity244
  ring

/-- The exact time derivative of the fourth-radial Fourier state is one
extra square-gradient factor above the signed phase: `|∂t V4|²=q*Phase`.
This is a pointwise Fourier PDE identity, not a norm comparison. -/
theorem thirdFullKinetic_fourthTemporalSquare_eq_qSignedPhase244
    (q : ℝ) (hq : 0 ≤ q) (z f : ℂ) :
    ‖((-(q ^ 3 : ℝ) : ℂ) * z) -
      (((q ^ 2 : ℝ) : ℂ) * f)‖ ^ 2 =
      q * h3GlobalSignedPhaseDensity244 q z f := by
  have hFactor :
      ((-(q ^ 3 : ℝ) : ℂ) * z) -
          (((q ^ 2 : ℝ) : ℂ) * f) =
        -((q : ℂ) ^ 2 * ((q : ℂ) * z + f)) := by
    push_cast
    ring
  calc
    ‖((-(q ^ 3 : ℝ) : ℂ) * z) -
      (((q ^ 2 : ℝ) : ℂ) * f)‖ ^ 2 =
        ‖(q : ℂ) ^ 2 * ((q : ℂ) * z + f)‖ ^ 2 := by
      rw [hFactor, norm_neg]
    _ = q ^ 4 * ‖(q : ℂ) * z + f‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hq]
      ring
    _ = q * h3GlobalSignedPhaseDensity244 q z f := by
      rw [thirdFullKinetic_signedPhase_eq_temporalResidualSquare244 q hq z f]
      ring

/-- On every strict physical slice, the sharp highpass fourth-radial
*temporal* Hilbert square equals the Fourier integral of `q * Phase`.
The PDE a.e. representative is used before taking the quotient-safe L² norm. -/
theorem thirdFullPhysical_highTemporalSquare_eq_qSignedPhaseBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
      hH3 hClass ρ j t‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        h3FourierGradientSquare ξ *
          h3GlobalSignedPhaseDensity244
            (h3FourierGradientSquare ξ)
            (h3SpectralScalarRawFourierL2 (U j) ξ)
            (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let D : H3FourierComplexL2 :=
    deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j) t
  have hAE :
      (D : H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
            h3SpectralScalarRawFourierL2 (U j) ξ -
          ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergence U U j ξ) := by
    simpa only [D, U, htAbs] using
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_deriv_ae_unitPDE
        hH3 hClass ht j)
  have hHigh :
      ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
        hH3 hClass ρ j t‖ ^ 2 =
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          ‖(D : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume := by
    change ‖D - h3CriticalFourierSharpLowCutoffCLM ρ D‖ ^ 2 = _
    exact h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ D
  rw [hHigh]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (s := (h3TerminalRadialFrequencyBelow ρ)ᶜ) hAE] with ξ hξ
  rw [hξ]
  exact thirdFullKinetic_fourthTemporalSquare_eq_qSignedPhase244
    (h3FourierGradientSquare ξ)
    (h3FourierGradientSquare_nonneg ξ)
    (h3SpectralScalarRawFourierL2 (U j) ξ)
    (h3RawFinLerayOuterProductDivergence U U j ξ)

/-- The sharp highband physical signed phase is controlled by the actual
highpass fourth-radial *temporal* square, with the sharp radius-squared loss.
No sixth-order velocity norm enters and no terminal-uniform bound is assumed. -/
theorem thirdFullPhysical_highSignedPhase_le_highTemporal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ρ ^ 2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ)
        (h3SpectralScalarRawFourierL2 (U j) ξ)
        (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume) ≤
      ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
        hH3 hClass ρ j t‖ ^ 2 := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow ρ)ᶜ
  let z : H3FourierPoint3 → ℂ :=
    fun ξ => h3SpectralScalarRawFourierL2 (U j) ξ
  let f : H3FourierPoint3 → ℂ :=
    fun ξ => h3RawFinLerayOuterProductDivergence U U j ξ
  let p : H3FourierPoint3 → ℝ := fun ξ =>
    h3GlobalSignedPhaseDensity244 (h3FourierGradientSquare ξ) (z ξ) (f ξ)
  let D : H3FourierComplexL2 :=
    deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j) t
  have hPhaseInt : Integrable p (volume : Measure H3FourierPoint3) := by
    let a : H3FourierPoint3 → ℝ := fun ξ =>
      h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2
    let b : H3FourierPoint3 → ℝ := fun ξ =>
      h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2
    let g : H3FourierPoint3 → ℝ := fun ξ =>
      h3FourierGradientSquare ξ ^ 4 * (inner ℂ (z ξ) (f ξ)).re
    have ha : Integrable a volume := by
      change Integrable (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 5 *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2) volume
      simpa only [U, htAbs] using
        (integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
          hH3 hClass ht j)
    have hb : Integrable b volume := by
      change Integrable
        (h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j) volume
      exact integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j
    have hg : Integrable g volume := by
      change Integrable
        (h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
          hH3 hClass ht j) volume
      exact integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
        hH3 hClass ht j
    change Integrable (fun ξ : H3FourierPoint3 =>
      a ξ + b ξ + 2 * g ξ) volume
    exact (ha.add hb).add (hg.const_mul 2)
  have hTemporalInt : Integrable
      (fun ξ : H3FourierPoint3 => h3FourierGradientSquare ξ * p ξ)
      (volume : Measure H3FourierPoint3) := by
    have hL2Int : Integrable
        (fun ξ : H3FourierPoint3 => ‖(D : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
      (MeasureTheory.Lp.memLp D).norm.integrable_sq
    have hDAE :=
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_deriv_ae_unitPDE
        hH3 hClass ht j
    refine hL2Int.congr ?_
    filter_upwards [hDAE] with ξ hξ
    rw [hξ]
    exact thirdFullKinetic_fourthTemporalSquare_eq_qSignedPhase244
      (h3FourierGradientSquare ξ)
      (h3FourierGradientSquare_nonneg ξ)
      (z ξ) (f ξ)
  have hPoint (ξ : H3FourierPoint3) (hξ : ξ ∈ S) :
      ρ ^ 2 * p ξ ≤ h3FourierGradientSquare ξ * p ξ := by
    have hOutside : ξ ∉ h3TerminalRadialFrequencyBelow ρ := hξ
    have hMag : ρ ≤ h3FourierGradientMagnitude ξ := by
      change ¬ h3FourierGradientMagnitude ξ < ρ at hOutside
      exact le_of_not_gt hOutside
    have hQ : ρ ^ 2 ≤ h3FourierGradientSquare ξ := by
      have hSquare : h3FourierGradientSquare ξ =
          h3FourierGradientMagnitude ξ ^ 2 := by
        dsimp only [h3FourierGradientSquare, h3FourierGradientMagnitude]
        ring
      rw [hSquare]
      exact pow_le_pow_left₀ hρ.le hMag 2
    have hP : 0 ≤ p ξ := by
      exact h3_globalSignedPhaseDensity_nonneg244
        (h3FourierGradientSquare ξ)
        (h3FourierGradientSquare_nonneg ξ) _ _
    exact mul_le_mul_of_nonneg_right hQ hP
  have hAE : ∀ᵐ ξ ∂((volume : Measure H3FourierPoint3).restrict S),
      ρ ^ 2 * p ξ ≤ h3FourierGradientSquare ξ * p ξ := by
    filter_upwards [ae_restrict_mem
      (measurableSet_h3TerminalRadialFrequencyBelow ρ).compl] with ξ hξ
    exact hPoint ξ hξ
  have hExact :=
    thirdFullPhysical_highTemporalSquare_eq_qSignedPhaseBand244
      hH3 hClass ht ρ j
  change ρ ^ 2 * (∫ ξ in S, p ξ ∂volume) ≤
      ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
        hH3 hClass ρ j t‖ ^ 2
  calc
    ρ ^ 2 * (∫ ξ in S, p ξ ∂volume) =
        ∫ ξ in S, ρ ^ 2 * p ξ ∂volume := by
      rw [integral_const_mul]
    _ ≤ ∫ ξ in S, h3FourierGradientSquare ξ * p ξ ∂volume :=
      integral_mono_ae
        (hPhaseInt.integrableOn.const_mul _)
        hTemporalInt.integrableOn hAE
    _ = ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
          hH3 hClass ρ j t‖ ^ 2 := by
      simpa only [S, p, z, f, U, htAbs] using hExact.symm

/-- Three genuine physical solenoidal coordinates: the temporal highpass
controls rho² times the *total* high-frequency signed phase expenditure. -/
theorem thirdFullPhysical_highSignedPhaseBand_le_temporalHighMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) (hρ : 0 < ρ) :
    ρ ^ 2 * thirdFullPhysicalCriticalHighSignedPhaseBand244
      hH3 hClass ht ρ ≤
    ∑ j : Fin 3,
      ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
        hH3 hClass ρ j t‖ ^ 2 := by
  let P (j : Fin 3) : ℝ :=
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ)
        (h3SpectralScalarRawFourierL2 (U j) ξ)
        (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume
  have hEach (j : Fin 3) :
      ρ ^ 2 * P j ≤
      ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
        hH3 hClass ρ j t‖ ^ 2 := by
    simpa only [P] using
      (thirdFullPhysical_highSignedPhase_le_highTemporal244
        hH3 hClass ht ρ hρ j)
  change ρ ^ 2 * (∑ j : Fin 3, P j) ≤ _
  calc
    ρ ^ 2 * (∑ j : Fin 3, P j) =
        ∑ j : Fin 3, ρ ^ 2 * P j := by rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin 3,
        ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
          hH3 hClass ρ j t‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact hEach j

/-- The actual dyadic highpass fifth/phase gate may be expressed using the
positive fifth-order highband viscosity and ONLY the highpass fourth-radial
temporal PDE expenditure. The sixth velocity moment is absent. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_highFifthTemporalBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ (r : ℝ) (_hr : r ∈ Set.Ioo s t) (hrClass : r ∈ Set.Ioo a T),
      K < h3PathPhysicalTopSignedLogRate244 hClass r ∧
      ∀ ρ : ℝ, 0 < ρ →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b)) +
          2 * thirdFullPhysicalCriticalHighFifthBand244
            hH3 hClass hrClass ρ +
          2 * (ρ ^ 2)⁻¹ *
            (∑ j : Fin 3,
              ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
                hH3 hClass ρ j r‖ ^ 2) := by
  obtain ⟨r, hr, hrClass, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_highFifthPhaseBand244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hrClass, hNet, ?_⟩
  intro ρ hρ
  have hPhaseTime :=
    thirdFullPhysical_highSignedPhaseBand_le_temporalHighMass244
      hH3 hClass hrClass ρ hρ
  have hPhaseDiv :
      thirdFullPhysicalCriticalHighSignedPhaseBand244
        hH3 hClass hrClass ρ ≤
      (ρ ^ 2)⁻¹ *
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
            hH3 hClass ρ j r‖ ^ 2) := by
    calc
      _ ≤ (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
            hH3 hClass ρ j r‖ ^ 2) / ρ ^ 2 :=
        (le_div_iff₀ (pow_pos hρ 2)).mpr (by
          simpa only [mul_comm] using hPhaseTime)
      _ = _ := by ring
  have hDoublePhase :
      2 * thirdFullPhysicalCriticalHighSignedPhaseBand244
        hH3 hClass hrClass ρ ≤
      2 * (ρ ^ 2)⁻¹ *
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
            hH3 hClass ρ j r‖ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hPhaseDiv (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_assoc] using h
  have hBound := hAll ρ hρ
  exact lt_of_lt_of_le hBound
    (add_le_add_right hDoublePhase
      ((2 * Real.pi) ^ 6 *
        (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
          ρ (velocityH3Energy0At u b)) +
        2 * thirdFullPhysicalCriticalHighFifthBand244
          hH3 hClass hrClass ρ))

end
end PrimeTensor.FirstMonomialTriad
