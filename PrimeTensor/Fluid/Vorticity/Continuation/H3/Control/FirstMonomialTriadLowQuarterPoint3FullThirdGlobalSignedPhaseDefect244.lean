import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAdjustableFifthCubicAbsorption244
import Mathlib.Tactic

/-!
# Exact global fifth/cubic signed phase defect

The adjustable fifth/cubic Young inequality conceals a positive remainder.
Retain the signed Fourier pairing rather than taking its absolute value.
For q >= 0 and complex velocity/forcing coordinates z, f, define

  Q(q,z,f) = q^5 |z|^2 + q^3 |f|^2 + 2 q^4 Re<z,f>.

Its exact real decomposition is

  Q = q^3 (q |z| - |f|)^2 + 2 q^4 (|z| |f| + Re<z,f>) >= 0.

This displays BOTH the amplitude mismatch and the phase/cancellation
orientation required for saturation. The genuine strict-time Fourier integrals
are finite, so their sum supplies an exact, nonnegative phase defect P(t).
Unlike Young's inequality, no information is discarded:

  D3'(t) + M5(t) + P(t) = M3(t).

This does not bound normalized Fourier concentration or prove continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeGlobalSignedPhaseDefect244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Signed PDE square-completion density with genuine radial powers. -/
noncomputable def h3GlobalSignedPhaseDensity244
    (q : ℝ) (z f : ℂ) : ℝ :=
  q ^ 5 * ‖z‖ ^ 2 + q ^ 3 * ‖f‖ ^ 2 +
    2 * (q ^ 4 * (inner ℂ z f).re)

/-- Exact decomposition into amplitude mismatch and phase-alignment defect. -/
theorem h3_globalSignedPhaseDensity_eq_twoDefects244
    (q : ℝ) (z f : ℂ) :
    h3GlobalSignedPhaseDensity244 q z f =
      q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2 +
        2 * q ^ 4 * (‖z‖ * ‖f‖ + (inner ℂ z f).re) := by
  unfold h3GlobalSignedPhaseDensity244
  ring

/-- The true signed density bounds the squared Fourier amplitude mismatch. -/
theorem h3_globalSignedPhaseDensity_ge_amplitudeMismatch244
    (q : ℝ) (_hq : 0 ≤ q) (z f : ℂ) :
    q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2 ≤
      h3GlobalSignedPhaseDensity244 q z f := by
  have hRe : -(inner ℂ z f).re ≤ ‖z‖ * ‖f‖ := by
    calc
      -(inner ℂ z f).re ≤ |(inner ℂ z f).re| := neg_le_abs _
      _ ≤ ‖inner ℂ z f‖ := Complex.abs_re_le_norm _
      _ ≤ ‖z‖ * ‖f‖ := norm_inner_le_norm z f
  have hPhase : 0 ≤ ‖z‖ * ‖f‖ + (inner ℂ z f).re := by
    linarith only [hRe]
  have hRest :
      0 ≤ 2 * q ^ 4 * (‖z‖ * ‖f‖ + (inner ℂ z f).re) :=
    mul_nonneg (by positivity) hPhase
  rw [h3_globalSignedPhaseDensity_eq_twoDefects244]
  exact le_add_of_nonneg_right hRest

/-- Nonnegative pointwise, without a modulus on the signed Fourier pairing. -/
theorem h3_globalSignedPhaseDensity_nonneg244
    (q : ℝ) (hq : 0 ≤ q) (z f : ℂ) :
    0 ≤ h3GlobalSignedPhaseDensity244 q z f := by
  exact le_trans
    (mul_nonneg (pow_nonneg hq 3) (sq_nonneg _))
    (h3_globalSignedPhaseDensity_ge_amplitudeMismatch244 q hq z f)

/-- The integrated signed phase defect of actual physical velocity and
Leray forcing, retaining rather than discarding the Young remainder. -/
noncomputable def h3PathTopFourierGlobalSignedPhaseDefect244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ)
        (h3SpectralScalarRawFourierL2 (U j) ξ)
        (h3RawFinLerayOuterProductDivergence U U j ξ)

/-- The full phase defect is nonnegative at every strict physical time. -/
theorem h3Path_globalSignedPhaseDefect_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0 ≤ h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass t ht := by
  unfold h3PathTopFourierGlobalSignedPhaseDefect244
  dsimp only
  apply Finset.sum_nonneg
  intro j hj
  apply integral_nonneg
  intro ξ
  exact h3_globalSignedPhaseDensity_nonneg244
    (h3FourierGradientSquare ξ)
    (h3FourierGradientSquare_nonneg ξ) _ _

/-- Exact (not merely bounded) phase remainder from the strict-time
weighted Fourier integrals. The individual integrability obligations use
previously closed Hilbert PDE factorization and cubic forcing moments. -/
theorem h3Path_globalSignedPhaseDefect_eq_fifth_add_cubic_sub_Leray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass t ht =
      h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt hH3 hClass ht -
        h3PathTopFourierGlobalLerayRate244 hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let z : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ => h3SpectralScalarRawFourierL2 (U j) ξ
  let f : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ => h3RawFinLerayOuterProductDivergence U U j ξ
  let m5 : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 5 * ‖z j ξ‖ ^ 2
  let m3 : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 3 * ‖f j ξ‖ ^ 2
  let g : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 4 *
      (inner ℂ (z j ξ) (f j ξ)).re
  have hEach (j : Fin 3) :
      (∫ ξ : H3FourierPoint3,
          h3GlobalSignedPhaseDensity244 (h3FourierGradientSquare ξ)
            (z j ξ) (f j ξ)) =
        (∫ ξ : H3FourierPoint3, m5 j ξ) +
          (∫ ξ : H3FourierPoint3, m3 j ξ) +
          2 * (∫ ξ : H3FourierPoint3, g j ξ) := by
    have hInt5 : Integrable (m5 j) (volume : Measure H3FourierPoint3) := by
      change Integrable (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 5 *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3)
      simpa only [U, htAbs] using
        (integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
          hH3 hClass ht j)
    have hInt3 : Integrable (m3 j) (volume : Measure H3FourierPoint3) := by
      change Integrable
        (h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j) (volume : Measure H3FourierPoint3)
      exact integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j
    have hIntG : Integrable (g j) (volume : Measure H3FourierPoint3) := by
      change Integrable
        (h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
          hH3 hClass ht j) (volume : Measure H3FourierPoint3)
      exact integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
        hH3 hClass ht j
    change (∫ ξ : H3FourierPoint3,
        m5 j ξ + m3 j ξ + 2 * g j ξ) =
      (∫ ξ : H3FourierPoint3, m5 j ξ) +
        (∫ ξ : H3FourierPoint3, m3 j ξ) +
        2 * (∫ ξ : H3FourierPoint3, g j ξ)
    have hSum :
        (∫ ξ : H3FourierPoint3,
            m5 j ξ + m3 j ξ + 2 * g j ξ) =
          (∫ ξ : H3FourierPoint3, m5 j ξ + m3 j ξ) +
            (∫ ξ : H3FourierPoint3, 2 * g j ξ) := by
      exact integral_add (hInt5.add hInt3) (hIntG.const_mul 2)
    have hAB :
        (∫ ξ : H3FourierPoint3, m5 j ξ + m3 j ξ) =
          (∫ ξ : H3FourierPoint3, m5 j ξ) +
            (∫ ξ : H3FourierPoint3, m3 j ξ) := by
      exact integral_add hInt5 hInt3
    have hG :
        (∫ ξ : H3FourierPoint3, 2 * g j ξ) =
          2 * (∫ ξ : H3FourierPoint3, g j ξ) := by
      rw [integral_const_mul]
    exact hSum.trans (congrArg₂ (fun a b : ℝ => a + b) hAB hG)
  unfold h3PathTopFourierGlobalSignedPhaseDefect244
    h3PathTopFourierGlobalFifthMass244
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
    h3PathTopFourierGlobalLerayRate244
  dsimp only
  change
    (∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        h3GlobalSignedPhaseDensity244 (h3FourierGradientSquare ξ)
          (z j ξ) (f j ξ)) =
    (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m5 j ξ) +
      (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m3 j ξ) -
      (∑ j : Fin 3, (-2 : ℝ) * ∫ ξ : H3FourierPoint3, g j ξ)
  calc
    (∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        h3GlobalSignedPhaseDensity244 (h3FourierGradientSquare ξ)
          (z j ξ) (f j ξ)) =
      ∑ j : Fin 3,
        ((∫ ξ : H3FourierPoint3, m5 j ξ) +
          (∫ ξ : H3FourierPoint3, m3 j ξ) +
          2 * (∫ ξ : H3FourierPoint3, g j ξ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hEach j
    _ = (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m5 j ξ) +
        (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m3 j ξ) -
        (∑ j : Fin 3, (-2 : ℝ) * ∫ ξ : H3FourierPoint3, g j ξ) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          ring

/-- Exact signed PDE balance with its *retained*, nonnegative Fourier phase
defect, sharpening all the earlier Young absorption inequalities. -/
theorem h3Path_globalFourthRadialPairing_add_fifth_add_phase_eq_cubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t +
      h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
      h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass t ht =
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass ht := by
  have hTop := h3Path_fourthRadialPairing_eq_globalHeat_add_Leray244
    hH3 hClass ht
  have hHeat := h3Path_globalHeatRate_eq_negTwoFifthMass244
    hH3 hClass ht
  have hPhase := h3Path_globalSignedPhaseDefect_eq_fifth_add_cubic_sub_Leray244
    hH3 hClass ht
  rw [hTop, hHeat, hPhase]
  ring

/-- Nonnegative top-dissipation growth requires cubic forcing to pay for
both fifth moment dissipation and the signed phase mismatch. -/
theorem h3Path_globalFourthRadialPairing_nonneg_forces_cubic_ge_fifth_add_phase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hGrowth : 0 ≤ h3PathTopFourierFourthRadialPairingRate244
      hH3 hClass t) :
    h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
      h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass t ht ≤
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass ht := by
  have hExact := h3Path_globalFourthRadialPairing_add_fifth_add_phase_eq_cubic244
    hH3 hClass ht
  linarith only [hExact, hGrowth]

end
end PrimeTensor.FirstMonomialTriad
