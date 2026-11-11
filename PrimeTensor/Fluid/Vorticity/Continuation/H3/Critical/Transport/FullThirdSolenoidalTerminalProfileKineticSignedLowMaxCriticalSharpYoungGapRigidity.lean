import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalHighpassPhaseTemporalCoercivity
import Mathlib.Tactic

/-!
# Exact critical H³ highpass Young gap and saturation rigidity

The accepted sharp highpass fifth/phase bound has a factor two. That
coefficient is not an artifact of its proof: it is optimal already for one
complex Fourier coordinate. More precisely, the *entire discarded error*
is an exact nonnegative square:

  2 q⁵ |z|² + 2 Phase(q,z,f) - q³ |f|²
    = q³ |f + 2 q z|².

The scalar equality case f = -2 q z corresponds to a Fourier residual
producing positive H³ growth; this does NOT assert existence of such a
solenoidal Navier--Stokes solution. Any genuine absorption improvement
must exploit PDE or triad structure not present in the scalar identity.

The identity is integrated on arbitrary measurable frequency bands and
specialized to the actual strict-time physical velocity and Leray forcing.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeCriticalSharpGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalSharpGap244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Parallelogram law in precisely the orientation needed for the exact
Young-gap identity; the proof uses the established complex Hilbert norm. -/
theorem thirdFullKinetic_complexParallelogramGap244 (x y : ℂ) :
    2 * ‖x‖ ^ 2 + 2 * ‖x + y‖ ^ 2 =
      ‖y‖ ^ 2 + ‖y + 2 * x‖ ^ 2 := by
  have h := parallelogram_law_with_norm (𝕜 := ℂ) x (x + y)
  have hPlus : x + (x + y) = y + 2 * x := by ring
  have hMinus : x - (x + y) = -y := by abel
  rw [hPlus, hMinus, norm_neg] at h
  linarith only [h]

/-- The coefficient-two fifth/phase source estimate has an EXACT gap,
not merely a nonnegative Young remainder. No sign information is lost. -/
theorem thirdFullKinetic_cubicFifthPhase_exactGap244
    (q : ℝ) (hq : 0 ≤ q) (z f : ℂ) :
    2 * q ^ 5 * ‖z‖ ^ 2 +
        2 * h3GlobalSignedPhaseDensity244 q z f =
      q ^ 3 * ‖f‖ ^ 2 +
        q ^ 3 * ‖f + 2 * ((q : ℂ) * z)‖ ^ 2 := by
  let x : ℂ := (q : ℂ) * z
  have hNorm : ‖x‖ ^ 2 = q ^ 2 * ‖z‖ ^ 2 := by
    dsimp only [x]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    ring
  have hPhase : h3GlobalSignedPhaseDensity244 q z f =
      q ^ 3 * ‖x + f‖ ^ 2 := by
    dsimp only [x]
    exact thirdFullKinetic_signedPhase_eq_temporalResidualSquare244 q hq z f
  calc
    2 * q ^ 5 * ‖z‖ ^ 2 +
        2 * h3GlobalSignedPhaseDensity244 q z f =
      q ^ 3 * (2 * ‖x‖ ^ 2 + 2 * ‖x + f‖ ^ 2) := by
        rw [hPhase, hNorm]
        ring
    _ = q ^ 3 * (‖f‖ ^ 2 + ‖f + 2 * x‖ ^ 2) := by
      rw [thirdFullKinetic_complexParallelogramGap244 x f]
    _ = q ^ 3 * ‖f‖ ^ 2 +
          q ^ 3 * ‖f + 2 * ((q : ℂ) * z)‖ ^ 2 := by
      dsimp only [x]
      ring

/-- For positive frequency the factor-two estimate is saturated exactly
when the projected nonlinear Fourier source is minus twice the heat symbol. -/
theorem thirdFullKinetic_cubicFifthPhase_saturation_iff244
    (q : ℝ) (hq : 0 < q) (z f : ℂ) :
    2 * q ^ 5 * ‖z‖ ^ 2 +
        2 * h3GlobalSignedPhaseDensity244 q z f =
      q ^ 3 * ‖f‖ ^ 2 ↔
        f + 2 * ((q : ℂ) * z) = 0 := by
  have hGap := thirdFullKinetic_cubicFifthPhase_exactGap244 q hq.le z f
  constructor
  · intro hSat
    have hZero : q ^ 3 * ‖f + 2 * ((q : ℂ) * z)‖ ^ 2 = 0 := by
      linarith only [hGap, hSat]
    have hCoeff : q ^ 3 ≠ 0 := ne_of_gt (pow_pos hq 3)
    have hNormSq : ‖f + 2 * ((q : ℂ) * z)‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hZero).resolve_left hCoeff
    have hNorm : ‖f + 2 * ((q : ℂ) * z)‖ = 0 := by
      nlinarith only [hNormSq, norm_nonneg (f + 2 * ((q : ℂ) * z))]
    exact norm_eq_zero.mp hNorm
  · intro hSat
    have hZero : q ^ 3 * ‖f + 2 * ((q : ℂ) * z)‖ ^ 2 = 0 := by
      rw [hSat]
      simp
    linarith only [hGap, hZero]

/-- An explicit complex Fourier mode saturates the estimate with positive
signed growth. Hence no universal scalar coefficient strictly below TWO
can replace it; further improvement needs genuine solenoidal structure. -/
theorem thirdFullKinetic_fifthPhase_factorTwo_optimal244
    (C : ℝ) (hC : C < 2) :
    ¬ (∀ q : ℝ, 0 ≤ q → ∀ z f : ℂ,
      q ^ 3 * ‖f‖ ^ 2 ≤
        C * (q ^ 5 * ‖z‖ ^ 2 +
          h3GlobalSignedPhaseDensity244 q z f)) := by
  intro hUniform
  have h := hUniform 1 (by norm_num) (1 : ℂ) (-2 : ℂ)
  have hPhase : h3GlobalSignedPhaseDensity244 1 (1 : ℂ) (-2 : ℂ) = 1 := by
    rw [thirdFullKinetic_signedPhase_eq_temporalResidualSquare244
      1 (by norm_num) (1 : ℂ) (-2 : ℂ)]
    norm_num
  rw [hPhase] at h
  norm_num at h
  linarith only [h, hC]

/-- The exact discarded square persists after localization to ANY measurable
Fourier band. Integrability is inherited from the established fifth, cubic,
and signed phase densities, not from an added high-derivative assumption. -/
theorem thirdFullKinetic_bandCubicFifthPhase_exactGap244
    (S : Set H3FourierPoint3) (hS : MeasurableSet S)
    (z f : H3FourierPoint3 → ℂ)
    (hFifth : Integrable
      (fun ξ => h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3))
    (hCubic : Integrable
      (fun ξ => h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3))
    (hPhase : Integrable
      (fun ξ => h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ) (z ξ) (f ξ))
      (volume : Measure H3FourierPoint3)) :
    2 * (∫ ξ in S,
        h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2 ∂volume) +
      2 * (∫ ξ in S,
        h3GlobalSignedPhaseDensity244
          (h3FourierGradientSquare ξ) (z ξ) (f ξ) ∂volume) =
      (∫ ξ in S,
        h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2 ∂volume) +
      (∫ ξ in S,
        h3FourierGradientSquare ξ ^ 3 *
          ‖f ξ + 2 * ((h3FourierGradientSquare ξ : ℂ) * z ξ)‖ ^ 2 ∂volume) := by
  let a : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2
  let b : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2
  let c : H3FourierPoint3 → ℝ := fun ξ =>
    h3GlobalSignedPhaseDensity244
      (h3FourierGradientSquare ξ) (z ξ) (f ξ)
  let d : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 3 *
      ‖f ξ + 2 * ((h3FourierGradientSquare ξ : ℂ) * z ξ)‖ ^ 2
  have ha : Integrable a volume := hFifth
  have hb : Integrable b volume := hCubic
  have hc : Integrable c volume := hPhase
  have hPoint (ξ : H3FourierPoint3) :
      2 * a ξ + 2 * c ξ = b ξ + d ξ := by
    dsimp only [a, b, c, d]
    simpa only [mul_assoc] using
      (thirdFullKinetic_cubicFifthPhase_exactGap244
        (h3FourierGradientSquare ξ)
        (h3FourierGradientSquare_nonneg ξ) (z ξ) (f ξ))
  have hd : Integrable d volume := by
    have hAlt : d = fun ξ => 2 * a ξ + 2 * c ξ - b ξ := by
      funext ξ
      have h := hPoint ξ
      linarith only [h]
    rw [hAlt]
    exact ((ha.const_mul 2).add (hc.const_mul 2)).sub hb
  change 2 * (∫ ξ in S, a ξ ∂volume) +
    2 * (∫ ξ in S, c ξ ∂volume) =
    (∫ ξ in S, b ξ ∂volume) +
    (∫ ξ in S, d ξ ∂volume)
  have hLeft :
      (∫ ξ in S, 2 * a ξ + 2 * c ξ ∂volume) =
        2 * (∫ ξ in S, a ξ ∂volume) +
          2 * (∫ ξ in S, c ξ ∂volume) := by
    rw [integral_add (ha.const_mul 2).integrableOn
      (hc.const_mul 2).integrableOn]
    rw [integral_const_mul, integral_const_mul]
  have hRight :
      (∫ ξ in S, b ξ + d ξ ∂volume) =
        (∫ ξ in S, b ξ ∂volume) +
          (∫ ξ in S, d ξ ∂volume) :=
    integral_add hb.integrableOn hd.integrableOn
  have hSame :
      (∫ ξ in S, 2 * a ξ + 2 * c ξ ∂volume) =
        (∫ ξ in S, b ξ + d ξ ∂volume) := by
    apply setIntegral_congr_fun hS
    intro ξ _
    exact hPoint ξ
  exact hLeft.symm.trans (hSame.trans hRight)

/-- Actual strict-time physical Fourier state. The equality includes the
positive highpass spectral rigidity defect, not merely a forcing bound. -/
theorem thirdFullPhysical_highCubicFifthPhase_exactGap_coordinate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) +
    2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ)
        (h3SpectralScalarRawFourierL2 (U j) ξ)
        (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume) =
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 ∂volume) +
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence U U j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let z : H3FourierPoint3 → ℂ :=
    fun ξ => h3SpectralScalarRawFourierL2 (U j) ξ
  let f : H3FourierPoint3 → ℂ :=
    fun ξ => h3RawFinLerayOuterProductDivergence U U j ξ
  let aa : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2
  let bb : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2
  let gg : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 4 * (inner ℂ (z ξ) (f ξ)).re
  have ha : Integrable aa volume := by
    change Integrable (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2) volume
    simpa only [U, htAbs] using
      (integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
        hH3 hClass ht j)
  have hb : Integrable bb volume := by
    change Integrable
      (h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j) volume
    exact integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
      hH3 hClass ht j
  have hg : Integrable gg volume := by
    change Integrable
      (h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
        hH3 hClass ht j) volume
    exact integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
      hH3 hClass ht j
  have hc : Integrable
      (fun ξ : H3FourierPoint3 =>
        h3GlobalSignedPhaseDensity244
          (h3FourierGradientSquare ξ) (z ξ) (f ξ)) volume := by
    change Integrable (fun ξ : H3FourierPoint3 =>
      aa ξ + bb ξ + 2 * gg ξ) volume
    exact (ha.add hb).add (hg.const_mul 2)
  change 2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2 ∂volume) +
    2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ) (z ξ) (f ξ) ∂volume) =
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2 ∂volume) +
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 *
        ‖f ξ + 2 * ((h3FourierGradientSquare ξ : ℂ) * z ξ)‖ ^ 2 ∂volume)
  exact thirdFullKinetic_bandCubicFifthPhase_exactGap244
    (h3TerminalRadialFrequencyBelow ρ)ᶜ
    (measurableSet_h3TerminalRadialFrequencyBelow ρ).compl
    z f ha hb hc

end
end PrimeTensor.FirstMonomialTriad
