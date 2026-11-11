import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalLocalizedFourthQHighpass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalSignedPhaseDefect244
import Mathlib.Tactic

/-!
# Critical H³: derivative-free highpass forcing/fifth/phase balance

The exact signed Fourier phase defect is retained rather than replacing it
by a norm of the fourth-Q source. Its previously proved amplitude lower
bound implies, for q >= 0 and arbitrary complex z and f,

  q³ |f|² <= 2 q⁵ |z|² + 2 Phase(q,z,f).

This inequality is sharp at the amplitude level: it follows from the exact
identity 2 a² + 2(a-b)² - b² = (2a-b)², with a=q|z|, b=|f|.

We integrate on every complementary measurable Fourier ball at an actual
strict physical time, then sum the three solenoidal Leray coordinates.
Unlike the fourth-Q highpass route, this incurs NO additional Fourier
derivative. The right-hand high fifth and high phase expenditures are real,
nonnegative physical spectral costs, NOT known terminal-uniform quantities.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeCriticalHighFifthPhase244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalHighFifthPhase244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The nonlinear cubic square mass is bounded by twice the exact physical
fifth velocity square plus twice the signed phase defect, frequencywise.
No higher-order moment is introduced. -/
theorem thirdFullKinetic_cubic_le_twoFifthPhase_density244
    (q : ℝ) (hq : 0 ≤ q) (z f : ℂ) :
    q ^ 3 * ‖f‖ ^ 2 ≤
      2 * q ^ 5 * ‖z‖ ^ 2 +
        2 * h3GlobalSignedPhaseDensity244 q z f := by
  have hPhase :=
    h3_globalSignedPhaseDensity_ge_amplitudeMismatch244 q hq z f
  have hSquare :
      0 ≤ q ^ 3 * (2 * q * ‖z‖ - ‖f‖) ^ 2 :=
    mul_nonneg (pow_nonneg hq 3) (sq_nonneg _)
  have hAmplitude :
      q ^ 3 * ‖f‖ ^ 2 ≤
        2 * q ^ 5 * ‖z‖ ^ 2 +
          2 * (q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2) := by
    calc
      q ^ 3 * ‖f‖ ^ 2 =
          2 * q ^ 5 * ‖z‖ ^ 2 +
            2 * (q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2) -
              q ^ 3 * (2 * q * ‖z‖ - ‖f‖) ^ 2 := by ring
      _ ≤ 2 * q ^ 5 * ‖z‖ ^ 2 +
            2 * (q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2) :=
        sub_le_self _ hSquare
  have hTwice :
      2 * (q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2) ≤
        2 * h3GlobalSignedPhaseDensity244 q z f :=
    mul_le_mul_of_nonneg_left hPhase (by norm_num : (0 : ℝ) ≤ 2)
  have hLift :
      2 * q ^ 5 * ‖z‖ ^ 2 +
          2 * (q ^ 3 * (q * ‖z‖ - ‖f‖) ^ 2) ≤
        2 * q ^ 5 * ‖z‖ ^ 2 +
          2 * h3GlobalSignedPhaseDensity244 q z f :=
    add_le_add_right hTwice _
  exact hAmplitude.trans hLift

/-- Integrate the sharp pointwise bound on ANY measurable Fourier band.
Integrability is explicit; no terminal-time supremum is postulated. -/
theorem thirdFullKinetic_bandCubic_le_twoFifthPhase244
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
    (∫ ξ in S,
        h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2 ∂volume) ≤
      2 * (∫ ξ in S,
        h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2 ∂volume) +
      2 * (∫ ξ in S,
        h3GlobalSignedPhaseDensity244
          (h3FourierGradientSquare ξ) (z ξ) (f ξ) ∂volume) := by
  let a : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2
  let b : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2
  let c : H3FourierPoint3 → ℝ := fun ξ =>
    h3GlobalSignedPhaseDensity244
      (h3FourierGradientSquare ξ) (z ξ) (f ξ)
  have ha : Integrable a volume := hFifth
  have hb : Integrable b volume := hCubic
  have hc : Integrable c volume := hPhase
  have hPoint : ∀ ξ : H3FourierPoint3,
      b ξ ≤ 2 * a ξ + 2 * c ξ := by
    intro ξ
    simpa only [a, b, c, mul_assoc] using
      (thirdFullKinetic_cubic_le_twoFifthPhase_density244
        (h3FourierGradientSquare ξ)
        (h3FourierGradientSquare_nonneg ξ) (z ξ) (f ξ))
  change (∫ ξ in S, b ξ ∂volume) ≤
    2 * (∫ ξ in S, a ξ ∂volume) +
      2 * (∫ ξ in S, c ξ ∂volume)
  calc
    (∫ ξ in S, b ξ ∂volume) ≤
        ∫ ξ in S, 2 * a ξ + 2 * c ξ ∂volume := by
      exact setIntegral_mono_on hb.integrableOn
        ((ha.const_mul 2).add (hc.const_mul 2)).integrableOn
        hS (fun ξ _ => hPoint ξ)
    _ = (∫ ξ in S, 2 * a ξ ∂volume) +
          (∫ ξ in S, 2 * c ξ ∂volume) := by
      exact integral_add (ha.const_mul 2).integrableOn
        (hc.const_mul 2).integrableOn
    _ = 2 * (∫ ξ in S, a ξ ∂volume) +
          2 * (∫ ξ in S, c ξ ∂volume) := by
      rw [integral_const_mul, integral_const_mul]

/-- Apply the derivative-free highpass coercivity to the actual physical
velocity and solenoidal projected Leray source at a strict PDE time. -/
theorem thirdFullPhysical_highCubic_le_twoHighFifthPhase_coordinate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        h3FourierGradientSquare ξ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 ∂volume) ≤
      2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        h3FourierGradientSquare ξ ^ 5 *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) +
      2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        h3GlobalSignedPhaseDensity244
          (h3FourierGradientSquare ξ)
          (h3SpectralScalarRawFourierL2 (U j) ξ)
          (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume) := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let z : H3FourierPoint3 → ℂ :=
    fun ξ => h3SpectralScalarRawFourierL2 (U j) ξ
  let f : H3FourierPoint3 → ℂ :=
    fun ξ => h3RawFinLerayOuterProductDivergence U U j ξ
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
  have hc : Integrable
      (fun ξ : H3FourierPoint3 =>
        h3GlobalSignedPhaseDensity244
          (h3FourierGradientSquare ξ) (z ξ) (f ξ)) volume := by
    change Integrable (fun ξ : H3FourierPoint3 =>
      a ξ + b ξ + 2 * g ξ) volume
    exact (ha.add hb).add (hg.const_mul 2)
  change (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 * ‖f ξ‖ ^ 2 ∂volume) ≤
    2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 5 * ‖z ξ‖ ^ 2 ∂volume) +
    2 * (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ) (z ξ) (f ξ) ∂volume)
  exact thirdFullKinetic_bandCubic_le_twoFifthPhase244
    (h3TerminalRadialFrequencyBelow ρ)ᶜ
    (measurableSet_h3TerminalRadialFrequencyBelow ρ).compl
    z f ha hb hc

/-- The genuine three-coordinate highpass cubic Leray forcing is paid by
high-frequency fifth velocity dissipation or the signed phase defect,
without invoking the fourth-Q forcing or a sixth velocity moment. -/
theorem thirdFullPhysical_highCubic_le_twoHighFifthPhase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (∑ j : Fin 3,
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        h3FourierGradientSquare ξ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 ∂volume) ≤
      2 * (∑ j : Fin 3,
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3FourierGradientSquare ξ ^ 5 *
            ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) +
      2 * (∑ j : Fin 3,
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3GlobalSignedPhaseDensity244
            (h3FourierGradientSquare ξ)
            (h3SpectralScalarRawFourierL2 (U j) ξ)
            (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume) := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let A (j : Fin 3) : ℝ :=
    ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 ∂volume
  let B (j : Fin 3) : ℝ :=
    ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume
  let C (j : Fin 3) : ℝ :=
    ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ)
        (h3SpectralScalarRawFourierL2 (U j) ξ)
        (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume
  change (∑ j : Fin 3, A j) ≤
    2 * (∑ j : Fin 3, B j) + 2 * (∑ j : Fin 3, C j)
  calc
    (∑ j : Fin 3, A j) ≤
        ∑ j : Fin 3, (2 * B j + 2 * C j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [A, B, C, U, htAbs] using
        (thirdFullPhysical_highCubic_le_twoHighFifthPhase_coordinate244
          hH3 hClass ht ρ j)
    _ = 2 * (∑ j : Fin 3, B j) +
          2 * (∑ j : Fin 3, C j) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

end
end PrimeTensor.FirstMonomialTriad
