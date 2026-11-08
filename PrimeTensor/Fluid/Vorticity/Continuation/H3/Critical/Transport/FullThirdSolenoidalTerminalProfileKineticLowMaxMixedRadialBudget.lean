import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticLowMaxFluxPolarization
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalRadialShellFluxGain
import Mathlib.Tactic

/-!
# Exact finite-radius coefficient for the mixed sixth-power Fourier flux

The previous theorem supplied an exact three-slot polarization telescope on
LowMax(R), the complement of the project's literal HighMax(R) sector.
Here we bound the *coefficient* of each mixed solenoidal sixth-power term.

The true gradient cutoff is 2*(R+1), not R+1.  On its complement the three
momentum-conserving ordinary Euclidean frequencies are bounded by that value,
so the maximum squared radius and its spread are both <= [2*(R+1)]².
The existing native radial-spread estimate then gives

  |F₆(P,Q,W)| <= 3*[2*(R+1)]⁶ * B₆(P,Q,W)

for the genuine complex six-transfer contraction budget B₆, with *distinct*
polarization fields in each slot.  This holds with no divergence-free premise
because the polynomial inequality is valid even before physical cancellation.

Integrating preserves the exact sector and gives a quantitative three-budget
bound for the actual polarization difference.  No claim is made that these
three budgets are bounded by H³ spectral L² differences: that requires a
separate mixed L²-L²-L¹ Fourier-convolution argument.  In particular, the
previous physical low-band PDE freezing theorem is not silently used to
bound the three mixed integrals.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev MixAxis244 := PrimeTensor.Axis Depth.three
private abbrev MixPoint244 := H3FourierPoint3
private abbrev MixPair244 := MixPoint244 × MixPoint244

noncomputable local instance axisFintypeKineticMixedRadial244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The native *mixed* three-channel complex contraction budget.  Each slot
may be a different polarization profile; no false symmetry is assumed. -/
noncomputable def thirdFullKineticMixedPolarSixthBudget244
    (P Q W : MixPoint244 → MixAxis244 → ℂ) (z : MixPair244) : ℝ :=
  thirdFullComplexSixthFluxContractionBudget244
    (WithLp.ofLp z.1)
    (WithLp.ofLp (-(z.1 + z.2)))
    (WithLp.ofLp z.2)
    (P z.1) (Q (-(z.1 + z.2))) (W z.2)

/-- The mixed contraction budget is nonnegative even for complex inputs
with unrelated phases. -/
theorem thirdFullKineticMixedPolarSixthBudget_nonneg244
    (P Q W : MixPoint244 → MixAxis244 → ℂ) (z : MixPair244) :
    0 ≤ thirdFullKineticMixedPolarSixthBudget244 P Q W z := by
  unfold thirdFullKineticMixedPolarSixthBudget244
    thirdFullComplexSixthFluxContractionBudget244
  positivity

/-- The genuine mixed native flux retains the exact linear radial-spread
gain, BEFORE imposing incompressibility or taking a Fourier integral. -/
theorem thirdFullKineticMixedPolarSixthFlux_radialSpread_le244
    (P Q W : MixPoint244 → MixAxis244 → ℂ) (z : MixPair244) :
    ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ≤
      (3 * (thirdFullTriadSquareRadiusMax244
          (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
          (WithLp.ofLp z.2)) ^ 2 *
        thirdFullTriadSquareRadiusSpread244
          (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
          (WithLp.ofLp z.2)) *
        thirdFullKineticMixedPolarSixthBudget244 P Q W z := by
  exact thirdFullComplexSixthPowerFlux_radialSpread_le244
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
    (WithLp.ofLp z.2)
    (P z.1) (Q (-(z.1 + z.2))) (W z.2)

/-- The *same* low-maximum Fourier sector simultaneously bounds the
squared-radius maximum and the squared-radius spread.  In particular the
physical 2*pi frequency normalization is not dropped. -/
theorem thirdFullKinetic_lowMax_squareRadiusAndSpread_le244
    (R : ℕ) (z : MixPair244)
    (hz : z ∈ (thirdFullHighMaxSet244 R)ᶜ) :
    thirdFullTriadSquareRadiusMax244
        (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
        (WithLp.ofLp z.2) ≤ (2 * ((R : ℝ) + 1)) ^ 2 ∧
    thirdFullTriadSquareRadiusSpread244
        (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
        (WithLp.ofLp z.2) ≤ (2 * ((R : ℝ) + 1)) ^ 2 := by
  let p : MixAxis244 → ℝ := WithLp.ofLp z.1
  let q : MixAxis244 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : MixAxis244 → ℝ := WithLp.ofLp z.2
  let ρ : ℝ := 2 * ((R : ℝ) + 1)
  have hπ : (1 : ℝ) ≤ 2 * Real.pi := by
    have h := Real.pi_gt_three
    linarith only [h]
  have hRadius (ξ : MixPoint244)
      (hξ : h3FourierGradientMagnitude ξ < ρ) : ‖ξ‖ ≤ ρ := by
    calc
      ‖ξ‖ = (1 : ℝ) * ‖ξ‖ := by ring
      _ ≤ (2 * Real.pi) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hπ (norm_nonneg ξ)
      _ ≤ ρ := hξ.le
  obtain ⟨hp, hq, hr⟩ :=
    thirdFullKinetic_lowMax_allFrequenciesBelow244 R z hz
  have hpBound : frequencyNorm p ≤ ρ := by
    simpa only [frequencyNorm, p, WithLp.toLp_ofLp] using
      hRadius z.1 hp
  have hqBound : frequencyNorm q ≤ ρ := by
    simpa only [frequencyNorm, q, WithLp.toLp_ofLp] using
      hRadius (-(z.1 + z.2)) hq
  have hrBound : frequencyNorm r ≤ ρ := by
    simpa only [frequencyNorm, r, WithLp.toLp_ofLp] using
      hRadius z.2 hr
  have hpp : thirdTriadAxisDot244 p p = frequencyNorm p ^ 2 := by
    simpa only [thirdTriadAxisDot244, dot] using
      (dot_self_eq_frequencyNorm_sq p)
  have hqq : thirdTriadAxisDot244 q q = frequencyNorm q ^ 2 := by
    simpa only [thirdTriadAxisDot244, dot] using
      (dot_self_eq_frequencyNorm_sq q)
  have hrr : thirdTriadAxisDot244 r r = frequencyNorm r ^ 2 := by
    simpa only [thirdTriadAxisDot244, dot] using
      (dot_self_eq_frequencyNorm_sq r)
  have hpSq : thirdTriadAxisDot244 p p ≤ ρ ^ 2 := by
    rw [hpp]
    exact pow_le_pow_left₀ (norm_nonneg _) hpBound 2
  have hqSq : thirdTriadAxisDot244 q q ≤ ρ ^ 2 := by
    rw [hqq]
    exact pow_le_pow_left₀ (norm_nonneg _) hqBound 2
  have hrSq : thirdTriadAxisDot244 r r ≤ ρ ^ 2 := by
    rw [hrr]
    exact pow_le_pow_left₀ (norm_nonneg _) hrBound 2
  have hMax : thirdFullTriadSquareRadiusMax244 p q r ≤ ρ ^ 2 := by
    unfold thirdFullTriadSquareRadiusMax244
    exact max_le hpSq (max_le hqSq hrSq)
  have hMin : 0 ≤ min (thirdTriadAxisDot244 p p)
      (min (thirdTriadAxisDot244 q q) (thirdTriadAxisDot244 r r)) :=
    le_min (thirdFull_axisSquareRadius_nonneg244 p)
      (le_min (thirdFull_axisSquareRadius_nonneg244 q)
        (thirdFull_axisSquareRadius_nonneg244 r))
  have hSpread : thirdFullTriadSquareRadiusSpread244 p q r ≤ ρ ^ 2 := by
    unfold thirdFullTriadSquareRadiusSpread244
    linarith only [hMax, hMin]
  exact ⟨hMax, hSpread⟩

/-- Finite-radius coefficient bound for any three distinct complex
polarizations. The sixth-degree radius factor is the exact homogeneity of
the three cubic squared-radius gaps; the remaining Fourier derivative sits
inside the unmodified contraction budget. -/
theorem thirdFullKinetic_lowMax_mixedFlux_le_radiusBudget244
    (R : ℕ) (P Q W : MixPoint244 → MixAxis244 → ℂ)
    (z : MixPair244) (hz : z ∈ (thirdFullHighMaxSet244 R)ᶜ) :
    ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ≤
      (3 * (2 * ((R : ℝ) + 1)) ^ 6) *
        thirdFullKineticMixedPolarSixthBudget244 P Q W z := by
  let p : MixAxis244 → ℝ := WithLp.ofLp z.1
  let q : MixAxis244 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : MixAxis244 → ℝ := WithLp.ofLp z.2
  let ρ : ℝ := 2 * ((R : ℝ) + 1)
  let S : ℝ := thirdFullTriadSquareRadiusMax244 p q r
  let Δ : ℝ := thirdFullTriadSquareRadiusSpread244 p q r
  let B : ℝ := thirdFullKineticMixedPolarSixthBudget244 P Q W z
  have hRadius := thirdFullKinetic_lowMax_squareRadiusAndSpread_le244 R z hz
  have hS : S ≤ ρ ^ 2 := hRadius.1
  have hΔ : Δ ≤ ρ ^ 2 := hRadius.2
  have hS0 : 0 ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact (thirdFull_axisSquareRadius_nonneg244 p).trans (le_max_left _ _)
  have hΔ0 : 0 ≤ Δ := thirdFullTriadSquareRadiusSpread_nonneg244 p q r
  have hB0 : 0 ≤ B := thirdFullKineticMixedPolarSixthBudget_nonneg244 P Q W z
  have hSq : S ^ 2 ≤ (ρ ^ 2) ^ 2 := pow_le_pow_left₀ hS0 hS 2
  have hMul : S ^ 2 * Δ ≤ (ρ ^ 2) ^ 2 * ρ ^ 2 :=
    mul_le_mul hSq hΔ hΔ0 (sq_nonneg _)
  have hK : 3 * S ^ 2 * Δ ≤ 3 * ρ ^ 6 := by
    calc
      3 * S ^ 2 * Δ = 3 * (S ^ 2 * Δ) := by ring
      _ ≤ 3 * ((ρ ^ 2) ^ 2 * ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hMul (by norm_num)
      _ = 3 * ρ ^ 6 := by ring
  have hOriginal := thirdFullKineticMixedPolarSixthFlux_radialSpread_le244 P Q W z
  change ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ≤
    (3 * ρ ^ 6) * B
  exact hOriginal.trans (mul_le_mul_of_nonneg_right hK hB0)

/-- The pointwise mixed coefficient gain integrates over the TRUE low-max
sector without taking an unproved nonlinear limit. Both integrability
contracts are explicit (and are subsequently discharged by Fourier moments). -/
theorem thirdFullKinetic_lowMax_mixedIntegral_le_radiusBudget244
    (R : ℕ) (P Q W : MixPoint244 → MixAxis244 → ℂ)
    (hFlux : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244 P Q W)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hBudget : IntegrableOn (thirdFullKineticMixedPolarSixthBudget244 P Q W)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume)) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ∂volume.prod volume) ≤
      (3 * (2 * ((R : ℝ) + 1)) ^ 6) *
        ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
          thirdFullKineticMixedPolarSixthBudget244 P Q W z ∂volume.prod volume := by
  let S : Set MixPair244 := (thirdFullHighMaxSet244 R)ᶜ
  let μ : Measure MixPair244 := volume.prod volume
  let K : ℝ := 3 * (2 * ((R : ℝ) + 1)) ^ 6
  have hEstimate : ∀ᵐ z ∂(μ.restrict S),
      ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ≤
        K * thirdFullKineticMixedPolarSixthBudget244 P Q W z := by
    filter_upwards [ae_restrict_mem (thirdFullHighMaxSet_measurable244 R).compl]
      with z hz
    exact thirdFullKinetic_lowMax_mixedFlux_le_radiusBudget244 R P Q W z hz
  have hCompare := setIntegral_mono_ae_restrict
    hFlux.norm (hBudget.const_mul K) hEstimate
  change (∫ z in S, ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖ ∂μ) ≤
    K * (∫ z in S, thirdFullKineticMixedPolarSixthBudget244 P Q W z ∂μ)
  simpa only [integral_const_mul] using hCompare

/-- Explicit radius-six coefficient multiplying the THREE exact complex
mixed-contraction budgets in the native polarization telescope.
No hidden L²-L²-L¹ estimate is asserted; the budgets are the remaining
convolution quantities to bound by weighted H³ spectral data. -/
theorem thirdFullKinetic_lowMax_difference_le_threeRadiusBudgets244
    (R : ℕ) (P Q : MixPoint244 → MixAxis244 → ℂ)
    (hP : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244 P P P)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hQ : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244 Q Q Q)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (h1 : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244
      (fun ξ j => P ξ j - Q ξ j) P P)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (h2 : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244
      Q (fun ξ j => P ξ j - Q ξ j) P)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (h3 : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244
      Q Q (fun ξ j => P ξ j - Q ξ j))
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hB1 : IntegrableOn (thirdFullKineticMixedPolarSixthBudget244
      (fun ξ j => P ξ j - Q ξ j) P P)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hB2 : IntegrableOn (thirdFullKineticMixedPolarSixthBudget244
      Q (fun ξ j => P ξ j - Q ξ j) P)
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hB3 : IntegrableOn (thirdFullKineticMixedPolarSixthBudget244
      Q Q (fun ξ j => P ξ j - Q ξ j))
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume)) :
    ‖(∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244 P P P z ∂volume.prod volume) -
      (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244 Q Q Q z ∂volume.prod volume)‖ ≤
      (3 * (2 * ((R : ℝ) + 1)) ^ 6) *
        ((∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullKineticMixedPolarSixthBudget244
              (fun ξ j => P ξ j - Q ξ j) P P z ∂volume.prod volume) +
         (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullKineticMixedPolarSixthBudget244
              Q (fun ξ j => P ξ j - Q ξ j) P z ∂volume.prod volume) +
         (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullKineticMixedPolarSixthBudget244
              Q Q (fun ξ j => P ξ j - Q ξ j) z ∂volume.prod volume)) := by
  let K : ℝ := 3 * (2 * ((R : ℝ) + 1)) ^ 6
  have h1' := thirdFullKinetic_lowMax_mixedIntegral_le_radiusBudget244
    R (fun ξ j => P ξ j - Q ξ j) P P h1 hB1
  have h2' := thirdFullKinetic_lowMax_mixedIntegral_le_radiusBudget244
    R Q (fun ξ j => P ξ j - Q ξ j) P h2 hB2
  have h3' := thirdFullKinetic_lowMax_mixedIntegral_le_radiusBudget244
    R Q Q (fun ξ j => P ξ j - Q ξ j) h3 hB3
  have hInitial := thirdFullKinetic_lowMax_integralDifferenceBudget244
    R P Q hP hQ h1 h2 h3
  calc
    _ ≤ ((∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            ‖thirdFullKineticMixedPolarSixthFlux244
              (fun ξ j => P ξ j - Q ξ j) P P z‖ ∂volume.prod volume) +
          (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            ‖thirdFullKineticMixedPolarSixthFlux244
              Q (fun ξ j => P ξ j - Q ξ j) P z‖ ∂volume.prod volume)) +
          (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            ‖thirdFullKineticMixedPolarSixthFlux244
              Q Q (fun ξ j => P ξ j - Q ξ j) z‖ ∂volume.prod volume) := hInitial
    _ ≤ (K * (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullKineticMixedPolarSixthBudget244
              (fun ξ j => P ξ j - Q ξ j) P P z ∂volume.prod volume) +
          K * (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullKineticMixedPolarSixthBudget244
              Q (fun ξ j => P ξ j - Q ξ j) P z ∂volume.prod volume)) +
          K * (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
            thirdFullKineticMixedPolarSixthBudget244
              Q Q (fun ξ j => P ξ j - Q ξ j) z ∂volume.prod volume) :=
            add_le_add (add_le_add h1' h2') h3'
    _ = _ := by ring

end
end PrimeTensor.FirstMonomialTriad
