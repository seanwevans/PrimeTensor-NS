import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticMovingRadialGapPDECost
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalOuterHighMaxTail
import Mathlib.Tactic

/-!
# Exact polarization stability for the native signed low-maximum sixth flux

The preceding physical PDE theorem freezes every fixed weighted H3 low radial
band on the original kinetic gaps. To transfer that fact to the *signed*
nonlinear Fourier flux we must first exhibit the actual trilinearity rather
than treating the absolute cubic estimate as a Lipschitz bound.

The genuine complex six-transfer symbol is trilinear in its three complex
polarizations, with NO conjugation of the Fourier inputs. Its difference at
two spectral profiles is exactly three mixed integrands, each containing one
polarization difference. This identity survives the exact low-maximum set
integral. The norm difference is bounded by the integrals of the norms of
those three genuine mixed integrands, with no discarded complex phases.

The low-maximum sector is the complement of the exact `HighMax(R)` set, and
therefore uses the sharp common threshold 2*(R+1). Equality on this band
makes the signed low-maximum integral identical. This file does NOT assume
nor claim an L2-to-cubic integral bound on the mixed terms: obtaining such a
bound is the remaining analytic input to combine PDE freezing with this
exact trilinear identity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev FluxAxisKinetic244 := PrimeTensor.Axis Depth.three
private abbrev FluxPointKinetic244 := H3FourierPoint3
private abbrev FluxPairKinetic244 := FluxPointKinetic244 × FluxPointKinetic244

noncomputable local instance axisFintypeKineticLowMaxPolar244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The real frequency coefficients do not interfere with linearity in the
FIRST complex polarization. This uses the native unconjugated Fourier dot. -/
theorem thirdFullComplexSixthPowerFlux_firstSub244
    (p q r : FluxAxisKinetic244 → ℝ)
    (A A' B C : FluxAxisKinetic244 → ℂ) :
    thirdFullComplexSixthPowerFlux244 p q r A B C -
      thirdFullComplexSixthPowerFlux244 p q r A' B C =
    thirdFullComplexSixthPowerFlux244 p q r (fun j => A j - A' j) B C := by
  classical
  unfold thirdFullComplexSixthPowerFlux244
    thirdFullComplexPolarizationDot244 mixedDot
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Exactly the same native symbol is linear in its MIDDLE complex slot.
No Hermitian or real-amplitude substitution has been made. -/
theorem thirdFullComplexSixthPowerFlux_middleSub244
    (p q r : FluxAxisKinetic244 → ℝ)
    (A B B' C : FluxAxisKinetic244 → ℂ) :
    thirdFullComplexSixthPowerFlux244 p q r A B C -
      thirdFullComplexSixthPowerFlux244 p q r A B' C =
    thirdFullComplexSixthPowerFlux244 p q r A (fun j => B j - B' j) C := by
  classical
  unfold thirdFullComplexSixthPowerFlux244
    thirdFullComplexPolarizationDot244 mixedDot
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Exact linearity of the LAST polarization, including all cubic radial
frequency-gap coefficients. -/
theorem thirdFullComplexSixthPowerFlux_lastSub244
    (p q r : FluxAxisKinetic244 → ℝ)
    (A B C C' : FluxAxisKinetic244 → ℂ) :
    thirdFullComplexSixthPowerFlux244 p q r A B C -
      thirdFullComplexSixthPowerFlux244 p q r A B C' =
    thirdFullComplexSixthPowerFlux244 p q r A B (fun j => C j - C' j) := by
  classical
  unfold thirdFullComplexSixthPowerFlux244
    thirdFullComplexPolarizationDot244 mixedDot
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The genuine complex sixth-power symbol has an EXACT, ordered
three-term polarization difference. One input difference occurs in each
term; this is the required algebraic structure for nonlinear continuity.
No absolute value or a priori norm bound enters the identity. -/
theorem thirdFullComplexSixthPowerFlux_subTelescope244
    (p q r : FluxAxisKinetic244 → ℝ)
    (A A' B B' C C' : FluxAxisKinetic244 → ℂ) :
    thirdFullComplexSixthPowerFlux244 p q r A B C -
      thirdFullComplexSixthPowerFlux244 p q r A' B' C' =
      thirdFullComplexSixthPowerFlux244 p q r
        (fun j => A j - A' j) B C +
      thirdFullComplexSixthPowerFlux244 p q r
        A' (fun j => B j - B' j) C +
      thirdFullComplexSixthPowerFlux244 p q r
        A' B' (fun j => C j - C' j) := by
  have hA := thirdFullComplexSixthPowerFlux_firstSub244 p q r A A' B C
  have hB := thirdFullComplexSixthPowerFlux_middleSub244 p q r A' B B' C
  have hC := thirdFullComplexSixthPowerFlux_lastSub244 p q r A' B' C C'
  calc
    thirdFullComplexSixthPowerFlux244 p q r A B C -
        thirdFullComplexSixthPowerFlux244 p q r A' B' C' =
      (thirdFullComplexSixthPowerFlux244 p q r A B C -
        thirdFullComplexSixthPowerFlux244 p q r A' B C) +
      (thirdFullComplexSixthPowerFlux244 p q r A' B C -
        thirdFullComplexSixthPowerFlux244 p q r A' B' C) +
      (thirdFullComplexSixthPowerFlux244 p q r A' B' C -
        thirdFullComplexSixthPowerFlux244 p q r A' B' C') := by abel
    _ = _ := by rw [hA, hB, hC]

/-- Three potentially different polarization profiles on the *same*
physical momentum-conservation plane. This is the genuine native polynomial,
not an auxiliary scalar amplitude model. -/
noncomputable def thirdFullKineticMixedPolarSixthFlux244
    (P Q W : FluxPointKinetic244 → FluxAxisKinetic244 → ℂ)
    (z : FluxPairKinetic244) : ℂ :=
  thirdFullComplexSixthPowerFlux244
    (WithLp.ofLp z.1)
    (WithLp.ofLp (-(z.1 + z.2)))
    (WithLp.ofLp z.2)
    (P z.1) (Q (-(z.1 + z.2))) (W z.2)

/-- The mixed raw-polarization kernel specializes by definition to the
*actual* solenoidal Schwartz sixth-power integrand, with its complex phase. -/
theorem thirdFullKineticMixedPolarSixthFlux_schwartz244
    (v : FluxAxisKinetic244 → SchwartzMap FluxPointKinetic244 ℂ)
    (z : FluxPairKinetic244) :
    thirdFullKineticMixedPolarSixthFlux244
      (fun ξ => h3SchwartzTriadPolarization v (WithLp.ofLp ξ))
      (fun ξ => h3SchwartzTriadPolarization v (WithLp.ofLp ξ))
      (fun ξ => h3SchwartzTriadPolarization v (WithLp.ofLp ξ)) z =
    thirdFullSchwartzComplexSixthPowerFlux244 v z := rfl

/-- The same exact polarization telescope holds at EVERY triad frequency.
The three mixed terms retain the original polarizations' slot ordering. -/
theorem thirdFullKineticMixedPolarSixthFlux_telescope244
    (P Q : FluxPointKinetic244 → FluxAxisKinetic244 → ℂ)
    (z : FluxPairKinetic244) :
    thirdFullKineticMixedPolarSixthFlux244 P P P z -
      thirdFullKineticMixedPolarSixthFlux244 Q Q Q z =
      thirdFullKineticMixedPolarSixthFlux244
        (fun ξ j => P ξ j - Q ξ j) P P z +
      thirdFullKineticMixedPolarSixthFlux244
        Q (fun ξ j => P ξ j - Q ξ j) P z +
      thirdFullKineticMixedPolarSixthFlux244
        Q Q (fun ξ j => P ξ j - Q ξ j) z := by
  unfold thirdFullKineticMixedPolarSixthFlux244
  simpa only [Pi.sub_apply] using
    (thirdFullComplexSixthPowerFlux_subTelescope244
      (WithLp.ofLp z.1)
      (WithLp.ofLp (-(z.1 + z.2)))
      (WithLp.ofLp z.2)
      (P z.1) (Q z.1)
      (P (-(z.1 + z.2))) (Q (-(z.1 + z.2)))
      (P z.2) (Q z.2))

/-- On the COMPLEMENT of the project's exact high-maximum set, each of the
three conserving Fourier frequencies is strictly below 2*(R+1).
The factor 2 is required; replacing it with R+1 is unjustified. -/
theorem thirdFullKinetic_lowMax_allFrequenciesBelow244
    (R : ℕ) (z : FluxPairKinetic244)
    (hz : z ∈ (thirdFullHighMaxSet244 R)ᶜ) :
    h3FourierGradientMagnitude z.1 < 2 * ((R : ℝ) + 1) ∧
    h3FourierGradientMagnitude (-(z.1 + z.2)) < 2 * ((R : ℝ) + 1) ∧
    h3FourierGradientMagnitude z.2 < 2 * ((R : ℝ) + 1) := by
  have hNot : ¬ 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude z.1)
        (max (h3FourierGradientMagnitude (-(z.1 + z.2)))
          (h3FourierGradientMagnitude z.2)) := by
    simpa only [thirdFullHighMaxSet244, Set.mem_compl_iff,
      Set.mem_ofPred_eq] using hz
  have hMax :
      max (h3FourierGradientMagnitude z.1)
        (max (h3FourierGradientMagnitude (-(z.1 + z.2)))
          (h3FourierGradientMagnitude z.2)) <
        2 * ((R : ℝ) + 1) := lt_of_not_ge hNot
  constructor
  · exact (le_max_left _ _).trans_lt hMax
  constructor
  · exact (le_max_left _ _).trans_lt
      ((le_max_right _ _).trans_lt hMax)
  · exact (le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt hMax)

/-- The true low-maximum flux is insensitive to ANY changes in its
polarization profile outside the common ball of radius 2*(R+1).
This statement is pointwise on the true momentum triad, not an invented
locality assumption about the convolution kernel. -/
theorem thirdFullKinetic_lowMax_polarKernel_congr244
    (R : ℕ)
    (P Q : FluxPointKinetic244 → FluxAxisKinetic244 → ℂ)
    (hAgree : ∀ ξ : FluxPointKinetic244,
      h3FourierGradientMagnitude ξ < 2 * ((R : ℝ) + 1) →
        P ξ = Q ξ)
    (z : FluxPairKinetic244)
    (hz : z ∈ (thirdFullHighMaxSet244 R)ᶜ) :
    thirdFullKineticMixedPolarSixthFlux244 P P P z =
      thirdFullKineticMixedPolarSixthFlux244 Q Q Q z := by
  obtain ⟨hp, hq, hr⟩ :=
    thirdFullKinetic_lowMax_allFrequenciesBelow244 R z hz
  unfold thirdFullKineticMixedPolarSixthFlux244
  rw [hAgree z.1 hp, hAgree (-(z.1 + z.2)) hq, hAgree z.2 hr]

/-- Equality of the original signed LOW-MAXIMUM complex integrals follows
from agreement on the exact common finite frequency ball. No assumption
about the profiles' high-frequency Fourier data is needed. -/
theorem thirdFullKinetic_lowMax_polarIntegral_congr244
    (R : ℕ)
    (P Q : FluxPointKinetic244 → FluxAxisKinetic244 → ℂ)
    (hAgree : ∀ ξ : FluxPointKinetic244,
      h3FourierGradientMagnitude ξ < 2 * ((R : ℝ) + 1) →
        P ξ = Q ξ) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244 P P P z ∂volume.prod volume) =
    ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244 Q Q Q z ∂volume.prod volume := by
  apply setIntegral_congr_ae (thirdFullHighMaxSet_measurable244 R).compl
  exact Filter.Eventually.of_forall
    (fun z hz => thirdFullKinetic_lowMax_polarKernel_congr244 R P Q hAgree z hz)

/-- INTEGRATED exact signed-flux telescope. The hypotheses are ordinary
integrability of the FOUR actual sector integrands; they are explicit
rather than postulated as consequences of weak H3 convergence. -/
theorem thirdFullKinetic_lowMax_integralTelescope244
    (R : ℕ) (P Q : FluxPointKinetic244 → FluxAxisKinetic244 → ℂ)
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
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume)) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244 P P P z ∂volume.prod volume) -
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244 Q Q Q z ∂volume.prod volume) =
    ((∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244
        (fun ξ j => P ξ j - Q ξ j) P P z ∂volume.prod volume) +
     (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244
        Q (fun ξ j => P ξ j - Q ξ j) P z ∂volume.prod volume)) +
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244
        Q Q (fun ξ j => P ξ j - Q ξ j) z ∂volume.prod volume) := by
  calc
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244 P P P z ∂volume.prod volume) -
      (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullKineticMixedPolarSixthFlux244 Q Q Q z ∂volume.prod volume) =
        ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
          (thirdFullKineticMixedPolarSixthFlux244 P P P z -
           thirdFullKineticMixedPolarSixthFlux244 Q Q Q z) ∂volume.prod volume :=
        (integral_sub hP hQ).symm
    _ = ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
          (thirdFullKineticMixedPolarSixthFlux244
             (fun ξ j => P ξ j - Q ξ j) P P z +
           thirdFullKineticMixedPolarSixthFlux244
             Q (fun ξ j => P ξ j - Q ξ j) P z +
           thirdFullKineticMixedPolarSixthFlux244
             Q Q (fun ξ j => P ξ j - Q ξ j) z) ∂volume.prod volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (fun z => thirdFullKineticMixedPolarSixthFlux_telescope244 P Q z)
    _ = _ := by
      let S : Set FluxPairKinetic244 := (thirdFullHighMaxSet244 R)ᶜ
      let μ : Measure FluxPairKinetic244 := volume.prod volume
      let f : FluxPairKinetic244 → ℂ :=
        thirdFullKineticMixedPolarSixthFlux244
          (fun ξ j => P ξ j - Q ξ j) P P
      let g : FluxPairKinetic244 → ℂ :=
        thirdFullKineticMixedPolarSixthFlux244
          Q (fun ξ j => P ξ j - Q ξ j) P
      let h : FluxPairKinetic244 → ℂ :=
        thirdFullKineticMixedPolarSixthFlux244
          Q Q (fun ξ j => P ξ j - Q ξ j)
      have hf : IntegrableOn f S μ := h1
      have hg : IntegrableOn g S μ := h2
      have hh : IntegrableOn h S μ := h3
      have hfg : IntegrableOn (f + g) S μ := hf.add hg
      have hSplitPair :
          (∫ z in S, f z + g z ∂μ) =
            (∫ z in S, f z ∂μ) + (∫ z in S, g z ∂μ) := by
        simpa only [Pi.add_apply] using (integral_add hf hg)
      have hSplitThird :
          (∫ z in S, (f z + g z) + h z ∂μ) =
            (∫ z in S, f z + g z ∂μ) + (∫ z in S, h z ∂μ) := by
        simpa only [Pi.add_apply] using (integral_add hfg hh)
      change (∫ z in S, (f z + g z) + h z ∂μ) =
        ((∫ z in S, f z ∂μ) + (∫ z in S, g z ∂μ)) +
          (∫ z in S, h z ∂μ)
      calc
        _ = (∫ z in S, f z + g z ∂μ) + (∫ z in S, h z ∂μ) :=
          hSplitThird
        _ = _ := by rw [hSplitPair]

/-- Quantitative, COMPLEX-PHASE-PRESERVING difference budget: the change
in the signed low-maximum flux is bounded by three integrals, each with
one genuine polarization difference and two undifferenced slots.
No spurious sign or positivity of a Fourier coefficient is assumed. -/
theorem thirdFullKinetic_lowMax_integralDifferenceBudget244
    (R : ℕ) (P Q : FluxPointKinetic244 → FluxAxisKinetic244 → ℂ)
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
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume)) :
    ‖(∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244 P P P z ∂volume.prod volume) -
      (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244 Q Q Q z ∂volume.prod volume)‖ ≤
    ((∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        ‖thirdFullKineticMixedPolarSixthFlux244
          (fun ξ j => P ξ j - Q ξ j) P P z‖ ∂volume.prod volume) +
      (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        ‖thirdFullKineticMixedPolarSixthFlux244
          Q (fun ξ j => P ξ j - Q ξ j) P z‖ ∂volume.prod volume)) +
      (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        ‖thirdFullKineticMixedPolarSixthFlux244
          Q Q (fun ξ j => P ξ j - Q ξ j) z‖ ∂volume.prod volume) := by
  rw [thirdFullKinetic_lowMax_integralTelescope244 R P Q hP hQ h1 h2 h3]
  calc
    ‖(∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244
          (fun ξ j => P ξ j - Q ξ j) P P z ∂volume.prod volume) +
       (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244
          Q (fun ξ j => P ξ j - Q ξ j) P z ∂volume.prod volume) +
       (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244
          Q Q (fun ξ j => P ξ j - Q ξ j) z ∂volume.prod volume)‖ ≤
      (‖∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244
          (fun ξ j => P ξ j - Q ξ j) P P z ∂volume.prod volume‖ +
       ‖∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244
          Q (fun ξ j => P ξ j - Q ξ j) P z ∂volume.prod volume‖) +
       ‖∫ z in (thirdFullHighMaxSet244 R)ᶜ,
        thirdFullKineticMixedPolarSixthFlux244
          Q Q (fun ξ j => P ξ j - Q ξ j) z ∂volume.prod volume‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ :=
      add_le_add
        (add_le_add (norm_integral_le_integral_norm _)
          (norm_integral_le_integral_norm _))
        (norm_integral_le_integral_norm _)

end
end PrimeTensor.FirstMonomialTriad
