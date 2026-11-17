import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedLocalBall
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-!
# The constructed Z³ Galerkin trajectory cannot escape its finite state ball

On the local interval from the actual finite-dimensional Picard flow, the
cutoff-free moving analytic Wiener bound implies a bound on the *norm of the
finite coefficient state itself*. No cardinality or maximal Fourier frequency
enters the 100 bound. The full viscous-plus-complete-Leray vector field also
has the previously proved cutoff-free W_(3/2) speed bound 51000.

The finite-dimensional vector field is continuous and the constructed path
is differentiable; therefore its time integrability is automatic. These are
the inputs to a maximal-interval continuation argument, NOT a claim that the
common existence interval has already been constructed.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set MeasureTheory
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev EscapeIndex244 := thirdFullThreeBandZ3Index244
private abbrev EscapeBand244 := EuclideanSpace ℂ (Fin 3)

/-- Each weighted retained Fourier coefficient is one nonnegative summand
of the genuine finite Galerkin Wiener mass. -/
theorem thirdFullThreeBand_z3GalerkinWiener_singleMode_le244
    (r : ℝ) (s : Finset EscapeIndex244)
    (u : EscapeIndex244 → EscapeBand244)
    (n : EscapeIndex244) (hn : n ∈ s) :
    thirdFullThreeBandZ3Weight244 r n * ‖u n‖ ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r j).le
      (norm_nonneg (u j))) hn

/-- Nonnegative analytic radii make all Fourier weights at least one. -/
theorem thirdFullThreeBand_z3GalerkinWeight_one_le244
    (r : ℝ) (hr : 0 ≤ r) (n : EscapeIndex244) :
    1 ≤ thirdFullThreeBandZ3Weight244 r n := by
  unfold thirdFullThreeBandZ3Weight244
  have hDegree : 0 ≤ thirdFullThreeBandZ3Degree244 n :=
    thirdFullThreeBand_z3Degree_nonneg244 n
  have hProduct : 0 ≤ r * thirdFullThreeBandZ3Degree244 n :=
    mul_nonneg hr hDegree
  have hExp := Real.add_one_le_exp (r * thirdFullThreeBandZ3Degree244 n)
  linarith

/-- A positive-radius Wiener bound controls the actual finite Galerkin
`Pi` norm, with NO dependence on the number of Fourier coefficients. -/
theorem thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244
    (r : ℝ) (hr : 0 ≤ r)
    (s : Finset EscapeIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (C : ℝ) (hC : 0 ≤ C)
    (hMass : thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ C) :
    ‖x‖ ≤ C := by
  classical
  apply (pi_norm_le_iff_of_nonneg hC).2
  intro i
  have hMode := thirdFullThreeBand_z3GalerkinWiener_singleMode_le244
    r s (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) i.1 i.2
  have hWeight := thirdFullThreeBand_z3GalerkinWeight_one_le244 r hr i.1
  rw [thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s x i.1 i.2] at hMode
  have hProd : (thirdFullThreeBandZ3Weight244 r i.1 - 1) * ‖x i‖ ≥ 0 :=
    mul_nonneg (sub_nonneg.mpr hWeight) (norm_nonneg (x i))
  have hCap := hMode.trans hMass
  nlinarith

/-- Under the high 9/5 analytic ball, even the norm of the *actual
finite-dimensional derivative vector field* is at most 51000 uniformly in
the Fourier cutoff. This is a finite-state, not just Wiener-mass, bound. -/
theorem thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244
    (mu : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset EscapeIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hHigh : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100) :
    ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s x‖ ≤ 51000 := by
  classical
  have hSpeed := thirdFullThreeBand_z3GalerkinNSField_speed51000_100Ball244
    mu hmu hmuMax s (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) hHigh
  have hEqual :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s
          (thirdFullThreeBandZ3GalerkinFiniteField244 mu s x)) =
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinNSField244 mu s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x)) := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
    apply Finset.sum_congr rfl
    intro n hn
    rw [thirdFullThreeBand_z3GalerkinFiniteExtend_on244 s
      (thirdFullThreeBandZ3GalerkinFiniteField244 mu s x) n hn]
    rfl
  apply thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244
    (Real.log (3 / 2 : ℝ)) (Real.log_nonneg (by norm_num)) s
    (thirdFullThreeBandZ3GalerkinFiniteField244 mu s x)
    51000 (by norm_num)
  simpa only [hEqual] using hSpeed

/-- Strong Picard differentiability automatically makes the *entire actual
finite coefficient field* Bochner-integrable on each compact subinterval.
No independent time-integrability assumption is supplied. -/
theorem thirdFullThreeBand_z3GalerkinFiniteField_intervalIntegrable244
    (mu a b : ℝ) (hab : a ≤ b)
    (s : Finset EscapeIndex244)
    (alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hODE : ∀ t ∈ Icc a b,
      HasDerivAt alpha
        (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t) :
    IntervalIntegrable
      (fun t : ℝ => thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t))
      volume a b := by
  have hF : Continuous (thirdFullThreeBandZ3GalerkinFiniteField244 mu s) :=
    (thirdFullThreeBand_z3GalerkinFiniteField_contDiff244 mu s).continuous
  have hContinuous : ContinuousOn
      (fun t : ℝ => thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t))
      (Icc a b) := by
    intro t ht
    exact (hF.continuousAt.comp (hODE t ht).continuousAt).continuousWithinAt
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le hab] using hContinuous

/-- Construct the genuine finite Galerkin trajectory, then obtain the
100 bound in the actual finite-dimensional state norm, the uniform 9/5
analytic mass, and the 51000 full-Leray field-speed bound. The time
integrability of the finite field is derived, not postulated.

The existence interval is currently positive but cutoff-dependent: the
maximal-continuation / blow-up-alternative bridge remains to be proved. -/
theorem thirdFullThreeBand_z3GalerkinConstructedLocal_nonEscapeAndSpeed244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset EscapeIndex244)
    (x0 : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x0) < 100) :
    ∃ delta : ℝ,
      0 < delta ∧
      delta ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 ∧
      ∃ alpha : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
        alpha a = x0 ∧
        (∀ t ∈ Icc a (a + delta),
          HasDerivAt alpha
            (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)) t) ∧
        (∀ t ∈ Icc a (a + delta), ‖alpha t‖ ≤ 100) ∧
        (∀ t ∈ Icc a (a + delta),
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (9 / 5 : ℝ)) s
            (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) ≤ 100) ∧
        (∀ t ∈ Icc a (a + delta),
          ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)‖ ≤ 51000) ∧
        (∀ t ∈ Icc a (a + delta),
          thirdFullThreeBandZ3GalerkinWienerMass244
            (Real.log (3 / 2 : ℝ)) s
            (thirdFullThreeBandZ3GalerkinNSField244 mu s
              (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t))) ≤ 51000) ∧
        IntervalIntegrable
          (fun t : ℝ => thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t))
          volume a (a + delta) := by
  classical
  obtain ⟨delta, hDelta, hWindow, alpha, hInit, hODE, hMoving⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteField_constructedLocalMovingBall244
      mu a hmu s x0 hInitial
  have hHigh (t : ℝ) (ht : t ∈ Icc a (a + delta)) :
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (9 / 5 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) ≤ 100 := by
    have hElapsed : t - a ≤
        thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 := by
      linarith [ht.2, hWindow]
    exact thirdFullThreeBand_z3MovingRadius_highBall244 a t hElapsed s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t))
      (hMoving t ht)
  have hState (t : ℝ) (ht : t ∈ Icc a (a + delta)) :
      ‖alpha t‖ ≤ 100 := by
    exact thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244
      (Real.log (9 / 5 : ℝ)) (Real.log_nonneg (by norm_num))
      s (alpha t) 100 (by norm_num) (hHigh t ht)
  have hSpeed (t : ℝ) (ht : t ∈ Icc a (a + delta)) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s
        (thirdFullThreeBandZ3GalerkinNSField244 mu s
          (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t))) ≤ 51000 :=
    thirdFullThreeBand_z3GalerkinNSField_speed51000_100Ball244
      mu hmu hmuMax s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s (alpha t)) (hHigh t ht)
  have hFiniteSpeed (t : ℝ) (ht : t ∈ Icc a (a + delta)) :
      ‖thirdFullThreeBandZ3GalerkinFiniteField244 mu s (alpha t)‖ ≤ 51000 :=
    thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244
      mu hmu hmuMax s (alpha t) (hHigh t ht)
  have hab : a ≤ a + delta := by linarith
  have hIntegrable :=
    thirdFullThreeBand_z3GalerkinFiniteField_intervalIntegrable244
      mu a (a + delta) hab s alpha hODE
  exact ⟨delta, hDelta, hWindow, alpha, hInit,
    hODE, hState, hHigh, hFiniteSpeed, hSpeed, hIntegrable⟩

end
end PrimeTensor.FirstMonomialTriad
