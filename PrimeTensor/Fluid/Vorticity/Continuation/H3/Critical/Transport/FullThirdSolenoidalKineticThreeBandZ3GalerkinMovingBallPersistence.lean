import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinZeroSafeMovingWiener
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Zero-safe moving analytic-ball persistence for the genuine finite Z³ Galerkin ODE

The previous module derives M_ε' ≤ (M_ε - 100) D_ε for the real strong
finite-dimensional complex Leray Galerkin ODE, with the smoothed norm
sqrt (‖u_n‖² + ε²). This module closes the scalar comparison via a strict
exponential barrier, then selects ε separately for each finite Fourier set.

A finite set may require a large frequency-dependent bound K on D_ε, but K
occurs only in the *comparison proof*, not in the final moving-radius
100-ball or the time window [a, a + (log(2)-log(9/5))/100].

Strong ODE existence and the initial strict W_log(2) bound are explicit. The
proof neither constructs the flow nor claims global-in-time Navier--Stokes
regularity or infinite Fourier-limit compactness.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Set
open scoped Interval
noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev PersistIndex244 := thirdFullThreeBandZ3Index244
private abbrev PersistBand244 := EuclideanSpace ℂ (Fin 3)

/-- Scalar differential comparison: the right side may have ANY continuous
or merely bounded coefficient D. Its numerical bound C may depend on an
auxiliary finite Fourier cutoff, but the conclusion does not.

The strict exponential barriers 100 + ε exp ((C+1)(t-a)) avoid a circular
first-exit argument at a point with zero derivative. -/
theorem thirdFullThreeBand_z3ScalarMovingBall_comparison244
    (a b : ℝ) (f D : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b))
    (hDBound : ∃ C : ℝ, ∀ t ∈ Icc a b, D t ≤ C)
    (hDerivative : ∀ t ∈ Ico a b,
      ∃ d : ℝ, HasDerivAt f d t ∧ d ≤ (f t - 100) * D t)
    (hInit : f a ≤ 100) :
    ∀ t ∈ Icc a b, f t ≤ 100 := by
  obtain ⟨C, hC⟩ := hDBound
  have hDiff : ∀ t ∈ Ico a b, HasDerivAt f (deriv f t) t := by
    intro t ht
    obtain ⟨d, hd, _⟩ := hDerivative t ht
    simpa only [hd.deriv] using hd
  have hRate : ∀ t ∈ Ico a b,
      deriv f t ≤ (f t - 100) * D t := by
    intro t ht
    obtain ⟨d, hd, hle⟩ := hDerivative t ht
    simpa only [hd.deriv] using hle
  have hBarrier (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      ∀ t ∈ Icc a b,
        f t ≤ 100 + epsilon * Real.exp ((C + 1) * (t - a)) := by
    let B : ℝ → ℝ := fun t => 100 + epsilon * Real.exp ((C + 1) * (t - a))
    let B' : ℝ → ℝ := fun t =>
      epsilon * (Real.exp ((C + 1) * (t - a)) * (C + 1))
    have hBDeriv : ∀ t : ℝ, HasDerivAt B (B' t) t := by
      intro t
      have hLinear :
          HasDerivAt (fun z : ℝ => (C + 1) * (z - a)) (C + 1) t := by
        simpa only [id, mul_one] using
          (((hasDerivAt_id t).sub_const a).const_mul (C + 1))
      have hExp := hLinear.exp
      have h := (hExp.const_mul epsilon).const_add (100 : ℝ)
      simpa only [B, B'] using h
    have hInitB : f a ≤ B a := by
      dsimp only [B]
      simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
      linarith
    have hCross : ∀ t ∈ Ico a b, f t = B t → deriv f t < B' t := by
      intro t ht heq
      have hExpPos : 0 < Real.exp ((C + 1) * (t - a)) := Real.exp_pos _
      have hProductPos : 0 < epsilon * Real.exp ((C + 1) * (t - a)) :=
        mul_pos hepsilon hExpPos
      have hCstrict : D t < C + 1 := by
        have hle := hC t ⟨ht.1, ht.2.le⟩
        linarith
      calc
        deriv f t ≤ (f t - 100) * D t := hRate t ht
        _ = (epsilon * Real.exp ((C + 1) * (t - a))) * D t := by
          rw [heq]
          dsimp only [B]
          ring
        _ < (epsilon * Real.exp ((C + 1) * (t - a))) * (C + 1) :=
          mul_lt_mul_of_pos_left hCstrict hProductPos
        _ = B' t := by dsimp only [B']; ring
    have hBarrierFull : ∀ t ∈ Icc a b, f t ≤ B t :=
      image_le_of_deriv_right_lt_deriv_boundary hf
        (fun t ht => (hDiff t ht).hasDerivWithinAt)
        hInitB hBDeriv hCross
    intro t ht
    exact hBarrierFull t ht
  intro t ht
  apply le_of_forall_pos_le_add
  intro delta hdelta
  let E : ℝ := Real.exp ((C + 1) * (t - a))
  have hE : 0 < E := Real.exp_pos _
  have hEne : E ≠ 0 := ne_of_gt hE
  have h := hBarrier (delta / E) (div_pos hdelta hE) t ht
  have hCancel : (delta / E) * E = delta := by
    field_simp [hEne]
  change f t ≤ 100 + (delta / E) * E at h
  rw [hCancel] at h
  exact h

/-- At a fixed Fourier cutoff a bound K on integer degrees gives a bound
D_ε ≤ K M_ε. This bound is used for existence of a scalar comparison
constant, never as a uniform Galerkin-frequency estimate. -/
theorem thirdFullThreeBand_z3SmoothWienerDerivative_cutoff_bound244
    (epsilon r K : ℝ) (s : Finset PersistIndex244)
    (u : PersistIndex244 → PersistBand244)
    (hDegree : ∀ n ∈ s, thirdFullThreeBandZ3Degree244 n ≤ K) :
    thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon r s u ≤
      K * thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon r s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244
    thirdFullThreeBandZ3GalerkinSmoothWienerMass244
  calc
    _ ≤ ∑ n ∈ s, K *
      (thirdFullThreeBandZ3Weight244 r n *
        thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u n)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hNonneg : 0 ≤ thirdFullThreeBandZ3Weight244 r n *
            thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u n) :=
          mul_nonneg (thirdFullThreeBand_z3Weight_pos244 r n).le
            (Real.sqrt_nonneg _)
        have h := mul_le_mul_of_nonneg_right (hDegree n hn) hNonneg
        calc
          _ = thirdFullThreeBandZ3Degree244 n *
              (thirdFullThreeBandZ3Weight244 r n *
                thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u n)) := by ring
          _ ≤ _ := h
    _ = _ := by rw [Finset.mul_sum]

/-- Continuous strong coefficients give continuity of the finite smoothed
analytic Wiener mass, including frequencies where u_n vanishes. -/
theorem thirdFullThreeBand_z3SmoothMovingMass_continuousOn244
    (a b epsilon : ℝ)
    (s : Finset PersistIndex244)
    (u : ℝ → PersistIndex244 → PersistBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a b)) :
    ContinuousOn (fun t : ℝ =>
      thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t))
      (Icc a b) := by
  classical
  unfold thirdFullThreeBandZ3GalerkinSmoothWienerMass244
  apply continuousOn_finsetSum
  intro n hn
  have hWeight : Continuous
      (fun t : ℝ => thirdFullThreeBandZ3Weight244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) n) := by
    unfold thirdFullThreeBandZ3Weight244
      thirdFullThreeBandZ3GalerkinMovingRadius244
    fun_prop
  have hAmp : ContinuousOn
      (fun t : ℝ => thirdFullThreeBandZ3SmoothAmplitude244 epsilon (u t n))
      (Icc a b) := by
    unfold thirdFullThreeBandZ3SmoothAmplitude244
    exact (((hContinuous n hn).norm.pow 2).add continuousOn_const).sqrt
  exact hWeight.continuousOn.mul hAmp

/-- A finite-degree bound and compact-time continuity automatically give
some scalar bound on D_ε. The auxiliary number may depend on S and ε. -/
theorem thirdFullThreeBand_z3SmoothMovingDerivative_bounded244
    (a b epsilon K : ℝ) (hK : 0 ≤ K)
    (s : Finset PersistIndex244)
    (u : ℝ → PersistIndex244 → PersistBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a b))
    (hDegree : ∀ n ∈ s, thirdFullThreeBandZ3Degree244 n ≤ K) :
    ∃ C : ℝ, ∀ t ∈ Icc a b,
      thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) ≤ C := by
  let f : ℝ → ℝ := fun t =>
    thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
      (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t)
  have hf : ContinuousOn f (Icc a b) :=
    thirdFullThreeBand_z3SmoothMovingMass_continuousOn244
      a b epsilon s u hContinuous
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨K * C, ?_⟩
  intro t ht
  have hD := thirdFullThreeBand_z3SmoothWienerDerivative_cutoff_bound244
    epsilon (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) K s (u t) hDegree
  have hM : f t ≤ ‖f t‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  calc
    _ ≤ K * f t := hD
    _ ≤ K * ‖f t‖ := mul_le_mul_of_nonneg_left hM hK
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hC t ht) hK

/-- Actual strong Galerkin solutions preserve the 100-ball of the SMOOTH
moving Wiener norm throughout the cutoff-independent radius window.
The fixed-cutoff degree K is needed only to run the scalar comparison. -/
theorem thirdFullThreeBand_z3SmoothMovingBall_persists244
    (mu a b epsilon K : ℝ) (hmu : 0 ≤ mu) (hepsilon : 0 < epsilon)
    (hK : 0 ≤ K)
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset PersistIndex244)
    (u : ℝ → PersistIndex244 → PersistBand244)
    (hDegree : ∀ n ∈ s, thirdFullThreeBandZ3Degree244 n ≤ K)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Ico a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hInitial : thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
      (thirdFullThreeBandZ3GalerkinMovingRadius244 a a) s (u a) ≤ 100) :
    ∀ t ∈ Icc a b,
      thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) ≤ 100 := by
  let f : ℝ → ℝ := fun t =>
    thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
      (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t)
  let D : ℝ → ℝ := fun t =>
    thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244 epsilon
      (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t)
  have hf : ContinuousOn f (Icc a b) :=
    thirdFullThreeBand_z3SmoothMovingMass_continuousOn244 a b epsilon s u hContinuous
  have hDBound : ∃ C : ℝ, ∀ t ∈ Icc a b, D t ≤ C :=
    thirdFullThreeBand_z3SmoothMovingDerivative_bounded244
      a b epsilon K hK s u hContinuous hDegree
  have hDerivative : ∀ t ∈ Ico a b,
      ∃ d : ℝ, HasDerivAt f d t ∧ d ≤ (f t - 100) * D t := by
    intro t ht
    have hTime : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 :=
      (sub_le_sub_right ht.2.le a).trans hWindow
    have hRadius : 0 ≤ thirdFullThreeBandZ3GalerkinMovingRadius244 a t :=
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9 / 5)).trans
        (thirdFullThreeBand_z3MovingRadius_lower244 a t hTime)
    obtain ⟨d, hd, hle⟩ :=
      thirdFullThreeBand_z3ZeroSafeMovingWiener_differential244
        mu a t epsilon hmu hepsilon s u hRadius
          (fun n hn => hODE n hn t ht)
    exact ⟨d, hd, hle⟩
  exact thirdFullThreeBand_z3ScalarMovingBall_comparison244
    a b f D hf hDBound hDerivative hInitial

/-- If the initial true W_log(2) mass is strictly below 100, the finite
regularization error can be paid by choosing epsilon separately for S.
The conclusion has no frequency cutoff or cardinality dependence. -/
theorem thirdFullThreeBand_z3MovingBall_persists_of_strict_initial244
    (mu a b K : ℝ) (hmu : 0 ≤ mu) (hK : 0 ≤ K)
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset PersistIndex244)
    (u : ℝ → PersistIndex244 → PersistBand244)
    (hDegree : ∀ n ∈ s, thirdFullThreeBandZ3Degree244 n ≤ K)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Ico a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s (u a) < 100) :
    ∀ t ∈ Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) ≤ 100 := by
  let W : ℝ := thirdFullThreeBandZ3GalerkinWienerMass244
    (Real.log (2 : ℝ)) s (u a)
  let E : ℝ := ∑ n ∈ s, thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply Finset.sum_nonneg
    intro n hn
    exact (thirdFullThreeBand_z3Weight_pos244 _ n).le
  let epsilon : ℝ := (100 - W) / (2 * (E + 1))
  have hDenom : 0 < 2 * (E + 1) := by positivity
  have hPos : 0 < epsilon := by
    dsimp only [epsilon]
    apply div_pos
    · have hW : W < 100 := hInitial
      linarith
    · exact hDenom
  have hBudget : epsilon * E ≤ 100 - W := by
    have hEDenom : E ≤ E + 1 := by linarith
    have hScaled := mul_le_mul_of_nonneg_left hEDenom hPos.le
    have hExact : epsilon * (2 * (E + 1)) = 100 - W := by
      dsimp only [epsilon]
      field_simp [ne_of_gt hDenom]
    nlinarith
  have hRadiusAtA : thirdFullThreeBandZ3GalerkinMovingRadius244 a a =
      Real.log (2 : ℝ) := by
    unfold thirdFullThreeBandZ3GalerkinMovingRadius244
    ring
  have hSmoothInit :
      thirdFullThreeBandZ3GalerkinSmoothWienerMass244 epsilon
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a a) s (u a) ≤ 100 := by
    rw [hRadiusAtA]
    have hSmooth := thirdFullThreeBand_z3SmoothWienerMass_le_true_add_error244
      epsilon (Real.log (2 : ℝ)) hPos.le s (u a)
    dsimp only [W, E] at hBudget
    linarith
  have hPersist := thirdFullThreeBand_z3SmoothMovingBall_persists244
    mu a b epsilon K hmu hPos hK hWindow s u
    hDegree hContinuous hODE hSmoothInit
  intro t ht
  exact (thirdFullThreeBand_z3WienerMass_le_smooth244 epsilon
    (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t)).trans
      (hPersist t ht)


/-- A finite Galerkin cutoff automatically has some finite l¹-degree cap.
This number may depend on the cutoff; the persistence lifespan does not. -/
theorem thirdFullThreeBand_z3FiniteGalerkin_degreeCap_exists244
    (s : Finset PersistIndex244) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ n ∈ s, thirdFullThreeBandZ3Degree244 n ≤ K := by
  classical
  refine ⟨∑ n ∈ s, thirdFullThreeBandZ3Degree244 n, ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro n hn
    exact thirdFullThreeBand_z3Degree_nonneg244 n
  · intro n hn
    exact Finset.single_le_sum
      (fun j hj => thirdFullThreeBand_z3Degree_nonneg244 j) hn

/-- Full cutoff-independent analytic-ball persistence from a STRICT initial
analytic 2-radius ball and the genuine strong Galerkin ODE. No frequency
cap K occurs anywhere in the theorem statement. The common radius window
is exactly the pre-existing log(2)-to-log(9/5) window. -/
theorem thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244
    (mu a b : ℝ) (hmu : 0 ≤ mu)
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset PersistIndex244)
    (u : ℝ → PersistIndex244 → PersistBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Ico a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s (u a) < 100) :
    ∀ t ∈ Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (thirdFullThreeBandZ3GalerkinMovingRadius244 a t) s (u t) ≤ 100 := by
  obtain ⟨K, hK, hDegree⟩ :=
    thirdFullThreeBand_z3FiniteGalerkin_degreeCap_exists244 s
  exact thirdFullThreeBand_z3MovingBall_persists_of_strict_initial244
    mu a b K hmu hK hWindow s u hDegree hContinuous hODE hInitial


/-- The actual Galerkin strong ODE now supplies the uniform higher-radius
9/5 Wiener ball, not an assumed analytic-ball certificate. -/
theorem thirdFullThreeBand_z3MovingBall_cutoffFreeHighRadius244
    (mu a b : ℝ) (hmu : 0 ≤ mu)
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset PersistIndex244)
    (u : ℝ → PersistIndex244 → PersistBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Ico a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s (u a) < 100) :
    ∀ t ∈ Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100 := by
  have hPersistence := thirdFullThreeBand_z3MovingBall_cutoffFreePersistence244
    mu a b hmu hWindow s u hContinuous hODE hInitial
  intro t ht
  have hTime : t - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244 :=
    (sub_le_sub_right ht.2 a).trans hWindow
  exact (thirdFullThreeBand_z3WienerMass_radius_mono244 _ _
    (thirdFullThreeBand_z3MovingRadius_lower244 a t hTime) s (u t)).trans
      (hPersistence t ht)

/-- The quadratic 25,750,000 h² consistency theorem now follows from a
strict INITIAL analytic 2-ball and the genuine strong Galerkin ODE, without
a postulated moving analytic 100-ball or a cutoff-dependent lifespan.
The two coefficientwise integrability assumptions remain explicit until
finite-dimensional flow construction/automatic time regularity is attached. -/
theorem thirdFullThreeBand_z3MovingBall_cutoffFreeODEResidual244
    (mu a b : ℝ) (hab : a ≤ b) (hmu : 0 ≤ mu)
    (hmuMax : mu ≤ (1 / 10 : ℝ))
    (hWindow : b - a ≤ thirdFullThreeBandZ3GalerkinMovingRadiusWindow244)
    (s : Finset PersistIndex244)
    (u : ℝ → PersistIndex244 → PersistBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Ico a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hFieldInt : ∀ t ∈ Icc a b, ∀ n ∈ s,
      IntervalIntegrable
        (fun z : ℝ => thirdFullThreeBandZ3GalerkinNSField244 mu s (u z) n)
        volume a t)
    (hRetardedInt : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume a b)
    (hInitial : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s (u a) < 100) :
    thirdFullThreeBandZ3GalerkinStepResidual244 mu (b - a)
        (Real.log (5 / 4 : ℝ)) s (u a) (u b) ≤
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * (b - a) ^ 2 := by
  have hHigh := thirdFullThreeBand_z3MovingBall_cutoffFreeHighRadius244
    mu a b hmu hWindow s u hContinuous hODE hInitial
  have hODE' : ∀ n ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t := by
    intro n hn t ht
    exact hODE n hn t ⟨ht.1.le, ht.2⟩
  exact thirdFullThreeBand_z3GalerkinStrongODE_fullResidual25750000_100Ball244
    mu a b hab hmu hmuMax s u hContinuous hODE' hFieldInt
      hRetardedInt hHigh

end
end PrimeTensor.FirstMonomialTriad
