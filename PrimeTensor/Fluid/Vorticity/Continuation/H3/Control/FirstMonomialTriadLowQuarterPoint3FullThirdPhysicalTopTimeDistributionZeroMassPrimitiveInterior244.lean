import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionNormalizedBump244
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Compact smooth primitives of zero-mean time tests with interior support bounds

This module constructs an actual smooth primitive of a compactly supported
one-dimensional time test, and proves that if its support is enclosed strictly
inside the time interval and its total integral vanishes, the primitive is
itself an element of the SAME compact-smooth test-function space. No
additional assumptions on the fluid path are introduced.

The remaining topological subproblem is to choose two interior real numbers
which strictly enclose the compact support of an arbitrary time test.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The interval integral of any smooth time test is globally smooth, with
exact classical derivative equal to the original test at every real time. -/
theorem h3Path_smoothTimePrimitive_hasDerivAt_and_contDiff244
    (c : ℝ) {Ω : Opens ℝ} (θ : TestFunction Ω ℝ ⊤) :
    (∀ t : ℝ,
      HasDerivAt (fun x : ℝ => ∫ s in c..x, θ s) (θ t) t) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ∫ s in c..x, θ s) := by
  let P : ℝ → ℝ := fun x => ∫ s in c..x, θ s
  have hθCont : Continuous (fun x : ℝ => θ x) := θ.continuous
  have hDeriv (t : ℝ) : HasDerivAt P (θ t) t :=
    (hθCont.integral_hasStrictDerivAt c t).hasDerivAt
  have hDerivEq : deriv P = (fun t : ℝ => θ t) := by
    funext t
    exact (hDeriv t).deriv
  refine ⟨hDeriv, ?_⟩
  apply (contDiff_infty_iff_deriv).2
  constructor
  · exact fun t => (hDeriv t).differentiableAt
  · rw [hDerivEq]
    exact θ.contDiff

/-- A zero-mass time test supported strictly inside `(ℓ,r)` has a genuine
compact smooth antiderivative on `(a,b)` whenever `a < ℓ < r < b`. The
antiderivative is the original interval integral, not an abstract witness.
-/
theorem h3Path_zeroMassTimeTest_hasCompactPrimitive_of_interiorBounds244
    {a b ℓ r : ℝ}
    (haℓ : a < ℓ) (hℓr : ℓ < r) (hrb : r < b)
    (θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤)
    (hInner : tsupport (fun t : ℝ => θ t) ⊆ Set.Ioo ℓ r)
    (hMass : (∫ t : ℝ, θ t) = 0) :
    ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η := by
  let Ω : Opens ℝ := h3PathStrictTimeOpen244 a b
  let P : ℝ → ℝ := fun t => ∫ s in ℓ..t, θ s
  have hSmooth := h3Path_smoothTimePrimitive_hasDerivAt_and_contDiff244 ℓ θ
  have hDeriv : ∀ t : ℝ, HasDerivAt P (θ t) t := hSmooth.1
  have hPContDiff : ContDiff ℝ (⊤ : ℕ∞) P := hSmooth.2
  have hθCont : Continuous (fun t : ℝ => θ t) := θ.continuous
  have hθZero (s : ℝ) (hs : s ∉ Set.Ioo ℓ r) : θ s = 0 := by
    by_contra hn
    have hSupport : s ∈ Function.support (fun t : ℝ => θ t) := hn
    exact hs (hInner (subset_tsupport _ hSupport))
  have hIntegralZero (x y : ℝ)
      (hZero : ∀ s ∈ Set.uIoo x y, θ s = 0) :
      (∫ s in x..y, θ s) = 0 := by
    have hEq : Set.EqOn (fun s : ℝ => θ s)
        (fun _ : ℝ => (0 : ℝ)) (Set.uIoo x y) := by
      intro s hs
      exact hZero s hs
    calc
      (∫ s in x..y, θ s) = (∫ _s in x..y, (0 : ℝ)) :=
        intervalIntegral.integral_congr_uIoo hEq
      _ = 0 := by simp
  have hLeftZero (t : ℝ) (ht : t ≤ ℓ) : P t = 0 := by
    change (∫ s in ℓ..t, θ s) = 0
    apply hIntegralZero
    intro s hs
    rw [Set.uIoo_of_ge ht] at hs
    apply hθZero s
    intro hsInner
    exact (lt_asymm hs.2 hsInner.1)
  have hRightIntervalZero (t : ℝ) (ht : r ≤ t) :
      (∫ s in r..t, θ s) = 0 := by
    apply hIntegralZero
    intro s hs
    rw [Set.uIoo_of_le ht] at hs
    apply hθZero s
    intro hsInner
    exact (lt_asymm hs.1 hsInner.2)
  have hSuppIoc : Function.support (fun t : ℝ => θ t) ⊆ Set.Ioc ℓ r := by
    intro t ht
    have ht' : t ∈ Set.Ioo ℓ r := hInner (subset_tsupport _ ht)
    exact ⟨ht'.1, ht'.2.le⟩
  have hMassLR : (∫ s in ℓ..r, θ s) = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset hSuppIoc]
    exact hMass
  have hRightZero (t : ℝ) (ht : r ≤ t) : P t = 0 := by
    change (∫ s in ℓ..t, θ s) = 0
    have hℓrInt : IntervalIntegrable (fun s : ℝ => θ s) volume ℓ r :=
      hθCont.intervalIntegrable ℓ r
    have hrtInt : IntervalIntegrable (fun s : ℝ => θ s) volume r t :=
      hθCont.intervalIntegrable r t
    have hAdd := intervalIntegral.integral_add_adjacent_intervals hℓrInt hrtInt
    rw [hMassLR, hRightIntervalZero t ht, add_zero] at hAdd
    exact hAdd.symm
  have hPzero (t : ℝ) (ht : t ∉ Set.Icc ℓ r) : P t = 0 := by
    have hCase : t < ℓ ∨ r < t := by
      by_contra hn
      push Not at hn
      exact ht ⟨hn.1, hn.2⟩
    rcases hCase with hleft | hright
    · exact hLeftZero t hleft.le
    · exact hRightZero t hright.le
  have hPSupport : Function.support P ⊆ Set.Icc ℓ r := by
    intro t ht
    by_contra hn
    exact ht (hPzero t hn)
  have hPTS : tsupport P ⊆ Set.Icc ℓ r :=
    closure_minimal hPSupport isClosed_Icc
  have hPCompact : HasCompactSupport P := by
    change IsCompact (tsupport P)
    exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure hPTS
  have hPTInner : tsupport P ⊆ Set.Ioo a b := by
    intro t ht
    have htt := hPTS ht
    exact ⟨lt_of_lt_of_le haℓ htt.1, lt_of_le_of_lt htt.2 hrb⟩
  let η : TestFunction Ω ℝ ⊤ := ⟨P, hPContDiff, hPCompact, hPTInner⟩
  refine ⟨η, ?_⟩
  apply TestFunction.ext
  intro t
  have hDiff : DifferentiableAt ℝ P t := (hDeriv t).differentiableAt
  have hEq : θ t = deriv P t := (hDeriv t).deriv.symm
  change θ t = (TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η) t
  rw [TestFunction.lineDerivCLM_apply_of_le
    (show (⊤ : ℕ∞) + 1 ≤ ⊤ by simp)]
  -- The bundled test function has underlying function definitionally `P`.
  -- Rewrite the target accordingly before translating the line derivative.
  change θ t = lineDeriv ℝ P t (1 : ℝ)
  simpa only [hDiff.lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv] using hEq

end
end PrimeTensor.FirstMonomialTriad
