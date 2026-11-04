import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRegularizedHermitianTransverseRecovery
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Strong weighted H³ convergence of the smooth origin regularizer

The previous module constructs real solenoidal Schwartz velocity fields with
exact Fourier amplitude χ(ξ) |ξ|²/(|ξ|²+δ) U(ξ). This module proves the
analytically missing convergence of the radial factor, in the genuine
H³ weighted spectral L² carrier, for arbitrary L² states.

The essential obstruction is frequency zero. It has exactly zero Fourier
volume, whereas for each nonzero frequency the regularizer approaches one.
Uniform domination by the original L² datum and dominated convergence give
strong rather than merely pointwise convergence. The result is extended to
all three finite Fourier components with their actual product-space norm.

No theorem here identifies an arbitrary weighted L² element with a smooth
Schwartz profile: that is the next construction using the compact Hermitian
density theorem and the actual real-solenoidal Schwartz realization.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology Set PrimeTensor.Bridge.Euclidean
open scoped ENNReal NNReal BigOperators

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeRegularizedStrong244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceRegularizedStrong244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Positive vanishing regularization scale, with no free assumptions. -/
def h3FullThirdRegularizationScale244 (n : ℕ) : ℝ :=
  (1 : ℝ) / ((n : ℝ) + 1)

@[simp] theorem h3FullThirdRegularizationScale_pos244 (n : ℕ) :
    0 < h3FullThirdRegularizationScale244 n := by
  unfold h3FullThirdRegularizationScale244
  positivity

/-- The chosen scales tend to zero. -/
theorem h3FullThirdRegularizationScale_tendsto_zero244 :
    Tendsto h3FullThirdRegularizationScale244 atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The exact smooth radial multiplier in the Euclidean Fourier realization. -/
noncomputable def h3FullThirdRadialRecoveryFactor244
    (n : ℕ) (ξ : V3) : ℝ :=
  ‖ξ‖ ^ 2 / (‖ξ‖ ^ 2 + h3FullThirdRegularizationScale244 n)

/-- The radial multiplier has uniform bounds independent of n and ξ. -/
theorem h3FullThirdRadialRecoveryFactor_bounds244
    (n : ℕ) (ξ : V3) :
    0 ≤ h3FullThirdRadialRecoveryFactor244 n ξ ∧
      h3FullThirdRadialRecoveryFactor244 n ξ ≤ 1 := by
  have hq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
  have hd : 0 < ‖ξ‖ ^ 2 + h3FullThirdRegularizationScale244 n :=
    add_pos_of_nonneg_of_pos hq (h3FullThirdRegularizationScale_pos244 n)
  constructor
  · exact div_nonneg hq hd.le
  · apply (div_le_iff₀ hd).2
    linarith [h3FullThirdRegularizationScale_pos244 n]

/-- Every fixed regularized multiplier is continuous. -/
theorem h3FullThirdRadialRecoveryFactor_continuous244 (n : ℕ) :
    Continuous (h3FullThirdRadialRecoveryFactor244 n) := by
  have hq : Continuous (fun ξ : V3 => ‖ξ‖ ^ 2) :=
    continuous_norm.pow 2
  unfold h3FullThirdRadialRecoveryFactor244
  apply hq.div (hq.add continuous_const)
  intro ξ
  have hq0 : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
  exact ne_of_gt (add_pos_of_nonneg_of_pos hq0
    (h3FullThirdRegularizationScale_pos244 n))

/-- At each NONZERO Fourier frequency the regularizer converges to one. -/
theorem h3FullThirdRadialRecoveryFactor_tendsto_one244
    (ξ : V3) (hξ : ξ ≠ 0) :
    Tendsto (fun n : ℕ => h3FullThirdRadialRecoveryFactor244 n ξ)
      atTop (𝓝 1) := by
  have hq : ‖ξ‖ ^ 2 ≠ 0 :=
    ne_of_gt (pow_pos (norm_pos_iff.mpr hξ) 2)
  have hden : Tendsto
      (fun n : ℕ => ‖ξ‖ ^ 2 + h3FullThirdRegularizationScale244 n)
      atTop (𝓝 (‖ξ‖ ^ 2)) := by
    convert (tendsto_const_nhds.add
      h3FullThirdRegularizationScale_tendsto_zero244) using 1 <;> simp
  have hnum : Tendsto (fun _ : ℕ => ‖ξ‖ ^ 2)
      atTop (𝓝 (‖ξ‖ ^ 2)) := tendsto_const_nhds
  have hdiv : Tendsto
      (fun n : ℕ => ‖ξ‖ ^ 2 /
        (‖ξ‖ ^ 2 + h3FullThirdRegularizationScale244 n))
      atTop (𝓝 (‖ξ‖ ^ 2 / ‖ξ‖ ^ 2)) :=
    hnum.div hden hq
  simpa only [h3FullThirdRadialRecoveryFactor244, div_self hq] using hdiv

/-- The one excluded frequency has zero Euclidean Fourier volume. -/
theorem h3FullThirdFourier_ae_nonzero244 :
    ∀ᵐ ξ : V3 ∂volume, ξ ≠ 0 := by
  have hHyperplane :
      (volume : Measure Point3) {x : Point3 | x xAxis = 0} = 0 := by
    change Measure.pi (fun _ : A3 => (volume : Measure ℝ))
      {x : Point3 | x xAxis = 0} = 0
    exact Measure.pi_hyperplane
      (fun _ : A3 => (volume : Measure ℝ)) xAxis 0
  have hFourierHyperplane :
      (volume : Measure V3)
        ((WithLp.ofLp : V3 → Point3) ⁻¹'
          {x : Point3 | x xAxis = 0}) = 0 := by
    exact (PiLp.volume_preserving_ofLp A3).preimage_null hHyperplane
  have hZero : (volume : Measure V3) ({0} : Set V3) = 0 := by
    refine measure_mono_null ?_ hFourierHyperplane
    intro ξ hξ
    simp only [Set.mem_singleton_iff] at hξ
    subst ξ
    simp
  rw [ae_iff]
  simpa using hZero

/-- The regularizer acts on the actual spectral L² representative. -/
def h3FullThirdRadialRecoveryRaw244
    (n : ℕ) (F : H3SpectralScalarState) (ξ : V3) : ℂ :=
  (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * F ξ

/-- The radial multiplier is a contraction in the actual weighted L² norm. -/
theorem h3FullThirdRadialRecoveryRaw_memLp244
    (n : ℕ) (F : H3SpectralScalarState) :
    MemLp (h3FullThirdRadialRecoveryRaw244 n F) 2 volume := by
  refine (MeasureTheory.Lp.memLp F).of_le_mul (c := 1) ?_ ?_
  · unfold h3FullThirdRadialRecoveryRaw244
    exact (Complex.continuous_ofReal.measurable.comp
      (h3FullThirdRadialRecoveryFactor_continuous244 n).measurable).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable F)
  · filter_upwards with ξ
    have hbound := (h3FullThirdRadialRecoveryFactor_bounds244 n ξ).2
    have hnonneg := (h3FullThirdRadialRecoveryFactor_bounds244 n ξ).1
    dsimp only [h3FullThirdRadialRecoveryRaw244]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnonneg, one_mul]
    calc
      h3FullThirdRadialRecoveryFactor244 n ξ * ‖F ξ‖ ≤
          1 * ‖F ξ‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
      _ = ‖F ξ‖ := one_mul _

/-- The genuine bundled L² spectral regularization. -/
noncomputable def h3FullThirdRadialRecoveryL2244
    (n : ℕ) (F : H3SpectralScalarState) : H3SpectralScalarState :=
  (h3FullThirdRadialRecoveryRaw_memLp244 n F).toLp
    (h3FullThirdRadialRecoveryRaw244 n F)

/-- The pointwise error is dominated by the unchanged L² input. -/
theorem h3FullThirdRadialRecoveryRaw_error_le244
    (n : ℕ) (F : H3SpectralScalarState) (ξ : V3) :
    ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ≤ ‖F ξ‖ := by
  have h0 := (h3FullThirdRadialRecoveryFactor_bounds244 n ξ).1
  have h1 := (h3FullThirdRadialRecoveryFactor_bounds244 n ξ).2
  have habs : |h3FullThirdRadialRecoveryFactor244 n ξ - 1| ≤ 1 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  unfold h3FullThirdRadialRecoveryRaw244
  rw [show (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * F ξ - F ξ =
      ((h3FullThirdRadialRecoveryFactor244 n ξ - 1 : ℝ) : ℂ) * F ξ by
        push_cast; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |h3FullThirdRadialRecoveryFactor244 n ξ - 1| * ‖F ξ‖ ≤
        1 * ‖F ξ‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
    _ = ‖F ξ‖ := one_mul _

/-- Pointwise complex error tends to zero off the null origin. -/
theorem h3FullThirdRadialRecoveryRaw_error_tendsto_zero244
    (F : H3SpectralScalarState) (ξ : V3) (hξ : ξ ≠ 0) :
    Tendsto (fun n : ℕ => h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ)
      atTop (𝓝 0) := by
  have hReal := h3FullThirdRadialRecoveryFactor_tendsto_one244 ξ hξ
  have hCast : Tendsto
      (fun n : ℕ => (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ))
      atTop (𝓝 (1 : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hReal
  have hProduct : Tendsto
      (fun n : ℕ => (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * F ξ)
      atTop (𝓝 ((1 : ℂ) * F ξ)) :=
    hCast.mul tendsto_const_nhds
  have hError : Tendsto
      (fun n : ℕ =>
        (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * F ξ - F ξ)
      atTop (𝓝 ((1 : ℂ) * F ξ - F ξ)) :=
    hProduct.sub tendsto_const_nhds
  simpa only [h3FullThirdRadialRecoveryRaw244, one_mul, sub_self] using hError

/-- The squared raw Fourier error is almost everywhere strongly measurable. -/
theorem h3FullThirdRadialRecoveryRaw_errorSq_aestronglyMeasurable244
    (n : ℕ) (F : H3SpectralScalarState) :
    AEStronglyMeasurable
      (fun ξ : V3 => ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ^ 2)
      volume := by
  have hScalar : AEStronglyMeasurable
      (fun ξ : V3 => (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ))
      volume :=
    (Complex.continuous_ofReal.comp
      (h3FullThirdRadialRecoveryFactor_continuous244 n)).aestronglyMeasurable
  have hError : AEStronglyMeasurable
      (fun ξ : V3 => h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ)
      volume := by
    exact (hScalar.mul (MeasureTheory.Lp.aestronglyMeasurable F)).sub
      (MeasureTheory.Lp.aestronglyMeasurable F)
  exact (hError.norm.aemeasurable.pow_const 2).aestronglyMeasurable

/-- The squared error has the genuine input L² density as its majorant. -/
theorem h3FullThirdRadialRecoveryRaw_errorSq_le244
    (n : ℕ) (F : H3SpectralScalarState) (ξ : V3) :
    ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ^ 2 ≤
      ‖F ξ‖ ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (h3FullThirdRadialRecoveryRaw_error_le244 n F ξ) 2

/-- Actual L² norm-square equals the Lebesgue square error integral. -/
theorem h3FullThirdRadialRecoveryL2_sub_norm_sq244
    (n : ℕ) (F : H3SpectralScalarState) :
    ‖h3FullThirdRadialRecoveryL2244 n F - F‖ ^ 2 =
      ∫ ξ : V3, ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ^ 2 := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub (h3FullThirdRadialRecoveryL2244 n F) F,
    MeasureTheory.MemLp.coeFn_toLp
      (h3FullThirdRadialRecoveryRaw_memLp244 n F)
  ] with ξ hSub hRep
  rw [hSub]
  simp only [Pi.sub_apply]
  have hRep' :
      (h3FullThirdRadialRecoveryL2244 n F : V3 → ℂ) ξ =
        h3FullThirdRadialRecoveryRaw244 n F ξ := hRep
  rw [hRep']

/-- Dominated convergence proves vanishing of the actual Fourier L²
norm-square error, not merely pointwise multiplier convergence. -/
theorem h3FullThirdRadialRecoveryL2_norm_sq_tendsto_zero244
    (F : H3SpectralScalarState) :
    Tendsto
      (fun n : ℕ => ‖h3FullThirdRadialRecoveryL2244 n F - F‖ ^ 2)
      atTop (𝓝 0) := by
  have hMajorant : Integrable (fun ξ : V3 => ‖F ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp F).integrable_norm_pow (by norm_num)
  have hLimit : ∀ᵐ ξ : V3 ∂volume,
      Tendsto
        (fun n : ℕ =>
          ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [h3FullThirdFourier_ae_nonzero244] with ξ hξ
    have hError := h3FullThirdRadialRecoveryRaw_error_tendsto_zero244
      F ξ hξ
    have hNorm := ((continuous_norm.pow 2).tendsto (0 : ℂ)).comp hError
    simpa [Function.comp_def] using hNorm
  have hIntegral : Tendsto
      (fun n : ℕ => ∫ ξ : V3,
        ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := atTop)
        (F := fun n : ℕ => fun ξ : V3 =>
          ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ^ 2)
        (f := fun _ : V3 => (0 : ℝ))
        (bound := fun ξ : V3 => ‖F ξ‖ ^ 2)
        (Eventually.of_forall fun n =>
          h3FullThirdRadialRecoveryRaw_errorSq_aestronglyMeasurable244 n F)
        (Eventually.of_forall fun n =>
          Eventually.of_forall fun ξ => by
            have h := h3FullThirdRadialRecoveryRaw_errorSq_le244 n F ξ
            have hLeft :
                0 ≤ ‖h3FullThirdRadialRecoveryRaw244 n F ξ - F ξ‖ ^ 2 :=
              sq_nonneg _
            simpa only [Real.norm_eq_abs,
              abs_of_nonneg hLeft] using h)
        hMajorant hLimit)
  simpa only [h3FullThirdRadialRecoveryL2_sub_norm_sq244] using hIntegral

/-- Strong convergence of the genuine weighted-H³ scalar spectral state.
The origin requires no value choice: it is a Fourier-volume null singleton. -/
theorem h3FullThirdRadialRecoveryL2_tendsto244
    (F : H3SpectralScalarState) :
    Tendsto (fun n : ℕ => h3FullThirdRadialRecoveryL2244 n F)
      atTop (𝓝 F) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hSq := h3FullThirdRadialRecoveryL2_norm_sq_tendsto_zero244 F
  have hSqrt := (Real.continuous_sqrt.tendsto 0).comp hSq
  change Tendsto (fun n : ℕ =>
    Real.sqrt (‖h3FullThirdRadialRecoveryL2244 n F - F‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) at hSqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hSqrt

/-- The genuine three-component weighted-H³ regularizer uses the exact finite
sup-norm carrier, not a single scalar surrogate. -/
noncomputable def h3FullThirdRadialRecoveryVelocity244
    (n : ℕ) (U : H3SpectralVelocityState) : H3SpectralVelocityState :=
  fun j => h3FullThirdRadialRecoveryL2244 n (U j)

/-- Strong convergence of all three weighted Fourier velocity components. -/
theorem h3FullThirdRadialRecoveryVelocity_tendsto244
    (U : H3SpectralVelocityState) :
    Tendsto (fun n : ℕ => h3FullThirdRadialRecoveryVelocity244 n U)
      atTop (𝓝 U) := by
  rw [tendsto_pi_nhds]
  intro j
  exact h3FullThirdRadialRecoveryL2_tendsto244 (U j)

/-- The regularized velocity sequence is also Cauchy in the actual H³ norm. -/
theorem h3FullThirdRadialRecoveryVelocity_cauchy244
    (U : H3SpectralVelocityState) :
    CauchySeq (fun n : ℕ => h3FullThirdRadialRecoveryVelocity244 n U) :=
  (h3FullThirdRadialRecoveryVelocity_tendsto244 U).cauchySeq

/-- The Euclidean-norm radius used in strong convergence is exactly the
axis-coordinate radial square in the previously proved Fourier recovery. -/
theorem h3FullThirdRadialRecoveryFactor_eq_axis244
    (n : ℕ) (ξ : V3) :
    h3FullThirdRadialRecoveryFactor244 n ξ =
      thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) /
        (thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) +
          h3FullThirdRegularizationScale244 n) := by
  have hSq :
      thirdTriadAxisDot244 (WithLp.ofLp ξ) (WithLp.ofLp ξ) =
        ‖ξ‖ ^ 2 := by
    simpa only [thirdTriadAxisDot244, pow_two] using
      (h3FourierPoint3_norm_sq_eq_sum_coordinates ξ).symm
  simp only [h3FullThirdRadialRecoveryFactor244, hSq]

end
end PrimeTensor.FirstMonomialTriad
