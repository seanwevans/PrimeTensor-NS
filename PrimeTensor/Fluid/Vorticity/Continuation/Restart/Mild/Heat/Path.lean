import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Fourier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.PathSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong continuity and the normalized free H³ jet path

`Heat.Fourier` constructs the genuine Fourier heat evolution and proves its
`L²` contraction estimates.  This file supplies the time-topology statement
needed by the mild fixed-point layer.

The crucial analytic point is strong continuity for each fixed `L²` datum.
We do **not** claim operator-norm continuity at time zero.  Instead, on the
Fourier side we apply dominated convergence to

    |(m_t(ξ) - m_t₀(ξ)) f(ξ)|²,

where `m_t(ξ) = exp (-4 π² ν t |ξ|²)`.  For nonnegative times both symbols
have modulus at most one, so the integrand is dominated by `|(2 : ℂ) f|²`,
which is integrable because `f ∈ L²`.

The result is then transported through inverse Fourier transform, real
projection, the Euclidean/project spatial carrier equivalence, and finally the
finite 120-coordinate H³ jet.

For a physical lifespan `τ ≥ 0` we obtain the normalized free path

    s ↦ exp (ν τ s Δ) J₀,    s ∈ [0,1],

as an actual `H3L2JetPath`, with uniform norm bounded by `‖J₀‖`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Set Filter
open scoped ENNReal NNReal InnerProductSpace Topology

noncomputable section

noncomputable local instance axisFintypeH3HeatPath
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3HeatPath :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## An `L²` norm-square formula used by dominated convergence -/

/--
For complex `L²` on the Euclidean Fourier carrier, the square of the `Lp` norm
is the integral of the pointwise squared norm.
-/
theorem h3FourierComplexL2_norm_sq_eq_integral_norm_sq
    (f : H3FourierComplexL2) :
    ‖f‖ ^ 2 = ∫ ξ : H3FourierPoint3, ‖f ξ‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = Complex.re ⟪f, f⟫_ℂ :=
      norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = Complex.re
        (∫ ξ : H3FourierPoint3, ⟪f ξ, f ξ⟫_ℂ) := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∫ ξ : H3FourierPoint3, Complex.re ⟪f ξ, f ξ⟫_ℂ := by
      symm
      exact
        Complex.reCLM.integral_comp_comm
          (MeasureTheory.L2.integrable_inner f f)
    _ = ∫ ξ : H3FourierPoint3, ‖f ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [inner_self_eq_norm_sq_to_K]
      norm_cast

/-! ## Nonnegative-time wrappers -/

/--
Frequency-space heat evolution with time packaged as a nonnegative real.
The proof argument in `h3HeatFrequencyApply` is thereby hidden from the
topological interface.
-/
def h3HeatFrequencyApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (f : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  h3HeatFrequencyApply ν (t : ℝ) hν t.property f

/-- Complex physical-space heat evolution at nonnegative time. -/
def h3ComplexHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (f : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  h3ComplexHeatApply ν (t : ℝ) hν t.property f

/-- Real project-carrier scalar heat evolution at nonnegative time. -/
def h3ScalarHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (f : H3ScalarL2) :
    H3ScalarL2 :=
  h3ScalarHeatApply ν (t : ℝ) hν t.property f

/-- Concrete H³ jet heat evolution at nonnegative time. -/
def h3L2JetHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (J : H3L2JetState) :
    H3L2JetState :=
  h3L2JetHeatApply ν (t : ℝ) hν t.property J

@[simp]
theorem h3L2JetHeatApplyNN_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (J : H3L2JetState)
    (a : H3JetIndex) :
    h3L2JetHeatApplyNN ν hν t J a =
      h3ScalarHeatApplyNN ν hν t (J a) :=
  rfl

/-- The nonnegative-time scalar heat wrapper remains contractive. -/
theorem norm_h3ScalarHeatApplyNN_le
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (f : H3ScalarL2) :
    ‖h3ScalarHeatApplyNN ν hν t f‖ ≤ ‖f‖ := by
  exact norm_h3ScalarHeatApply_le hν t.property f

/-- The nonnegative-time jet heat wrapper remains contractive. -/
theorem norm_h3L2JetHeatApplyNN_le
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (J : H3L2JetState) :
    ‖h3L2JetHeatApplyNN ν hν t J‖ ≤ ‖J‖ := by
  exact norm_h3L2JetHeatApply_le hν t.property J

/-! ## Fourier-side strong continuity -/

/-- Pointwise Fourier difference used in the dominated-convergence proof. -/
def h3HeatFrequencyDifference
    (ν : ℝ)
    (t t₀ : ℝ≥0)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3HeatFourierSymbol ν (t : ℝ) ξ -
      h3HeatFourierSymbol ν (t₀ : ℝ) ξ) * f ξ

/-- The squared pointwise Fourier difference. -/
def h3HeatFrequencyDifferenceSq
    (ν : ℝ)
    (t t₀ : ℝ≥0)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) : ℝ :=
  ‖h3HeatFrequencyDifference ν t t₀ f ξ‖ ^ 2

/-- The squared Fourier difference is a.e. strongly measurable for every time. -/
theorem h3HeatFrequencyDifferenceSq_aestronglyMeasurable
    (ν : ℝ)
    (t t₀ : ℝ≥0)
    (f : H3FourierComplexL2) :
    AEStronglyMeasurable
      (h3HeatFrequencyDifferenceSq ν t t₀ f)
      volume := by
  have hdiff :
      AEStronglyMeasurable
        (h3HeatFrequencyDifference ν t t₀ f)
        volume := by
    unfold h3HeatFrequencyDifference
    exact
      ((continuous_h3HeatFourierSymbol ν (t : ℝ)).sub
          (continuous_h3HeatFourierSymbol ν (t₀ : ℝ))).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable f)
  unfold h3HeatFrequencyDifferenceSq
  exact
    (hdiff.norm.aemeasurable.pow_const 2).aestronglyMeasurable

/--
The Fourier difference is dominated by `2 f`, uniformly in nonnegative time.
-/
theorem h3HeatFrequencyDifference_norm_le_two_mul
    {ν : ℝ}
    (hν : 0 ≤ ν)
    (t t₀ : ℝ≥0)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFrequencyDifference ν t t₀ f ξ‖
      ≤ ‖(2 : ℂ) * f ξ‖ := by
  have hsym :
      ‖h3HeatFourierSymbol ν (t : ℝ) ξ -
          h3HeatFourierSymbol ν (t₀ : ℝ) ξ‖ ≤ 2 := by
    calc
      ‖h3HeatFourierSymbol ν (t : ℝ) ξ -
          h3HeatFourierSymbol ν (t₀ : ℝ) ξ‖
          ≤ ‖h3HeatFourierSymbol ν (t : ℝ) ξ‖ +
              ‖h3HeatFourierSymbol ν (t₀ : ℝ) ξ‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 :=
        add_le_add
          (norm_h3HeatFourierSymbol_le_one hν t.property ξ)
          (norm_h3HeatFourierSymbol_le_one hν t₀.property ξ)
      _ = 2 := by norm_num
  unfold h3HeatFrequencyDifference
  rw [norm_mul, norm_mul]
  have hf0 : 0 ≤ ‖f ξ‖ := norm_nonneg _
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo]
  exact mul_le_mul_of_nonneg_right hsym hf0

/-- Uniform square domination required by dominated convergence. -/
theorem h3HeatFrequencyDifferenceSq_le_bound
    {ν : ℝ}
    (hν : 0 ≤ ν)
    (t t₀ : ℝ≥0)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) :
    h3HeatFrequencyDifferenceSq ν t t₀ f ξ
      ≤ ‖(2 : ℂ) * f ξ‖ ^ 2 := by
  unfold h3HeatFrequencyDifferenceSq
  have h :=
    h3HeatFrequencyDifference_norm_le_two_mul hν t t₀ f ξ
  have hleft :
      0 ≤ ‖h3HeatFrequencyDifference ν t t₀ f ξ‖ :=
    norm_nonneg _
  have hright : 0 ≤ ‖(2 : ℂ) * f ξ‖ := norm_nonneg _
  nlinarith

/-- The DCT dominating square is integrable because `f ∈ L²`. -/
theorem h3HeatFrequency_bound_integrable
    (f : H3FourierComplexL2) :
    Integrable
      (fun ξ : H3FourierPoint3 => ‖(2 : ℂ) * f ξ‖ ^ 2)
      volume := by
  have hmem :
      MemLp
        (fun ξ : H3FourierPoint3 => (2 : ℂ) * f ξ)
        2 volume :=
    (MeasureTheory.Lp.memLp f).const_mul (2 : ℂ)
  exact hmem.integrable_norm_pow (by norm_num)

/-- For each frequency, the squared difference tends to zero as time tends to `t₀`. -/
theorem tendsto_h3HeatFrequencyDifferenceSq
    (ν : ℝ)
    (t₀ : ℝ≥0)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun t : ℝ≥0 => h3HeatFrequencyDifferenceSq ν t t₀ f ξ)
      (𝓝 t₀)
      (𝓝 0) := by
  have hcont :
      Continuous
        (fun t : ℝ≥0 =>
          h3HeatFrequencyDifferenceSq ν t t₀ f ξ) := by
    unfold h3HeatFrequencyDifferenceSq h3HeatFrequencyDifference
    unfold h3HeatFourierSymbol
    fun_prop
  have hzero :
      h3HeatFrequencyDifferenceSq ν t₀ t₀ f ξ = 0 := by
    unfold h3HeatFrequencyDifferenceSq h3HeatFrequencyDifference
    rw [sub_self, zero_mul, norm_zero]
    norm_num
  have htend :
      Tendsto
        (fun t : ℝ≥0 => h3HeatFrequencyDifferenceSq ν t t₀ f ξ)
        (𝓝 t₀)
        (𝓝 (h3HeatFrequencyDifferenceSq ν t₀ t₀ f ξ)) :=
    hcont.continuousAt (x := t₀)
  rw [hzero] at htend
  exact htend

/-- A.e. pointwise formula for the nonnegative-time frequency heat wrapper. -/
theorem h3HeatFrequencyApplyNN_coeFn
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (f : H3FourierComplexL2) :
    ∀ᵐ ξ : H3FourierPoint3 ∂volume,
      h3HeatFrequencyApplyNN ν hν t f ξ =
        h3HeatFourierSymbol ν (t : ℝ) ξ * f ξ := by
  unfold h3HeatFrequencyApplyNN h3HeatFrequencyApply
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3HeatFrequency_memLp hν t.property f)

/--
The squared `L²` norm of the frequency-space heat difference is exactly the
integral used in the dominated-convergence proof.
-/
theorem h3HeatFrequencyApplyNN_sub_norm_sq
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t t₀ : ℝ≥0)
    (f : H3FourierComplexL2) :
    ‖h3HeatFrequencyApplyNN ν hν t f -
        h3HeatFrequencyApplyNN ν hν t₀ f‖ ^ 2
      =
      ∫ ξ : H3FourierPoint3,
        h3HeatFrequencyDifferenceSq ν t t₀ f ξ := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (h3HeatFrequencyApplyNN ν hν t f)
      (h3HeatFrequencyApplyNN ν hν t₀ f),
    h3HeatFrequencyApplyNN_coeFn ν hν t f,
    h3HeatFrequencyApplyNN_coeFn ν hν t₀ f
  ] with ξ hsub ht ht₀
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [ht, ht₀]
  unfold h3HeatFrequencyDifferenceSq h3HeatFrequencyDifference
  congr 2
  ring

/--
Strong continuity of the Fourier multiplier on complex `L²`, for each fixed
datum and nonnegative viscosity.
-/
theorem continuous_h3HeatFrequencyApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (f : H3FourierComplexL2) :
    Continuous (fun t : ℝ≥0 => h3HeatFrequencyApplyNN ν hν t f) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hIntegral :
      Tendsto
        (fun t : ℝ≥0 =>
          ∫ ξ : H3FourierPoint3,
            h3HeatFrequencyDifferenceSq ν t t₀ f ξ)
        (𝓝 t₀)
        (𝓝 0) := by
    simpa using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 t₀)
        (F := fun t : ℝ≥0 =>
          h3HeatFrequencyDifferenceSq ν t t₀ f)
        (f := fun _ : H3FourierPoint3 => (0 : ℝ))
        (bound := fun ξ : H3FourierPoint3 => ‖(2 : ℂ) * f ξ‖ ^ 2)
        (Eventually.of_forall fun t =>
          h3HeatFrequencyDifferenceSq_aestronglyMeasurable ν t t₀ f)
        (Eventually.of_forall fun t =>
          Eventually.of_forall fun ξ => by
            have h :=
              h3HeatFrequencyDifferenceSq_le_bound hν t t₀ f ξ
            simpa [h3HeatFrequencyDifferenceSq, Real.norm_eq_abs] using h)
        (h3HeatFrequency_bound_integrable f)
        (Eventually.of_forall fun ξ =>
          tendsto_h3HeatFrequencyDifferenceSq ν t₀ f ξ))
  have hSq :
      Tendsto
        (fun t : ℝ≥0 =>
          ‖h3HeatFrequencyApplyNN ν hν t f -
              h3HeatFrequencyApplyNN ν hν t₀ f‖ ^ 2)
        (𝓝 t₀)
        (𝓝 0) := by
    simpa only [h3HeatFrequencyApplyNN_sub_norm_sq ν hν] using hIntegral
  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp hSq
  change
    Tendsto
      (fun t : ℝ≥0 =>
        Real.sqrt
          (‖h3HeatFrequencyApplyNN ν hν t f -
              h3HeatFrequencyApplyNN ν hν t₀ f‖ ^ 2))
      (𝓝 t₀)
      (𝓝 (Real.sqrt 0)) at hSqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hSqrt

/-! ## Strong continuity after Fourier inversion and real transport -/

/-- Strong continuity of complex physical-space heat evolution. -/
theorem continuous_h3ComplexHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (f : H3FourierComplexL2) :
    Continuous (fun t : ℝ≥0 => h3ComplexHeatApplyNN ν hν t f) := by
  unfold h3ComplexHeatApplyNN h3ComplexHeatApply
  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.continuous.comp
      (continuous_h3HeatFrequencyApplyNN ν hν
        ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) f))

/-- Transport back from Euclidean Fourier space is continuous. -/
theorem continuous_h3FromFourierRealL2 :
    Continuous (h3FromFourierRealL2 : H3FourierRealL2 → H3ScalarL2) := by
  unfold h3FromFourierRealL2
  exact
    (MeasureTheory.Lp.isometry_compMeasurePreserving
      (E := ℝ)
      (p := (2 : ℝ≥0∞))
      (PiLp.volume_preserving_toLp (PrimeTensor.Axis Depth.three))).continuous

/-- Pointwise real projection on `L²` is continuous. -/
theorem continuous_h3RealPartFourierL2 :
    Continuous (h3RealPartFourierL2 : H3FourierComplexL2 → H3FourierRealL2) := by
  unfold h3RealPartFourierL2
  exact
    (Complex.reCLM.compLpL
      (2 : ℝ≥0∞)
      (volume : Measure H3FourierPoint3)).continuous

/-- Strong continuity of the real scalar heat evolution on `L²(Point3)`. -/
theorem continuous_h3ScalarHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (f : H3ScalarL2) :
    Continuous (fun t : ℝ≥0 => h3ScalarHeatApplyNN ν hν t f) := by
  unfold h3ScalarHeatApplyNN h3ScalarHeatApply
  exact
    continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        (continuous_h3ComplexHeatApplyNN ν hν
          (h3ComplexifyFourierL2 (h3ToFourierRealL2 f))))

/-- Strong continuity of the complete 120-coordinate H³ jet heat evolution. -/
theorem continuous_h3L2JetHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (J : H3L2JetState) :
    Continuous (fun t : ℝ≥0 => h3L2JetHeatApplyNN ν hν t J) := by
  apply continuous_pi
  intro a
  exact continuous_h3ScalarHeatApplyNN ν hν (J a)

/-! ## Normalized physical time and the free path -/

/-- Physical time `τ s`, packaged as a nonnegative real. -/
def h3PhysicalTimeNN
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (s : H3UnitTime) : ℝ≥0 :=
  ⟨h3PhysicalTime τ s,
    (h3PhysicalTime_mem_Icc hτ s).1⟩

@[simp]
theorem h3PhysicalTimeNN_val
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (s : H3UnitTime) :
    (h3PhysicalTimeNN τ hτ s : ℝ) =
      h3PhysicalTime τ s :=
  rfl

/-- Normalized time maps continuously into nonnegative physical time. -/
theorem continuous_h3PhysicalTimeNN
    (τ : ℝ)
    (hτ : 0 ≤ τ) :
    Continuous (h3PhysicalTimeNN τ hτ) := by
  unfold h3PhysicalTimeNN h3PhysicalTime
  fun_prop

/--
The genuine normalized free heat path

    s ↦ exp (ν τ s Δ) J₀

as an element of the concrete mild path space.
-/
def h3L2JetHeatFreePath
    (ν τ : ℝ)
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ)
    (J : H3L2JetState) :
    H3L2JetPath :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s : H3UnitTime =>
      h3L2JetHeatApplyNN ν hν (h3PhysicalTimeNN τ hτ s) J)
    ((continuous_h3L2JetHeatApplyNN ν hν J).comp
      (continuous_h3PhysicalTimeNN τ hτ))
    ‖J‖
    (fun s =>
      norm_h3L2JetHeatApplyNN_le
        ν hν (h3PhysicalTimeNN τ hτ s) J)

@[simp]
theorem h3L2JetHeatFreePath_apply
    (ν τ : ℝ)
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ)
    (J : H3L2JetState)
    (s : H3UnitTime) :
    h3L2JetHeatFreePath ν τ hν hτ J s =
      h3L2JetHeatApply ν (h3PhysicalTime τ s)
        hν (h3PhysicalTime_mem_Icc hτ s).1 J :=
  rfl

/-- The normalized free path has no larger uniform norm than its initial jet. -/
theorem norm_h3L2JetHeatFreePath_le
    (ν τ : ℝ)
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ)
    (J : H3L2JetState) :
    ‖h3L2JetHeatFreePath ν τ hν hτ J‖ ≤ ‖J‖ := by
  apply
    (BoundedContinuousFunction.norm_le
      (f := h3L2JetHeatFreePath ν τ hν hτ J)
      (norm_nonneg J)).2
  intro s
  exact
    norm_h3L2JetHeatApplyNN_le
      ν hν (h3PhysicalTimeNN τ hτ s) J

/--
For a genuine logged H³ snapshot, the entire normalized free path is controlled
by the square root of the canonical H³ energy.
-/
theorem norm_h3L2JetHeatFreePath_velocityH3L2JetAt_le_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t₀ ν τ : ℝ}
    (hInt : VelocityH3IntegrableAt u t₀)
    (hMeas : VelocityH3MeasurableAt u t₀)
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ) :
    ‖h3L2JetHeatFreePath ν τ hν hτ
        (velocityH3L2JetAt u t₀ hInt hMeas)‖
      ≤ Real.sqrt (velocityH3EnergyAt u t₀) := by
  calc
    ‖h3L2JetHeatFreePath ν τ hν hτ
        (velocityH3L2JetAt u t₀ hInt hMeas)‖
        ≤ ‖velocityH3L2JetAt u t₀ hInt hMeas‖ :=
      norm_h3L2JetHeatFreePath_le
        ν τ hν hτ
        (velocityH3L2JetAt u t₀ hInt hMeas)
    _ ≤ Real.sqrt (velocityH3EnergyAt u t₀) :=
      velocityH3L2JetAt_norm_le_sqrt_energy hInt hMeas

end

end Euclidean
end Bridge
end PrimeTensor
