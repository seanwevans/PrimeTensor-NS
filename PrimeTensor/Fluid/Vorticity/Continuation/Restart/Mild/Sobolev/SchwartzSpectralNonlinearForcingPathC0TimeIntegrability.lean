import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingHeatSpatialDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingPathDerivativeBilinear

/-!
# Time integrability of the classical retarded nonlinear forcing path

The derivative path is now continuous and interval integrable, and the fixed-lag
Fourier multiplier has been identified with the genuine spatial derivative.
To differentiate the Duhamel time integral itself, the parametric-integral
argument also needs the undifferentiated classical reconstruction to be
integrable in the source-time variable.

This file closes that zeroth-order time-side prerequisite.  It proves:

* a lag-uniform pointwise bilinear bound for the positive-lag classical
  reconstruction;
* exact subtraction identities in the two spectral inputs;
* continuity in the positive heat lag for frozen inputs;
* continuity of the full retarded path for continuous spectral inputs; and
* interval integrability on `0..t` under uniform H³ bounds.

Unlike the first-derivative path, no endpoint singularity appears here: the
heat multiplier is contractive, so the scalar time majorant is simply the
constant `C_force * MU * MV`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathC0TimeIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The positive-lag classical nonlinear forcing reconstruction is bounded by
its Fourier `L¹` mass. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_integral
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i x‖
      ≤
    ∫ ξ : H3FourierPoint3,
      ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i ξ‖ := by
  rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel]
  calc
    ‖∫ ξ : H3FourierPoint3,
        h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
          ν τ U V i x ξ‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
          ν τ U V i x ξ‖ :=
      norm_integral_le_integral_norm _
    _ =
      ∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      unfold h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
      simp only [Circle.norm_smul]

/-- Heat contractivity makes the Fourier `L¹` norm no larger than the
unheated nonlinear forcing mass. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_norm_integral_le_L1Mass
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖)
      ≤
    h3RawFinLerayOuterProductDivergenceL1Mass U V i := by
  have hHeatInt :=
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative_integrable
      hν hτ U V i).norm
  have hRawInt :=
    (h3RawFinLerayOuterProductDivergence_integrable U V i).norm

  unfold h3RawFinLerayOuterProductDivergenceL1Mass
  refine integral_mono_ae hHeatInt hRawInt ?_
  filter_upwards with ξ
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [norm_mul]
  exact
    mul_le_of_le_one_left
      (norm_nonneg _)
      (norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ)

/-- Uniform pointwise bilinear bound for the fixed positive-lag classical
reconstruction. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i x‖
      ≤
    h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V‖ := by
  exact
    (norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_integral
      hν hτ U V i x).trans
      ((h3RawFinLerayOuterProductDivergenceHeatRepresentative_norm_integral_le_L1Mass
        hν hτ U V i).trans
        (h3RawFinLerayOuterProductDivergenceL1Mass_le U V i))

/-! ## Bilinear subtraction for the classical reconstruction -/

/-- The fixed-lag classical reconstruction is subtractive in its first
spectral input. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ (U - V) W i x
      =
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U W i x
      -
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ V W i x := by
  rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel]
  rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel]
  rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel]

  have hUInt :=
    h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
      hν hτ U W i x
  have hVInt :=
    h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
      hν hτ V W i x

  rw [← integral_sub hUInt hVInt]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
  rw [h3RawFinLerayOuterProductDivergenceHeatRepresentative_sub_left]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- The fixed-lag classical reconstruction is subtractive in its second
spectral input. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U (V - W) i x
      =
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i x
      -
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U W i x := by
  rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel]
  rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel]
  rw [h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel]

  have hVInt :=
    h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
      hν hτ U V i x
  have hWInt :=
    h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
      hν hτ U W i x

  rw [← integral_sub hVInt hWInt]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
  rw [h3RawFinLerayOuterProductDivergenceHeatRepresentative_sub_right]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- First-input variation is controlled linearly by the spectral difference. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U U₀ V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ (U - U₀) V i x‖
      ≤
    h3NonlinearForcingL1Coefficient * ‖U - U₀‖ * ‖V‖ := by
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear
      hν hτ (U - U₀) V i x

/-- Second-input variation is controlled linearly by the spectral difference. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V V₀ : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U (V - V₀) i x‖
      ≤
    h3NonlinearForcingL1Coefficient * ‖U‖ * ‖V - V₀‖ := by
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear
      hν hτ U (V - V₀) i x

/-! ## Frozen-input positive-lag continuity -/

/-- Later positive heat lags are pointwise dominated by an earlier positive
lag in the inverse-Fourier kernel. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_le_of_le
    {ν a τ : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (haτ : a ≤ τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
        ν τ U V i x ξ‖
      ≤
    ‖h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
        ν a U V i x ξ‖ := by
  have hb : 0 ≤ τ - a := sub_nonneg.mpr haτ
  have hsplit : a + (τ - a) = τ := by ring
  have hheat :
      h3HeatFourierSymbol ν τ ξ
        =
      h3HeatFourierSymbol ν (τ - a) ξ *
        h3HeatFourierSymbol ν a ξ := by
    simpa only [hsplit] using
      (h3HeatFourierSymbol_add ν a (τ - a) ξ)
  have hcontract :
      ‖h3HeatFourierSymbol ν (τ - a) ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one hν.le hb ξ

  unfold h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
  simp only [Circle.norm_smul]
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [hheat]
  calc
    ‖(h3HeatFourierSymbol ν (τ - a) ξ *
          h3HeatFourierSymbol ν a ξ) *
        h3RawFinLerayOuterProductDivergence U V i ξ‖
        =
      ‖h3HeatFourierSymbol ν (τ - a) ξ‖ *
        (‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖) := by
      simp only [norm_mul]
      ring
    _ ≤
      1 *
        (‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖) := by
      exact
        mul_le_mul_of_nonneg_right
          hcontract
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ =
      ‖h3HeatFourierSymbol ν a ξ *
        h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
      simp only [norm_mul, one_mul]

/-- For fixed inputs and spatial point, the inverse-Fourier kernel is
continuous in the heat lag. -/
theorem continuous_h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_lag
    (ν : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x ξ : H3FourierPoint3) :
    Continuous
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
          ν τ U V i x ξ) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  unfold h3HeatFourierSymbol
  fun_prop

/-- Frozen-input fixed-point reconstruction is continuous at every strictly
positive heat lag. -/
theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatC3Representative_lag
    {ν τ₀ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i x)
      τ₀ := by
  let a : ℝ := τ₀ / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have haτ₀ : a < τ₀ := by
    dsimp [a]
    linarith
  have hnear : Set.Ioi a ∈ 𝓝 τ₀ :=
    Ioi_mem_nhds haτ₀

  have hBoundInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
            ν a U V i x ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
      hν ha U V i x).norm

  have hIntegral :
      Tendsto
        (fun τ : ℝ =>
          ∫ ξ : H3FourierPoint3,
            h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
              ν τ U V i x ξ)
        (𝓝 τ₀)
        (𝓝
          (∫ ξ : H3FourierPoint3,
            h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
              ν τ₀ U V i x ξ)) := by
    exact
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝 τ₀)
        (F := fun τ : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
            ν τ U V i x)
        (f :=
          h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
            ν τ₀ U V i x)
        (bound := fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
            ν a U V i x ξ‖)
        (by
          filter_upwards [hnear] with τ hτ
          exact
            (h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_integrable
              hν (lt_trans ha hτ) U V i x).aestronglyMeasurable)
        (by
          filter_upwards [hnear] with τ hτ
          exact
            Eventually.of_forall fun ξ =>
              norm_h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_le_of_le
                hν ha hτ.le U V i x ξ)
        hBoundInt
        (Eventually.of_forall fun ξ =>
          (continuous_h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_lag
            ν U V i x ξ).continuousAt)

  show Tendsto
    (fun τ : ℝ =>
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i x)
    (𝓝 τ₀)
    (𝓝
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ₀ U V i x))
  simpa only [
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel
  ] using hIntegral

/-- Frozen-input retarded reconstruction is continuous at every source time
strictly before the target time. -/
theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatC3Representative_retarded_frozen
    {ν t s₀ : ℝ}
    (hν : 0 < ν)
    (hs₀ : s₀ < t)
    (U₀ V₀ : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν (t - s) U₀ V₀ i x)
      s₀ := by
  have hLag :
      ContinuousAt (fun s : ℝ => t - s) s₀ :=
    continuousAt_const.sub continuousAt_id
  exact
    (continuousAt_h3RawFinLerayOuterProductDivergenceHeatC3Representative_lag
      hν (sub_pos.mpr hs₀) U₀ V₀ i x).comp hLag

/-! ## Retarded path continuity and time integrability -/

/-- Classical pointwise nonlinear heat reconstruction along a retarded
spectral path. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatC3Representative
    ν (t - s) (U s) (V s) i x

/-- Exact three-term decomposition of a retarded zeroth-order path
difference. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_sub_decomposition
    {ν t s s₀ : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (hs₀ : s₀ < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x s
      -
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x s₀
      =
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (t - s) (U s - U s₀) (V s) i x
      +
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (t - s) (U s₀) (V s - V s₀) i x
      +
    (h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (t - s) (U s₀) (V s₀) i x
      -
     h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (t - s₀) (U s₀) (V s₀) i x) := by
  have hτ : 0 < t - s := sub_pos.mpr hs
  unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
  have hA :=
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left
      hν hτ (U s) (U s₀) (V s) i x
  have hB :=
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right
      hν hτ (U s₀) (V s) (V s₀) i x
  rw [hA, hB]
  abel

/-- For continuous spectral input paths, the classical retarded nonlinear
reconstruction is continuous at every source time strictly before the target
observation time. -/
theorem continuousAt_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
    {ν t s₀ : ℝ}
    (hν : 0 < ν)
    (hs₀ : s₀ < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x)
      s₀ := by
  let c : ℝ := h3NonlinearForcingL1Coefficient
  let T : ℝ → ℂ :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν (t - s) (U s₀) (V s₀) i x
  let g : ℝ → ℝ :=
    fun s =>
      c * ‖U s - U s₀‖ * ‖V s‖
        +
      c * ‖U s₀‖ * ‖V s - V s₀‖
        +
      ‖T s - T s₀‖

  have hTimeAt : ContinuousAt T s₀ := by
    dsimp [T]
    exact
      continuousAt_h3RawFinLerayOuterProductDivergenceHeatC3Representative_retarded_frozen
        hν hs₀ (U s₀) (V s₀) i x

  have hgCont : ContinuousAt g s₀ := by
    dsimp [g, c]
    exact
      ((((continuousAt_const.mul
          (hU.continuousAt.sub continuousAt_const).norm).mul
          hV.continuousAt.norm).add
        ((continuousAt_const.mul continuousAt_const).mul
          (hV.continuousAt.sub continuousAt_const).norm)).add
        (hTimeAt.sub continuousAt_const).norm)

  have hgZero : Tendsto g (𝓝 s₀) (𝓝 0) := by
    simpa [g] using hgCont.tendsto

  have hNear : ∀ᶠ s : ℝ in 𝓝 s₀, s < t :=
    eventually_lt_nhds hs₀

  have hUpper :
      ∀ᶠ s : ℝ in 𝓝 s₀,
        ‖h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν t U V i x s
            -
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν t U V i x s₀‖
          ≤
        g s := by
    filter_upwards [hNear] with s hs
    have hlag : 0 < t - s := sub_pos.mpr hs
    have hDiff :=
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_sub_decomposition
        hν hs hs₀ U V i x
    rw [hDiff]

    have hAbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U s - U s₀) (V s) i x‖
          ≤
        c * ‖U s - U s₀‖ * ‖V s‖ := by
      dsimp [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_left_le
          hν hlag (U s) (U s₀) (V s) i x

    have hBbound :
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U s₀) (V s - V s₀) i x‖
          ≤
        c * ‖U s₀‖ * ‖V s - V s₀‖ := by
      dsimp [c]
      exact
        norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_sub_right_le
          hν hlag (U s₀) (V s) (V s₀) i x

    change
      ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U s - U s₀) (V s) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν (t - s) (U s₀) (V s - V s₀) i x
          +
        (T s - T s₀)‖
        ≤ g s

    calc
      ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s - U s₀) (V s) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s₀) (V s - V s₀) i x
          +
        (T s - T s₀)‖
          ≤
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s - U s₀) (V s) i x
          +
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s₀) (V s - V s₀) i x‖
          +
        ‖T s - T s₀‖ :=
        norm_add_le _ _
      _ ≤
        (‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s - U s₀) (V s) i x‖
          +
        ‖h3RawFinLerayOuterProductDivergenceHeatC3Representative
              ν (t - s) (U s₀) (V s - V s₀) i x‖)
          +
        ‖T s - T s₀‖ := by
        exact add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤
        (c * ‖U s - U s₀‖ * ‖V s‖
          +
        c * ‖U s₀‖ * ‖V s - V s₀‖)
          +
        ‖T s - T s₀‖ := by
        exact add_le_add (add_le_add hAbound hBbound) (le_refl _)
      _ = g s := by rfl

  exact
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Eventually.of_forall fun s =>
          norm_nonneg
            (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
                ν t U V i x s
              -
            h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
                ν t U V i x s₀))
        hUpper
        hgZero)

/-- The zeroth-order classical retarded path is continuous throughout the open
Duhamel interval. -/
theorem continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Ioo
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousOn
      (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x)
      (Set.Ioo (0 : ℝ) t) := by
  intro s hs
  exact
    (continuousAt_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
      hν hs.2 U V hU hV i x).continuousWithinAt

/-- Under uniform path bounds, the classical retarded reconstruction has a
constant pointwise time majorant. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_le
    {ν t MU MV s : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (hU : ‖U s‖ ≤ MU)
    (hV : ‖V s‖ ≤ MV)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x s‖
      ≤
    h3NonlinearForcingL1Coefficient * MU * MV := by
  have hτ : 0 < t - s := sub_pos.mpr hs.2
  have h0 :=
    norm_h3RawFinLerayOuterProductDivergenceHeatC3Representative_le_bilinear
      hν hτ (U s) (V s) i x
  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg
  have h1 :
      h3NonlinearForcingL1Coefficient * ‖U s‖
        ≤
      h3NonlinearForcingL1Coefficient * MU :=
    mul_le_mul_of_nonneg_left hU hC
  have h2 :
      h3NonlinearForcingL1Coefficient * ‖U s‖ * ‖V s‖
        ≤
      h3NonlinearForcingL1Coefficient * MU * MV :=
    mul_le_mul h1 hV (norm_nonneg _) (mul_nonneg hC hMU)
  exact h0.trans h2

/-- Continuous spectral paths with uniform interior bounds give an
interval-integrable classical retarded forcing at every fixed spatial point. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_intervalIntegrable_of_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖U s‖ ≤ MU)
    (hV : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x)
      volume
      0
      t := by
  let M : ℝ := h3NonlinearForcingL1Coefficient * MU * MV

  have hMajorantIoo :
      IntegrableOn
        (fun _s : ℝ => M)
        (Set.Ioo (0 : ℝ) t)
        volume := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact intervalIntegrable_const

  have hMeas :
      AEStronglyMeasurable
        (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    (continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Ioo
      hν U V hUcont hVcont i x).aestronglyMeasurable measurableSet_Ioo

  have hIoo :
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i x)
        (Set.Ioo (0 : ℝ) t)
        volume := by
    refine hMajorantIoo.mono' hMeas ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    dsimp [M]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_le
        hν hMU hMV U V hs (hU s hs) (hV s hs) i x

  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hIoo

end

end Euclidean
end Bridge
end PrimeTensor
