import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncation.Convergence

/-!
# Bounded q³ truncation for the sixth-diffusion branch

The selected higher weighted state is now

    q³ û_j,

with continuous PDE right-hand side

    -q⁴ û_j - q³ F_j.

To transport the already-proved raw Fourier derivative without applying the
unbounded multiplier directly, this file repeats the successful top-tail
cutoff mechanism at intrinsic power three.

For `R ≥ 0` define

    T³_R f = 1_{|D| < R} q³ f.

Since `q = |D|²`, on the cutoff ball

    |q³| = |D|⁶ ≤ R⁶,

so `T³_R` is a bounded real continuous-linear operator on Fourier `L²`.

The file then proves:

* derivative transport through every fixed `T³_R`;
* generic strong cutoff removal whenever `G = q³ F` a.e.;
* norm domination `‖T³_R F‖ ≤ ‖G‖`;
* selected convergence of the raw velocity truncations to `q³ û_j`;
* selected convergence of the projected-RHS truncations to
  `-q⁴ û_j - q³ F_j`.

The natural high-frequency exhaustion is reused directly from the existing
`q²` truncation convergence file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSixthDiffusionQCubeTruncation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Pointwise q³ truncation -/

noncomputable def h3SixthDiffusionTruncatedQCubeMultiplier
    (R : ℝ)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3TerminalRadialFrequencyBelow R).indicator
    (fun η : H3FourierPoint3 =>
      ((h3FourierGradientSquare η ^ 3 : ℝ) : ℂ))
    ξ

theorem h3SixthDiffusionTruncatedQCubeMultiplier_aestronglyMeasurable
    (R : ℝ) :
    AEStronglyMeasurable
      (h3SixthDiffusionTruncatedQCubeMultiplier R)
      (volume : Measure H3FourierPoint3) := by

  unfold h3SixthDiffusionTruncatedQCubeMultiplier

  apply AEStronglyMeasurable.indicator
    ?_
    (measurableSet_h3TerminalRadialFrequencyBelow R)

  have hQCube :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 3) := by
    unfold h3FourierGradientSquare
    fun_prop

  exact
    (
      Complex.continuous_ofReal.comp hQCube
    ).aestronglyMeasurable

theorem norm_h3SixthDiffusionTruncatedQCubeMultiplier_le
    {R : ℝ}
    (hR : 0 ≤ R)
    (ξ : H3FourierPoint3) :
    ‖h3SixthDiffusionTruncatedQCubeMultiplier R ξ‖
      ≤
    R ^ 6 := by

  by_cases hξ :
      ξ ∈ h3TerminalRadialFrequencyBelow R

  · unfold h3SixthDiffusionTruncatedQCubeMultiplier
    rw [Set.indicator_of_mem hξ]

    have hGradLt :
        h3FourierGradientMagnitude ξ < R := by
      simpa only [
        h3TerminalRadialFrequencyBelow,
        Set.mem_ofPred_eq
      ] using hξ

    have hGradLe :
        h3FourierGradientMagnitude ξ ≤ R :=
      hGradLt.le

    have hPow :
        h3FourierGradientMagnitude ξ ^ 6
          ≤
        R ^ 6 :=
      pow_le_pow_left₀
        (h3FourierGradientMagnitude_nonneg ξ)
        hGradLe
        6

    rw [
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg
        (pow_nonneg
          (h3FourierGradientSquare_nonneg ξ)
          3),
      ← h3FourierGradientMagnitude_sq
    ]

    calc
      (h3FourierGradientMagnitude ξ ^ 2) ^ 3
          =
        h3FourierGradientMagnitude ξ ^ 6 := by
        ring
      _ ≤
        R ^ 6 :=
        hPow

  · unfold h3SixthDiffusionTruncatedQCubeMultiplier
    rw [Set.indicator_of_notMem hξ, norm_zero]
    positivity

noncomputable def h3SixthDiffusionTruncatedQCubeFunction
    (R : ℝ)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) : ℂ :=
  h3SixthDiffusionTruncatedQCubeMultiplier R ξ * f ξ

theorem h3SixthDiffusionTruncatedQCubeFunction_memLp
    {R : ℝ}
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    MemLp
      (h3SixthDiffusionTruncatedQCubeFunction R f)
      2
      (volume : Measure H3FourierPoint3) := by

  apply
    (MeasureTheory.Lp.memLp f).of_le_mul
      (c := R ^ 6)
      (
        (
          h3SixthDiffusionTruncatedQCubeMultiplier_aestronglyMeasurable R
        ).mul
          (MeasureTheory.Lp.aestronglyMeasurable f)
      )

  filter_upwards with ξ

  change
    ‖h3SixthDiffusionTruncatedQCubeMultiplier R ξ * f ξ‖
      ≤
    R ^ 6 * ‖f ξ‖

  rw [norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3SixthDiffusionTruncatedQCubeMultiplier_le hR ξ)
      (norm_nonneg (f ξ))

noncomputable def h3SixthDiffusionTruncatedQCubeL2
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  (
    h3SixthDiffusionTruncatedQCubeFunction_memLp
      hR f
  ).toLp
    (h3SixthDiffusionTruncatedQCubeFunction R f)

theorem h3SixthDiffusionTruncatedQCubeL2_ae
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    (
      (
        h3SixthDiffusionTruncatedQCubeL2 R hR f :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SixthDiffusionTruncatedQCubeFunction R f := by

  unfold h3SixthDiffusionTruncatedQCubeL2

  exact
    MemLp.coeFn_toLp
      (
        h3SixthDiffusionTruncatedQCubeFunction_memLp
          hR f
      )

/-! ## Real continuous-linear operator -/

theorem h3SixthDiffusionTruncatedQCubeL2_add
    (R : ℝ)
    (hR : 0 ≤ R)
    (f g : H3FourierComplexL2) :
    h3SixthDiffusionTruncatedQCubeL2 R hR (f + g)
      =
    h3SixthDiffusionTruncatedQCubeL2 R hR f
      +
    h3SixthDiffusionTruncatedQCubeL2 R hR g := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3SixthDiffusionTruncatedQCubeL2_ae R hR (f + g),
    h3SixthDiffusionTruncatedQCubeL2_ae R hR f,
    h3SixthDiffusionTruncatedQCubeL2_ae R hR g,
    Lp.coeFn_add f g,
    Lp.coeFn_add
      (h3SixthDiffusionTruncatedQCubeL2 R hR f)
      (h3SixthDiffusionTruncatedQCubeL2 R hR g)
  ] with ξ hfg hf hg hAdd hOutAdd

  rw [hfg, hOutAdd]
  simp only [Pi.add_apply]
  rw [hf, hg]

  unfold h3SixthDiffusionTruncatedQCubeFunction

  rw [hAdd]
  simp only [Pi.add_apply]

  ring

theorem h3SixthDiffusionTruncatedQCubeL2_smul_real
    (R : ℝ)
    (hR : 0 ≤ R)
    (c : ℝ)
    (f : H3FourierComplexL2) :
    h3SixthDiffusionTruncatedQCubeL2 R hR (c • f)
      =
    c • h3SixthDiffusionTruncatedQCubeL2 R hR f := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3SixthDiffusionTruncatedQCubeL2_ae R hR (c • f),
    h3SixthDiffusionTruncatedQCubeL2_ae R hR f,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c
      (h3SixthDiffusionTruncatedQCubeL2 R hR f)
  ] with ξ hcf hf hInSmul hOutSmul

  rw [hcf, hOutSmul]
  simp only [Pi.smul_apply]
  rw [hf]

  unfold h3SixthDiffusionTruncatedQCubeFunction

  rw [hInSmul]

  simp only [Pi.smul_apply, Complex.real_smul]

  ring

noncomputable def h3SixthDiffusionTruncatedQCubeRealLinearMap
    (R : ℝ)
    (hR : 0 ≤ R) :
    H3FourierComplexL2 →ₗ[ℝ] H3FourierComplexL2 where
  toFun :=
    h3SixthDiffusionTruncatedQCubeL2 R hR
  map_add' :=
    h3SixthDiffusionTruncatedQCubeL2_add R hR
  map_smul' := by
    intro c f
    exact
      h3SixthDiffusionTruncatedQCubeL2_smul_real
        R hR c f

@[simp]
theorem h3SixthDiffusionTruncatedQCubeRealLinearMap_apply
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    h3SixthDiffusionTruncatedQCubeRealLinearMap R hR f
      =
    h3SixthDiffusionTruncatedQCubeL2 R hR f := by
  rfl

theorem norm_h3SixthDiffusionTruncatedQCubeL2_le
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    ‖h3SixthDiffusionTruncatedQCubeL2 R hR f‖
      ≤
    R ^ 6 * ‖f‖ := by

  apply
    Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    h3SixthDiffusionTruncatedQCubeL2_ae R hR f
  ] with ξ hξ

  rw [hξ]

  unfold h3SixthDiffusionTruncatedQCubeFunction

  rw [norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3SixthDiffusionTruncatedQCubeMultiplier_le hR ξ)
      (norm_nonneg (f ξ))

noncomputable def h3SixthDiffusionTruncatedQCubeRealCLM
    (R : ℝ)
    (hR : 0 ≤ R) :
    H3FourierComplexL2 →L[ℝ] H3FourierComplexL2 :=
  (
    h3SixthDiffusionTruncatedQCubeRealLinearMap R hR
  ).mkContinuous
    (R ^ 6)
    (fun f => by
      change
        ‖h3SixthDiffusionTruncatedQCubeL2 R hR f‖
          ≤
        R ^ 6 * ‖f‖
      exact
        norm_h3SixthDiffusionTruncatedQCubeL2_le
          R hR f)

@[simp]
theorem h3SixthDiffusionTruncatedQCubeRealCLM_apply
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    h3SixthDiffusionTruncatedQCubeRealCLM R hR f
      =
    h3SixthDiffusionTruncatedQCubeL2 R hR f := by
  rfl

/-! ## Transport the raw selected derivative -/

theorem h3SelectedRestartVelocityRawFourierL2_truncatedQCube_hasDerivAt_unit
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ tau q R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
    (hR : 0 ≤ R)
    (i : Fin 3) :
    HasDerivAt
      (fun r : ℝ =>
        h3SixthDiffusionTruncatedQCubeL2
          R hR
          (
            h3SpectralScalarRawFourierL2
              (
                (
                  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalSelectedDecoderAnchorState
                      hNS ht₀ hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalSelectedDecoderAnchorState_le
                      hNS ht₀ hE hTail)
                    r
                ) i
              )
          ))
      (
        h3SixthDiffusionTruncatedQCubeL2
          R hR
          (
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail
              (
                h3PreterminalElapsedToSelectedUnitRadius
                  htauR
                  ⟨q, hq.1.le, hq.2.le⟩
              )
              i
          )
      )
      q := by

  have hRaw :=
    h3SelectedRestartVelocityRawFourierL2_hasDerivAt_unit
      hNS ht₀ htau hE hTail htauR hq i

  have h :=
    (
      h3SixthDiffusionTruncatedQCubeRealCLM
        R hR
    ).hasFDerivAt.comp_hasDerivAt
      q
      hRaw

  simpa only [
    Function.comp_def,
    h3SixthDiffusionTruncatedQCubeRealCLM_apply
  ] using h

/-! ## Generic cutoff removal -/

theorem norm_sq_h3SixthDiffusionTruncatedQCubeL2_sub_eq_highRadial_squareMass
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        F ξ))
    (n : ℕ) :
    ‖(
      h3SixthDiffusionTruncatedQCubeL2
          ((n : ℝ) + 1)
          (by positivity)
          F
        -
      G
    )‖ ^ 2
      =
    ∫ ξ in h3TopTailNaturalHighRadialSet n,
      ‖G ξ‖ ^ 2
    ∂volume := by

  rw [
    h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
  ]

  rw [
    ← integral_indicator
      (measurableSet_h3TopTailNaturalHighRadialSet n)
  ]

  apply integral_congr_ae

  have hTrunc :=
    h3SixthDiffusionTruncatedQCubeL2_ae
      ((n : ℝ) + 1)
      (by positivity)
      F

  filter_upwards [hTrunc, hFG] with ξ hTruncξ hFGξ

  rw [hTruncξ]

  unfold
    h3SixthDiffusionTruncatedQCubeFunction
    h3SixthDiffusionTruncatedQCubeMultiplier

  by_cases hLow :
      ξ ∈
        h3TerminalRadialFrequencyBelow
          ((n : ℝ) + 1)

  · rw [Set.indicator_of_mem hLow]
    rw [hFGξ]

    have hNotHigh :
        ξ ∉ h3TopTailNaturalHighRadialSet n := by
      simp only [
        h3TopTailNaturalHighRadialSet,
        Set.mem_compl_iff,
        not_not
      ]
      exact hLow

    rw [Set.indicator_of_notMem hNotHigh]

    simp

  · rw [Set.indicator_of_notMem hLow]

    have hHigh :
        ξ ∈ h3TopTailNaturalHighRadialSet n := by
      simpa only [
        h3TopTailNaturalHighRadialSet,
        Set.mem_compl_iff
      ] using hLow

    rw [Set.indicator_of_mem hHigh]

    simp

theorem tendsto_h3SixthDiffusionTruncatedQCubeL2_of_ae_eq
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        F ξ)) :
    Tendsto
      (fun n : ℕ =>
        h3SixthDiffusionTruncatedQCubeL2
          ((n : ℝ) + 1)
          (by positivity)
          F)
      atTop
      (𝓝 G) := by

  apply
    tendsto_iff_norm_sub_tendsto_zero.2

  have hTail :=
    tendsto_h3FourierComplexL2_highRadial_squareMass_zero
      G

  have hSq :
      Tendsto
        (fun n : ℕ =>
          ‖(
            h3SixthDiffusionTruncatedQCubeL2
                ((n : ℝ) + 1)
                (by positivity)
                F
              -
            G
          )‖ ^ 2)
        atTop
        (𝓝 0) := by

    apply
      hTail.congr'

    filter_upwards with n

    exact
      (
        norm_sq_h3SixthDiffusionTruncatedQCubeL2_sub_eq_highRadial_squareMass
          F G hFG n
      ).symm

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp
      hSq

  change
    Tendsto
      (fun n : ℕ =>
        Real.sqrt
          (
            ‖(
              h3SixthDiffusionTruncatedQCubeL2
                  ((n : ℝ) + 1)
                  (by positivity)
                  F
                -
              G
            )‖ ^ 2
          ))
      atTop
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

/-! ## Generic domination -/

theorem norm_h3SixthDiffusionTruncatedQCubeL2_le_of_ae_eq
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        F ξ))
    {R : ℝ}
    (hR : 0 ≤ R) :
    ‖h3SixthDiffusionTruncatedQCubeL2 R hR F‖
      ≤
    ‖G‖ := by

  apply Lp.norm_le_norm_of_ae_le

  have hTrunc :=
    h3SixthDiffusionTruncatedQCubeL2_ae
      R hR F

  filter_upwards [hTrunc, hFG]
    with ξ hTruncξ hFGξ

  rw [hTruncξ, hFGξ]

  unfold
    h3SixthDiffusionTruncatedQCubeFunction
    h3SixthDiffusionTruncatedQCubeMultiplier

  by_cases hLow :
      ξ ∈ h3TerminalRadialFrequencyBelow R

  · rw [Set.indicator_of_mem hLow]

  · rw [Set.indicator_of_notMem hLow]
    rw [zero_mul, norm_zero]
    exact norm_nonneg _

/-! ## Selected velocity convergence -/

theorem tendsto_h3SixthDiffusionTruncatedQCubeL2_selectedVelocityOnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    Tendsto
      (fun n : ℕ =>
        h3SixthDiffusionTruncatedQCubeL2
          ((n : ℝ) + 1)
          (by positivity)
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              (s : ℝ)
              j
          ))
      atTop
      (
        𝓝
          (
            h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
              hNS ht₀ hE hTail hQ hQR j s
          )
      ) := by

  let F : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      (s : ℝ)
      j

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j s

  have hG :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_ae
      hNS ht₀ hE hTail hQ hQR j s

  have hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        F ξ) := by

    dsimp only [F, G] at hG ⊢
    exact hG

  have h :=
    tendsto_h3SixthDiffusionTruncatedQCubeL2_of_ae_eq
      F G hFG

  dsimp only [F, G] at h ⊢

  exact h

/-! ## Selected projected-RHS convergence -/

theorem tendsto_h3SixthDiffusionTruncatedQCubeL2_selectedProjectedRHSOnSlab
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let qRadius :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨
        (s : ℝ),
        (
          lt_of_lt_of_le
            (by positivity : 0 < Q / 2)
            s.property.1
        ).le,
        (
          lt_of_le_of_lt
            s.property.2
            hQR
        ).le
      ⟩
    Tendsto
      (fun n : ℕ =>
        h3SixthDiffusionTruncatedQCubeL2
          ((n : ℝ) + 1)
          (by positivity)
          (
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail qRadius j
          ))
      atTop
      (
        𝓝
          (
            h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
              hNS ht₀ hE hTail hQ hQR j s
          )
      ) := by

  dsimp only

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (s : ℝ),
      (
        lt_of_lt_of_le
          (by positivity : 0 < Q / 2)
          s.property.1
      ).le,
      (
        lt_of_le_of_lt
          s.property.2
          hQR
      ).le
    ⟩

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius j

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j s

  have hFG :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab_ae_eq_qcube_projectedRHS
      hNS ht₀ hE hTail hQ hQR j s

  have h :=
    tendsto_h3SixthDiffusionTruncatedQCubeL2_of_ae_eq
      F G hFG

  dsimp only [F, G, qRadius] at h ⊢

  exact h

/-! ## Selected projected-RHS domination -/

theorem norm_h3SixthDiffusionTruncatedQCubeL2_selectedProjectedRHSOnSlab_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s : Set.Icc (Q / 2) Q)
    (n : ℕ) :
    let qRadius :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨
        (s : ℝ),
        (
          lt_of_lt_of_le
            (by positivity : 0 < Q / 2)
            s.property.1
        ).le,
        (
          lt_of_le_of_lt
            s.property.2
            hQR
        ).le
      ⟩
    ‖(
      h3SixthDiffusionTruncatedQCubeL2
        ((n : ℝ) + 1)
        (by positivity)
        (
          h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
            hNS ht₀ hE hTail qRadius j
        )
    )‖
      ≤
    ‖(
      h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR j s
    )‖ := by

  dsimp only

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (s : ℝ),
      (
        lt_of_lt_of_le
          (by positivity : 0 < Q / 2)
          s.property.1
      ).le,
      (
        lt_of_le_of_lt
          s.property.2
          hQR
      ).le
    ⟩

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius j

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j s

  have hFG :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab_ae_eq_qcube_projectedRHS
      hNS ht₀ hE hTail hQ hQR j s

  have h :=
    norm_h3SixthDiffusionTruncatedQCubeL2_le_of_ae_eq
      F G hFG
      (R := ((n : ℝ) + 1))
      (by positivity)

  dsimp only [F, G, qRadius] at h ⊢

  exact h

end

end Euclidean
end Bridge
end PrimeTensor
