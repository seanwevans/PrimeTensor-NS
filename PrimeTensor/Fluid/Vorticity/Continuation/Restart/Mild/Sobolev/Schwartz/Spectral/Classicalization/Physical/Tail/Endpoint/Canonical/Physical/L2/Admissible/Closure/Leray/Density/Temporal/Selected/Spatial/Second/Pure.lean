import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.Spatial.First
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quadratic.Inverse.Frechet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Spatial.PDE.Form

/-!
# Physical L² temporal admissibility: selected pure second spatial jet

The zero-order and first-spatial selected velocity jets are already jointly
continuous in `(time,space)`.

This file closes the remaining pure second spatial jet.

The key point is that the selected positive-time path has a stronger topology
than bare H³ continuity: the quadratic weighted raw-Fourier mass of the
difference state tends to zero.  The quadratic Fourier classicalization layer
also gives a spatial-point-independent operator-norm estimate for the complete
second Fréchet derivative.

For one coordinate direction `a` this gives a uniform bound

    ‖∂ₐ² Rep(W(r)-W(s))(x)‖
      ≤ C₂,a M₂(W(r)-W(s)),

independent of `x`.

A joint increment then splits as

    ∂ₐ² Rep(W(r))(y) - ∂ₐ² Rep(W(s))(x)
      =
    [∂ₐ² Rep(W(r))(y) - ∂ₐ² Rep(W(s))(y)]
      +
    [∂ₐ² Rep(W(s))(y) - ∂ₐ² Rep(W(s))(x)].

The first bracket tends to zero uniformly in `y` by quadratic difference-mass
continuity; the second tends to zero by ordinary spatial continuity of the
fixed positive-time `C³` selected slice.

This is genuine joint continuity, not an inference from separate continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalSelectedPureSecond
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by the physical weak-test layer. -/
local instance point3NormTopologicalSpaceH3PhysicalL2TemporalSelectedPureSecond :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Generic order-two transport from the real `Point3` representative to the
real part of the complex Fourier-carrier representative, under the cubic
moment regularity available for selected positive-time difference states. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_secondFrechet_eval_eq_re_of_cubic
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H)
    (x : Point3)
    (m : Fin 2 → Point3) :
    iteratedFDeriv ℝ 2
        (h3SpectralScalarRealC1RepresentativeOnPoint3 H)
        x m
      =
    (iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative H)
        (h3Point3ToFourierCLM x)
        (fun k => h3Point3ToFourierCLM (m k))).re := by
  have hComplexC3 :
      ContDiff ℝ 3
        (h3SpectralScalarC1Representative H) :=
    h3SpectralScalarC1Representative_contDiff_three_of_cubic
      H hThree

  have hRealC3 :
      ContDiff ℝ 3
        (h3SpectralScalarRealC1Representative H) :=
    h3SpectralScalarRealC1Representative_contDiff_three_of_cubic
      H hThree

  have hComplexC2 :
      ContDiff ℝ 2
        (h3SpectralScalarC1Representative H) :=
    hComplexC3.of_le (by norm_num)

  have hRealC2 :
      ContDiff ℝ 2
        (h3SpectralScalarRealC1Representative H) :=
    hRealC3.of_le (by norm_num)

  have hLeft :
      iteratedFDeriv ℝ 2
          (h3SpectralScalarRealC1Representative H)
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative H)
          (h3Point3ToFourierCLM x)) := by
    unfold h3SpectralScalarRealC1Representative

    change
      iteratedFDeriv ℝ 2
          (Complex.reCLM ∘
            h3SpectralScalarC1Representative H)
          (h3Point3ToFourierCLM x)
        =
      Complex.reCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative H)
          (h3Point3ToFourierCLM x))

    exact
      Complex.reCLM.iteratedFDeriv_comp_left
        hComplexC2.contDiffAt
        (by norm_num)

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      H
  ]

  have hRight :=
    h3Point3ToFourierCLM.iteratedFDeriv_comp_right
      hRealC2
      x
      (i := 2)
      (by norm_num)

  rw [hRight]

  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply
  ]

  rw [hLeft]

  rfl

/-- Repeated concrete coordinate derivatives respect subtraction for spatially
`C²` real scalar fields. -/
theorem SpatialC2.spatial_d_square_sub
    {f g : ScalarField3}
    (hf : SpatialC2 f)
    (hg : SpatialC2 g)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d a
        (spatial3.d a
          (fun y : Point3 => f y - g y))
        x
      =
    spatial3.d a
        (spatial3.d a f)
        x
      -
    spatial3.d a
        (spatial3.d a g)
        x := by
  have hSub : SpatialC2 (fun y : Point3 => f y - g y) := by
    unfold SpatialC2 at hf hg ⊢
    exact hf.sub hg

  rw [
    hSub.spatial_d_square_eq_iteratedFDeriv_two_const
      x a,
    hf.spatial_d_square_eq_iteratedFDeriv_two_const
      x a,
    hg.spatial_d_square_eq_iteratedFDeriv_two_const
      x a
  ]

  have hfCont : ContDiff ℝ 2 f := by
    exact hf

  have hgCont : ContDiff ℝ 2 g := by
    exact hg

  have hIter :=
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 2)
      (x := x)
      hfCont.contDiffAt
      hgCont.contDiffAt

  have hEval :=
    congrArg
      (fun T =>
        T (fun _ : Fin 2 => axisDirection a))
      hIter

  change
    (iteratedFDeriv ℝ 2 (f - g) x)
        (fun _ : Fin 2 => axisDirection a)
      =
    (iteratedFDeriv ℝ 2 f x)
        (fun _ : Fin 2 => axisDirection a)
      -
    (iteratedFDeriv ℝ 2 g x)
        (fun _ : Fin 2 => axisDirection a)

  exact hEval

/-- Fixed coefficient for one repeated physical coordinate direction in the
uniform quadratic second-derivative estimate. -/
noncomputable def h3PhysicalPureSecondQuadraticCoefficient
    (a : PrimeTensor.Axis Depth.three) : ℝ :=
  h3QuadraticFourierSecondFrechetCoefficient *
    ∏ k : Fin 2,
      ‖h3Point3ToFourierCLM (axisDirection a)‖

theorem h3PhysicalPureSecondQuadraticCoefficient_nonneg
    (a : PrimeTensor.Axis Depth.three) :
    0 ≤ h3PhysicalPureSecondQuadraticCoefficient a := by
  unfold h3PhysicalPureSecondQuadraticCoefficient
  exact
    mul_nonneg
      h3QuadraticFourierSecondFrechetCoefficient_nonneg
      (Finset.prod_nonneg
        (fun k _ =>
          norm_nonneg
            (h3Point3ToFourierCLM (axisDirection a))))

/-- Uniform-in-space quadratic mass bound for one pure second derivative of a
cubic-moment spectral state. -/
theorem norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_square_apply_le_quadraticMass
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    ‖spatial3.d a
        (spatial3.d a
          (h3SpectralScalarRealC1RepresentativeOnPoint3 H))
        x‖
      ≤
    h3PhysicalPureSecondQuadraticCoefficient a *
      h3SpectralScalarRawFourierMomentMass (2 : ℝ) H := by
  have hTwo :
      H3RawFourierMomentIntegrable (2 : ℝ) H :=
    h3RawFourierMomentIntegrable_two_of_three
      H hThree

  have hC3 :
      SpatialC3
        (h3SpectralScalarRealC1RepresentativeOnPoint3 H) := by
    unfold SpatialC3
    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_three_of_cubic
        H hThree

  have hC2 :
      SpatialC2
        (h3SpectralScalarRealC1RepresentativeOnPoint3 H) :=
    hC3.toSpatialC2

  let mP : Fin 2 → Point3 :=
    fun _ => axisDirection a

  let mF : Fin 2 → H3FourierPoint3 :=
    fun k => h3Point3ToFourierCLM (mP k)

  let xH : H3FourierPoint3 :=
    h3Point3ToFourierCLM x

  let D2 :
      ContinuousMultilinearMap
        ℝ
        (fun _ : Fin 2 => H3FourierPoint3)
        ℂ :=
    iteratedFDeriv ℝ 2
      (FourierTransform.fourier
        (h3SpectralScalarRawFourier H))
      (-xH)

  have hSquare :=
    hC2.spatial_d_square_eq_iteratedFDeriv_two_const
      x a

  have hTransport :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_secondFrechet_eval_eq_re_of_cubic
      H hThree x mP

  have hInverse :=
    h3SpectralScalarC1Representative_secondFrechet_eval_eq_fourier_neg
      H hTwo xH mF

  have hKNonneg :
      0 ≤
        ∏ k : Fin 2, ‖-mF k‖ :=
    Finset.prod_nonneg
      (fun k _ => norm_nonneg (-mF k))

  have hEval :
      ‖D2 (fun k => -mF k)‖
        ≤
      ‖D2‖ *
        ∏ k : Fin 2, ‖-mF k‖ := by
    exact
      D2.le_opNorm
        (fun k => -mF k)

  have hOp :
      ‖D2‖
        ≤
      h3QuadraticFourierSecondFrechetCoefficient *
        h3SpectralScalarRawFourierMomentMass (2 : ℝ) H := by
    dsimp only [D2, xH]
    exact
      h3SpectralScalarRawFourier_fourier_secondFrechet_norm_le
        H hTwo
        (-h3Point3ToFourierCLM x)

  have hEvalBound :
      ‖D2 (fun k => -mF k)‖
        ≤
      (h3QuadraticFourierSecondFrechetCoefficient *
          h3SpectralScalarRawFourierMomentMass (2 : ℝ) H) *
        ∏ k : Fin 2, ‖-mF k‖ := by
    exact
      hEval.trans
        (mul_le_mul_of_nonneg_right
          hOp hKNonneg)

  have hRe :
      ‖(D2 (fun k => -mF k)).re‖
        ≤
      ‖D2 (fun k => -mF k)‖ := by
    simpa [Real.norm_eq_abs] using
      Complex.abs_re_le_norm
        (D2 (fun k => -mF k))

  rw [hSquare]
  rw [hTransport]
  rw [hInverse]

  have hBound :=
    hRe.trans hEvalBound

  dsimp only [
    D2,
    xH,
    mF,
    mP
  ] at hBound

  unfold h3PhysicalPureSecondQuadraticCoefficient

  simpa only [norm_neg, mul_assoc, mul_left_comm, mul_comm] using hBound

/-- Along the selected path, the difference of two pure second derivatives is
uniformly bounded in the spatial point by the quadratic difference mass. -/
theorem norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_pureSecond_difference_apply_le_quadraticMass
    {ν A r s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hr : 0 < r)
    (hrR : r < h3FinHeatLerayRestartRadius ν A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖spatial3.d a
          (spatial3.d a
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r i)))
          x
        -
      spatial3.d a
          (spatial3.d a
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s i)))
          x‖
      ≤
    h3PhysicalPureSecondQuadraticCoefficient a *
      h3SpectralScalarRawFourierMomentMass
        (2 : ℝ)
        (W r i - W s i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hrThreeOrd :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
      3 hν U₀ hA hU₀ hr hrR.le i

  have hsThreeOrd :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
      3 hν U₀ hA hU₀ hs hsR.le i

  have hrThree :
      H3RawFourierMomentIntegrable
        (3 : ℝ) (W r i) := by
    unfold H3RawFourierMomentIntegrable
    simpa only [
      W,
      h3FourierMomentWeight_three_classicalization_cubicFrechet
    ] using hrThreeOrd

  have hsThree :
      H3RawFourierMomentIntegrable
        (3 : ℝ) (W s i) := by
    unfold H3RawFourierMomentIntegrable
    simpa only [
      W,
      h3FourierMomentWeight_three_classicalization_cubicFrechet
    ] using hsThreeOrd

  have hDiffThree :
      H3RawFourierMomentIntegrable
        (3 : ℝ) (W r i - W s i) :=
    h3RawFourierMomentIntegrable_three_sub
      (W r i) (W s i) hrThree hsThree

  have hrC3 :
      SpatialC3
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W r i)) := by
    unfold SpatialC3
    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_three_of_cubic
        (W r i) hrThree

  have hsC3 :
      SpatialC3
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s i)) := by
    unfold SpatialC3
    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_three_of_cubic
        (W s i) hsThree

  have hDiffBound :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_square_apply_le_quadraticMass
      (W r i - W s i)
      hDiffThree
      x a

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_sub
      (W r i)
      (W s i)
  ] at hDiffBound

  have hSub :=
    hrC3.toSpatialC2.spatial_d_square_sub
      hsC3.toSpatialC2
      x a

  rw [hSub] at hDiffBound

  simpa only [W] using hDiffBound

/-- A pure second spatial derivative of one fixed positive-time selected slice
is continuous in the physical point. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_pureSecond_spatial_continuous
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    Continuous
      (spatial3.d a
        (spatial3.d a
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s i)))) := by
  let f : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s i)

  have hfC3 :
      SpatialC3 f := by
    unfold SpatialC3
    dsimp only [f]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        3 hν U₀ hA hU₀ hs hsR.le i

  have hFirstC2 :
      SpatialC2 (spatial3.d a f) :=
    hfC3.partialDeriv_contDiff_two a

  have hSecondC1 :
      SpatialC1
        (spatial3.d a
          (spatial3.d a f)) :=
    hFirstC2.partialDeriv_contDiff_one a

  dsimp only [f] at hSecondC1

  exact hSecondC1.continuous

/-- Every selected pure second spatial coordinate derivative is genuinely
jointly continuous on a strict positive elapsed-time slab inside the restart
radius. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_pureSecond_jointContinuousOn
    {ν A tau : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d a
          (spatial3.d a
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ z.1 i)))
          z.2)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
  intro z hz

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let s : ℝ := z.1
  let x : Point3 := z.2

  let J : ℝ → Point3 → ℝ :=
    fun r y =>
      spatial3.d a
        (spatial3.d a
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i)))
        y

  have hs : 0 < s := by
    dsimp only [s]
    exact hz.1.1

  have hsTau : s < tau := by
    dsimp only [s]
    exact hz.1.2

  have hsR :
      s < h3FinHeatLerayRestartRadius ν A :=
    lt_of_lt_of_le hsTau hTauR

  have hMass :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierMomentMass
            (2 : ℝ)
            (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W, s] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_quadraticDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hFst :
      Tendsto
        (fun w : ℝ × Point3 => w.1)
        (𝓝 z)
        (𝓝 s) := by
    dsimp only [s]
    exact continuousAt_fst

  have hMassProd :
      Tendsto
        (fun w : ℝ × Point3 =>
          h3SpectralScalarRawFourierMomentMass
            (2 : ℝ)
            (W w.1 i - W s i))
        (𝓝 z)
        (𝓝 0) :=
    hMass.comp hFst

  let C : ℝ :=
    h3PhysicalPureSecondQuadraticCoefficient a

  have hConst :
      Tendsto
        (fun _ : ℝ × Point3 => C)
        (𝓝 z)
        (𝓝 C) :=
    tendsto_const_nhds

  have hTimeUpper :
      Tendsto
        (fun w : ℝ × Point3 =>
          C *
            h3SpectralScalarRawFourierMomentMass
              (2 : ℝ)
              (W w.1 i - W s i))
        (𝓝 z)
        (𝓝 0) := by
    have hMul :=
      hConst.mul hMassProd

    simpa only [mul_zero] using hMul

  have hFixedSpatial :
      Continuous (J s) := by
    dsimp only [J, W, s]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_pureSecond_spatial_continuous
        hν U₀ hA hU₀ hs hsR i a

  have hSpaceNormContinuous :
      Continuous
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖) :=
    ((hFixedSpatial.comp continuous_snd).sub continuous_const).norm

  have hSpaceNormAt :
      ContinuousAt
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖)
        z :=
    hSpaceNormContinuous.continuousAt

  have hSpaceNorm :
      Tendsto
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖)
        (𝓝 z)
        (𝓝 ‖J s z.2 - J s x‖)
      at hSpaceNormAt

    have hx : z.2 = x := by
      rfl

    simpa only [hx, sub_self, norm_zero] using hSpaceNormAt

  have hUpper :
      Tendsto
        (fun w : ℝ × Point3 =>
          C *
              h3SpectralScalarRawFourierMomentMass
                (2 : ℝ)
                (W w.1 i - W s i)
            +
          ‖J s w.2 - J s x‖)
        (𝓝 z)
        (𝓝 0) := by
    have hAdd :=
      hTimeUpper.add hSpaceNorm

    simpa only [zero_add] using hAdd

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyInterval :
      ∀ᶠ w in 𝓝 z,
        w.1 ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius ν A) :=
    hFst hInterval

  have hNonneg :
      ∀ᶠ w in 𝓝 z,
        0 ≤ ‖J w.1 w.2 - J s x‖ :=
    Filter.Eventually.of_forall
      (fun w =>
        norm_nonneg
          (J w.1 w.2 - J s x))

  have hBound :
      ∀ᶠ w in 𝓝 z,
        ‖J w.1 w.2 - J s x‖
          ≤
        C *
            h3SpectralScalarRawFourierMomentMass
              (2 : ℝ)
              (W w.1 i - W s i)
          +
        ‖J s w.2 - J s x‖ := by
    filter_upwards [hEventuallyInterval] with w hw

    have hTime :
        ‖J w.1 w.2 - J s w.2‖
          ≤
        C *
          h3SpectralScalarRawFourierMomentMass
            (2 : ℝ)
            (W w.1 i - W s i) := by
      dsimp only [J, C, W]

      exact
        norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_pureSecond_difference_apply_le_quadraticMass
          hν U₀ hA hU₀
          hw.1 hw.2
          hs hsR
          i w.2 a

    have hDecomp :
        J w.1 w.2 - J s x
          =
        (J w.1 w.2 - J s w.2)
          +
        (J s w.2 - J s x) := by
      ring

    rw [hDecomp]

    exact
      (norm_add_le _ _).trans
        (add_le_add
          hTime
          (le_refl
            ‖J s w.2 - J s x‖))

  have hNorm :
      Tendsto
        (fun w : ℝ × Point3 =>
          ‖J w.1 w.2 - J s x‖)
        (𝓝 z)
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hBound
      hUpper

  have hAt :
      ContinuousAt
        (fun w : ℝ × Point3 =>
          J w.1 w.2)
        z := by
    change
      Tendsto
        (fun w : ℝ × Point3 =>
          J w.1 w.2)
        (𝓝 z)
        (𝓝 (J z.1 z.2))

    rw [tendsto_iff_norm_sub_tendsto_zero]

    dsimp only [s, x] at hNorm

    exact hNorm

  exact hAt.continuousWithinAt

/-- The selected pure-second velocity frontier follows automatically from the
restart-radius inclusion already required by the endpoint argument. -/
theorem H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed_of_le_restartRadius
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E) :
    H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed
      (tau := tau)
      hν hNS ht hE hTail := by
  unfold
    H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed

  dsimp only

  intro a j

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hCoordinate :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          spatial3.d a
            (spatial3.d a
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W z.1
                  (h3ClassicalizationFinOfAxis j))))
            z.2)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
    dsimp only [W]

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_pureSecond_jointContinuousOn
        hν U₀ hA hU₀
        hTauR
        (h3ClassicalizationFinOfAxis j)
        a

  apply hCoordinate.congr

  intro z hz

  have hField :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ z.1 y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W z.1
          (h3ClassicalizationFinOfAxis j)) := by
    funext y

    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

    rw [
      h3SpectralRealVelocityOfPath_component
    ]

    rfl

  change
    spatial3.d a
        (spatial3.d a
          (fun y : Point3 =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ z.1 y).component j))
        z.2
      =
    spatial3.d a
        (spatial3.d a
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W z.1
              (h3ClassicalizationFinOfAxis j))))
        z.2

  exact
    congrArg
      (fun f : Point3 → ℝ =>
        spatial3.d a
          (spatial3.d a f)
          z.2)
      hField

/-- With all selected velocity jets now jointly continuous, the physical L²
identity needs only the selected pressure-force joint-continuity frontier. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedPressureForceJointlyContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hSelectedPressure :
      H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab
        (tau := tau)
        hNS ht hE hTail) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hSelectedSecond :
      H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed
        (tau := tau)
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail :=
    H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed_of_le_restartRadius
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hTauR

  exact
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedPureSecondJets_and_pressureForceJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint
      hEvolution hTauR
      hSelectedSecond hSelectedPressure

end

end Euclidean
end Bridge
end PrimeTensor
