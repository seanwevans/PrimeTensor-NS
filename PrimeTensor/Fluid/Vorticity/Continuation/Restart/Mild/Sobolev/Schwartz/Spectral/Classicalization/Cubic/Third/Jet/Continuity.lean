import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Third.Partial.Difference.Continuity

/-!
# Classicalization: cubic third-jet time continuity

The preceding classicalization layers have now proved that every ordered third
spatial partial of the real `Point3` representative of the *spectral
difference state*

    W r i - W s i

has norm tending to zero as `r → s`.

To turn that statement into ordinary time continuity of the third spatial jet
we need one algebraic fact: inverse-Fourier reconstruction respects
subtraction.

There is a small but important representation detail here.  A spectral state
is an `Lp` element, so the chosen pointwise representatives of `F - G` and
`F - G` formed after coercion agree only almost everywhere.  Consequently the
raw Fourier deweighting is first shown subtraction-linear *a.e.*.  The inverse
Fourier integral is insensitive to that representative choice, so the
classical complex, real, and `Point3` representatives are exactly
subtraction-linear as honest functions.

After that exact reconstruction bridge, the already-proved `C³`
partial/Fréchet identification and Mathlib's `iteratedFDeriv_sub_apply` give

    D_{a,b,c} Rep(W r i - W s i)
      =
    D_{a,b,c} Rep(W r i) - D_{a,b,c} Rep(W s i).

Thus the difference-to-zero estimate is precisely the metric criterion for
`ContinuousAt`.

This closes scalar ordered-third-jet time continuity for the selected restart
path.  The next layer only has to package the three scalar coordinates as the
project's real velocity representative and discharge
`RealVelocityThirdJetContinuousAt`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicThirdJetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-! ## Exact subtraction transport through reconstruction -/

/- Raw Fourier subtraction is already available in the imported classicalization
chain as `h3SpectralScalarRawFourier_sub_ae`; this file starts at the exact
inverse-Fourier reconstruction transport. -/

/-- The complex inverse-Fourier representative is exactly subtraction-linear.

The only non-pointwise input is `h3SpectralScalarRawFourier_sub_ae`; Fourier
integration turns that a.e. identity into equality of the resulting
classical functions. -/
theorem h3SpectralScalarC1Representative_sub
    (F G : H3SpectralScalarState) :
    h3SpectralScalarC1Representative (F - G)
      =
    fun x : H3FourierPoint3 =>
      h3SpectralScalarC1Representative F x
        -
      h3SpectralScalarC1Representative G x := by
  funext x

  have hFRaw :
      Integrable
        (h3SpectralScalarRawFourier F)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 F)

  have hGRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hRawSub :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hCongr :
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourier (F - G))
          x
        =
      FourierTransformInv.fourierInv
          (fun ξ : H3FourierPoint3 =>
            h3SpectralScalarRawFourier F ξ
              -
            h3SpectralScalarRawFourier G ξ)
          x :=
    Real.fourierInv_congr_ae hRawSub x

  have hFIntegrand :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          𝐞 ⟪ξ, x⟫_ℝ •
            h3SpectralScalarRawFourier F ξ)
        (volume : Measure H3FourierPoint3) := by
    have h :=
      (Real.fourierIntegral_convergent_iff
        (μ := (volume : Measure H3FourierPoint3))
        (f := h3SpectralScalarRawFourier F)
        (-x)).2 hFRaw
    simpa using h

  have hGIntegrand :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          𝐞 ⟪ξ, x⟫_ℝ •
            h3SpectralScalarRawFourier G ξ)
        (volume : Measure H3FourierPoint3) := by
    have h :=
      (Real.fourierIntegral_convergent_iff
        (μ := (volume : Measure H3FourierPoint3))
        (f := h3SpectralScalarRawFourier G)
        (-x)).2 hGRaw
    simpa using h

  unfold h3SpectralScalarC1Representative

  rw [hCongr]

  rw [
    Real.fourierInv_eq,
    Real.fourierInv_eq,
    Real.fourierInv_eq
  ]

  simp only [smul_sub]

  exact
    integral_sub
      hFIntegrand
      hGIntegrand

/-- Taking real parts preserves exact subtraction-linearity. -/
theorem h3SpectralScalarRealC1Representative_sub
    (F G : H3SpectralScalarState) :
    h3SpectralScalarRealC1Representative (F - G)
      =
    fun x : H3FourierPoint3 =>
      h3SpectralScalarRealC1Representative F x
        -
      h3SpectralScalarRealC1Representative G x := by
  funext x

  unfold h3SpectralScalarRealC1Representative

  rw [
    h3SpectralScalarC1Representative_sub
      F G
  ]

  rfl

/-- The actual real representative on the project's `Point3` carrier is
exactly subtraction-linear. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_sub
    (F G : H3SpectralScalarState) :
    h3SpectralScalarRealC1RepresentativeOnPoint3 (F - G)
      =
    fun x : Point3 =>
      h3SpectralScalarRealC1RepresentativeOnPoint3 F x
        -
      h3SpectralScalarRealC1RepresentativeOnPoint3 G x := by
  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      (F - G),
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      F,
    h3SpectralScalarRealC1RepresentativeOnPoint3_eq_comp
      G,
    h3SpectralScalarRealC1Representative_sub
      F G
  ]

  rfl

/-! ## Ordered third partials respect subtraction -/

/-- For spatially `C³` real scalar fields, every ordered third coordinate
partial respects subtraction.

This is proved through the already-compiled exact third-partial/Fréchet bridge
and Mathlib's subtraction formula for `iteratedFDeriv`; no mixed-partial
permutation is introduced. -/
theorem SpatialC3.spatial_d_three_sub
    {dim : Depth}
    {f g : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f)
    (hg : SpatialC3 g)
    (x : PrimeTensor.Point ℝ dim)
    (a b c : PrimeTensor.Axis dim) :
    (spatial dim).d a
        ((spatial dim).d b
          ((spatial dim).d c
            (fun y => f y - g y)))
        x
      =
    (spatial dim).d a
        ((spatial dim).d b
          ((spatial dim).d c f))
        x
      -
    (spatial dim).d a
        ((spatial dim).d b
          ((spatial dim).d c g))
        x := by
  have hSub : SpatialC3 (fun y => f y - g y) := by
    unfold SpatialC3 at hf hg ⊢
    exact hf.sub hg

  let m : Fin 3 → PrimeTensor.Point ℝ dim :=
    ![axisDirection a, axisDirection b, axisDirection c]

  rw [
    hSub.spatial_d_three_eq_iteratedFDeriv_three_axes
      x a b c,
    hf.spatial_d_three_eq_iteratedFDeriv_three_axes
      x a b c,
    hg.spatial_d_three_eq_iteratedFDeriv_three_axes
      x a b c
  ]

  have hfCont : ContDiff ℝ 3 f := by
    exact hf

  have hgCont : ContDiff ℝ 3 g := by
    exact hg

  have hIter :=
    iteratedFDeriv_sub_apply
      (𝕜 := ℝ)
      (i := 3)
      (x := x)
      hfCont.contDiffAt
      hgCont.contDiffAt

  have hEval :=
    congrArg
      (fun T =>
        T
          (![axisDirection a, axisDirection b, axisDirection c] :
            Fin 3 → PrimeTensor.Point ℝ dim))
      hIter

  change
    (iteratedFDeriv ℝ 3 (f - g) x)
        (![axisDirection a, axisDirection b, axisDirection c] :
          Fin 3 → PrimeTensor.Point ℝ dim)
      =
    (iteratedFDeriv ℝ 3 f x)
        (![axisDirection a, axisDirection b, axisDirection c] :
          Fin 3 → PrimeTensor.Point ℝ dim)
      -
    (iteratedFDeriv ℝ 3 g x)
        (![axisDirection a, axisDirection b, axisDirection c] :
          Fin 3 → PrimeTensor.Point ℝ dim)

  exact hEval

/-! ## Selected scalar third-jet continuity -/

/-- Every ordered third spatial partial of every selected scalar coordinate is
time-continuous at every strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_thirdPartial_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a b c : PrimeTensor.Axis Depth.three) :
    ContinuousAt
      (fun r : ℝ =>
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ r i))))
          x)
      s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let J : ℝ → ℝ :=
    fun r =>
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r i))))
        x

  have hDifference :
      Tendsto
        (fun r : ℝ =>
          ‖spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W r i - W s i))))
            x‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_thirdPartial_difference_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i x a b c

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i - W s i))))
          x‖
          =
        ‖J r - J s‖ := by
    filter_upwards [hInterval] with r hr

    have hrThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hr.1 hr.2.le i

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

    have hrC3 :
        SpatialC3
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i)) := by
      unfold SpatialC3
      exact
        h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_three_of_cubic
          (W r i)
          hrThree

    have hsC3 :
        SpatialC3
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i)) := by
      unfold SpatialC3
      exact
        h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_three_of_cubic
          (W s i)
          hsThree

    rw [
      h3SpectralScalarRealC1RepresentativeOnPoint3_sub
        (W r i)
        (W s i)
    ]

    have hThirdSub :=
      hrC3.spatial_d_three_sub
        hsC3
        x a b c

    change
      ‖(spatial Depth.three).d a
          ((spatial Depth.three).d b
            ((spatial Depth.three).d c
              (fun y : Point3 =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W r i) y
                  -
                h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W s i) y)))
          x‖
        =
      ‖(spatial Depth.three).d a
          ((spatial Depth.three).d b
            ((spatial Depth.three).d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i))))
          x
          -
        (spatial Depth.three).d a
          ((spatial Depth.three).d b
            ((spatial Depth.three).d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W s i))))
          x‖

    exact congrArg norm hThirdSub

  have hNormSub :
      Tendsto
        (fun r : ℝ => ‖J r - J s‖)
        (𝓝 s)
        (𝓝 0) :=
    hDifference.congr' hEventuallyEq

  have hJ :
      Tendsto
        J
        (𝓝 s)
        (𝓝 (J s)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε

    have hEventuallyNormDist :
        ∀ᶠ r in 𝓝 s,
          dist (‖J r - J s‖) (0 : ℝ) < ε :=
      (Metric.tendsto_nhds.mp hNormSub) ε hε

    filter_upwards [hEventuallyNormDist] with r hr

    simpa [
      Real.dist_eq,
      Real.norm_eq_abs
    ] using hr

  change
    Tendsto
      (fun r : ℝ =>
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ r i))))
          x)
      (𝓝 s)
      (𝓝
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s i))))
          x))

  simpa only [J, W] using hJ

end
end Euclidean
end Bridge
end PrimeTensor
