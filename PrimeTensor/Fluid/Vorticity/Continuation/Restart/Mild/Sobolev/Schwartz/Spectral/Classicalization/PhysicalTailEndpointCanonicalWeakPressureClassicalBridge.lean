import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalWeakPressureAnnihilation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Classicalization: classical pressure gradient equals the weak gradient pairing

`PhysicalTailEndpointCanonicalWeakPressureAnnihilation` proves that the
distributional gradient of the endpoint scalar pressure defect annihilates
every compactly supported smooth divergence-free test vector.

The pointwise endpoint momentum equation, however, contains the ordinary
classical derivatives

    spatial3.d i q.

This file closes that representation seam.

For every spatially `C¹` scalar field `q`, every coordinate axis `i`, and every
compactly supported smooth scalar test function `φ`, Mathlib's multivariate
line-derivative integration-by-parts theorem gives

    (∂ᵢ T_q)(φ)
      =
    ∫ φ(x) ∂ᵢq(x) dx,

where `T_q` is PrimeTensor's function-induced ordinary distribution from the
previous file.

The proof needs no global integrability of `q` or `∂ᵢq`: continuity gives local
integrability, while compact support of `φ` and its derivative makes all three
products required by integration by parts globally integrable.

Specializing to the endpoint pressure defect turns the distributional
annihilation theorem into the classical weak identity

    Σᵢ ∫ φᵢ ∂ᵢq = 0

for every divergence-free test vector.

No Fourier transform of the old pressure is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakPressureClassicalBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakPressureClassicalBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A coordinate derivative of a spatially `C¹` scalar field is continuous.

This is the local version needed to make the derivative locally integrable in
the compactly-supported integration-by-parts argument. -/
theorem h3SpatialC1_spatial3_d_continuous_weakPressure
    {q : ScalarField3}
    (hq : SpatialC1 q)
    (a : PrimeTensor.Axis Depth.three) :
    Continuous (spatial3.d a q) := by
  have hfun :
      (fun x : Point3 =>
        spatial3.d a q x)
        =
      (fun x : Point3 =>
        (fderiv ℝ q x) (axisDirection a)) := by
    funext x
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
        hq x a

  change
    Continuous
      (fun x : Point3 =>
        spatial3.d a q x)

  rw [hfun]

  have hqC1 :
      ContDiff ℝ 1 q := by
    simpa only [SpatialC1] using hq

  have hfd :
      ContDiff ℝ 0 (fderiv ℝ q) :=
    hqC1.fderiv_right (by norm_num)

  exact
    (hfd.clm_apply contDiff_const).continuous

/-- For a `C¹` scalar field, the ordinary distributional coordinate derivative
pairs with a test function exactly as integration against the classical
coordinate derivative.

The distribution constructor is the compatibility wrapper introduced in
`PhysicalTailEndpointCanonicalWeakPressureAnnihilation`; unlike newer Mathlib
revisions, PrimeTensor's pinned revision does not yet expose
`Distribution.ofFun`. -/
theorem h3WeakDistributionOfFun_lineDeriv_apply_eq_integral_spatial3_d
    {q : ScalarField3}
    (hq : SpatialC1 q)
    (a : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    (((Distribution.lineDerivCLM
      (axisDirection a) :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun q))
      φ)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d a q x)
      ∂volume := by
  let v : Point3 :=
    axisDirection a

  let dφ : H3WeakTestFunction :=
    (TestFunction.lineDerivCLM
      ℝ v :
        H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
      φ

  let dq : Point3 → ℝ :=
    spatial3.d a q

  have hqLocal :
      LocallyIntegrable
        q
        (volume : Measure Point3) :=
    hq.continuous.locallyIntegrable

  have hqLocalOn :
      LocallyIntegrableOn
        q
        Set.univ
        (volume : Measure Point3) :=
    hqLocal.locallyIntegrableOn Set.univ

  have hdqContinuous :
      Continuous dq := by
    dsimp only [dq]
    exact
      h3SpatialC1_spatial3_d_continuous_weakPressure
        hq a

  have hdqLocal :
      LocallyIntegrable
        dq
        (volume : Measure Point3) :=
    hdqContinuous.locallyIntegrable

  have hdqLocalOn :
      LocallyIntegrableOn
        dq
        Set.univ
        (volume : Measure Point3) :=
    hdqLocal.locallyIntegrableOn Set.univ

  have hDφq :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (dφ x)
            (q x))
        (volume : Measure Point3) := by
    exact
      dφ.integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        hqLocalOn

  have hφdq :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            (dq x))
        (volume : Measure Point3) := by
    exact
      φ.integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        hdqLocalOn

  have hφq :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            (q x))
        (volume : Measure Point3) := by
    exact
      φ.integrable_bilin
        (ContinuousLinearMap.lsmul ℝ ℝ)
        hqLocalOn

  have hφLine
      (x : Point3) :
      HasLineDerivAt ℝ
        (φ : Point3 → ℝ)
        (dφ x)
        x v := by
    have hDiff :
        DifferentiableAt ℝ
          (φ : Point3 → ℝ)
          x :=
      (φ.contDiff.differentiable (by simp)).differentiableAt

    have hLine :=
      hDiff.hasFDerivAt.hasLineDerivAt v

    have hdφLine :
        dφ x
          =
        lineDeriv ℝ
          (φ : Point3 → ℝ)
          x v := by
      dsimp only [dφ]
      exact
        TestFunction.lineDerivCLM_apply_of_le
          (𝕜 := ℝ)
          (f := φ)
          (v := v)
          (x := x)
          (by simp)

    have hdφValue :
        dφ x
          =
        (fderiv ℝ
          (φ : Point3 → ℝ)
          x) v := by
      rw [hdφLine]
      exact hDiff.lineDeriv_eq_fderiv

    rw [hdφValue]
    exact hLine

  have hqLine
      (x : Point3) :
      HasLineDerivAt ℝ
        q
        (dq x)
        x v := by
    have hDiff :
        DifferentiableAt ℝ q x :=
      (hq.differentiable_one).differentiableAt

    have hLine :=
      hDiff.hasFDerivAt.hasLineDerivAt v

    have hValue :
        (fderiv ℝ q x) v
          =
        dq x := by
      dsimp only [v, dq]
      exact
        (PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
          hq x a).symm

    simpa only [hValue] using hLine

  have hIBP :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (dq x)
        ∂volume)
        =
      -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (dφ x)
          (q x)
        ∂volume := by
    exact
      integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        hDφq
        hφdq
        hφq
        (fun x _ => hφLine x)
        (fun x _ => hqLine x)

  have hT_dφ :
      h3WeakDistributionOfFun q dφ
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (dφ x)
          (q x)
        ∂volume := by
    unfold h3WeakDistributionOfFun
    exact
      TestFunction.integralAgainstBilinCLM_eq_integral
        hqLocalOn

  change
    (((Distribution.lineDerivCLM
      v :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun q))
      φ)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (dq x)
      ∂volume

  rw [Distribution.lineDerivCLM_apply]
  rw [show
    (TestFunction.lineDerivCLM
      ℝ v :
        H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
      φ
      =
    dφ by rfl]
  rw [hT_dφ]

  exact hIBP.symm

/-- The ordinary classical gradient of the endpoint scalar pressure defect
annihilates every compactly supported smooth divergence-free test vector.

This is the concrete weak pressure-elimination identity needed by the next
endpoint projected-momentum step. -/
theorem h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_classicalGradient_pairing_eq_zero
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
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 i)
            (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint s)
            x)
        ∂volume
      =
    0 := by
  let q : ScalarField3 :=
    h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint s

  have hqC1 :
      SpatialC1 q := by
    simpa only [q] using
      h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_spatialC1
        hNS ht htau hEnd hE hTail hEndpoint hs

  have hDist :
      ∑ i : Fin 3,
        (((Distribution.lineDerivCLM
          (axisDirection (h3AxisOfFin3 i)) :
            H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
          (h3WeakDistributionOfFun q))
          (φ i))
        =
      0 := by
    simpa only [q] using
      h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_distributionGradient_pairing_eq_zero
        hNS ht htau hEnd hE hTail hEndpoint hs φ hφ

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 i)
            q
            x)
        ∂volume)
        =
      ∑ i : Fin 3,
        (((Distribution.lineDerivCLM
          (axisDirection (h3AxisOfFin3 i)) :
            H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
          (h3WeakDistributionOfFun q))
          (φ i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      exact
        h3WeakDistributionOfFun_lineDeriv_apply_eq_integral_spatial3_d
          hqC1
          (h3AxisOfFin3 i)
          (φ i)
    _ = 0 :=
      hDist

end

end Euclidean
end Bridge
end PrimeTensor
