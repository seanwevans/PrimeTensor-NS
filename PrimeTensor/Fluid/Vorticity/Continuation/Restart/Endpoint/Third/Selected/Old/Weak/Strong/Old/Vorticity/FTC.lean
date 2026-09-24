import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Vorticity.Fubini
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.FTC

/-!
# Endpoint-independent old vorticity weak FTC

The heavy one-dimensional FTC arguments in the endpoint-era `FTC` file are
already endpoint-independent:

* compact testing of each vorticity slice is spatially integrable;
* the compactly tested old-vorticity trajectory satisfies pointwise FTC,
  provided the temporal derivative is integrable on the shortened interval.

The endpoint hypothesis entered only through:

* the Fubini interchange;
* product-space integrability used to obtain a.e. temporal slice
  integrability.

Both inputs now follow directly from `CanonicalH3TailDataFrom`.

This file therefore closes the x/y/z weak-vorticity pairing increment
identities with no
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed` assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVorticityFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldVorticityFTC :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The time integral of the compactly tested x-vorticity temporal derivative
is exactly the increment of the old x-vorticity weak pairing, directly from
the canonical H³ tail. -/
theorem intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_eq_pairing_sub_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    h3PreterminalTailCanonicalWeakVorticityXPairingOnElapsed
        (u := u) (t := t) ψ q
      -
    h3PreterminalTailCanonicalWeakVorticityXPairingOnElapsed
        (u := u) (t := t) ψ
        (h3EndpointElapsedZero q) := by
  have hSwap :=
    intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_swap_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  have hSlices :=
    hShort.1.prod_left_ae

  rw [hSwap]

  have hFTCae :
      ∀ᵐ x : Point3 ∂volume,
        (∫ r in (0 : ℝ)..(q : ℝ),
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
          =
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityX
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x)
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityX
              (logSpaceTimeVectorField u)
              t
              x) := by
    filter_upwards [hSlices] with x hx
    exact
      intervalIntegral_h3LoggedPreterminalVorticityXTemporalDerivative_eq_sub
        hNS ht hEnd ψ q x hx

  rw [integral_congr_ae hFTCae]

  have hQ :=
    h3PreterminalTailCanonical_test_mul_realVorticityX_integrable
      hNS ht hEnd hTail ψ q

  have h0Raw :=
    h3PreterminalTailCanonical_test_mul_realVorticityX_integrable
      hNS ht hEnd hTail ψ
      (h3EndpointElapsedZero q)

  have h0 :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityX
              (logSpaceTimeVectorField u)
              t
              x))
        (volume : Measure Point3) := by
    simpa only [
      h3EndpointElapsedZero_coe,
      add_zero
    ] using h0Raw

  rw [integral_sub hQ h0]

  unfold h3PreterminalTailCanonicalWeakVorticityXPairingOnElapsed
  simp only [
    h3EndpointElapsedZero_coe,
    add_zero
  ]

/-- The time integral of the compactly tested y-vorticity temporal derivative
is exactly the increment of the old y-vorticity weak pairing, directly from
the canonical H³ tail. -/
theorem intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_eq_pairing_sub_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
        (u := u) (t := t) ψ q
      -
    h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
        (u := u) (t := t) ψ
        (h3EndpointElapsedZero q) := by
  have hSwap :=
    intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_swap_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  have hSlices :=
    hShort.2.1.prod_left_ae

  rw [hSwap]

  have hFTCae :
      ∀ᵐ x : Point3 ∂volume,
        (∫ r in (0 : ℝ)..(q : ℝ),
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
          =
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityY
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x)
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityY
              (logSpaceTimeVectorField u)
              t
              x) := by
    filter_upwards [hSlices] with x hx
    exact
      intervalIntegral_h3LoggedPreterminalVorticityYTemporalDerivative_eq_sub
        hNS ht hEnd ψ q x hx

  rw [integral_congr_ae hFTCae]

  have hQ :=
    h3PreterminalTailCanonical_test_mul_realVorticityY_integrable
      hNS ht hEnd hTail ψ q

  have h0Raw :=
    h3PreterminalTailCanonical_test_mul_realVorticityY_integrable
      hNS ht hEnd hTail ψ
      (h3EndpointElapsedZero q)

  have h0 :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityY
              (logSpaceTimeVectorField u)
              t
              x))
        (volume : Measure Point3) := by
    simpa only [
      h3EndpointElapsedZero_coe,
      add_zero
    ] using h0Raw

  rw [integral_sub hQ h0]

  unfold h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
  simp only [
    h3EndpointElapsedZero_coe,
    add_zero
  ]

/-- The time integral of the compactly tested z-vorticity temporal derivative
is exactly the increment of the old z-vorticity weak pairing, directly from
the canonical H³ tail. -/
theorem intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_eq_pairing_sub_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    h3PreterminalTailCanonicalWeakVorticityZPairingOnElapsed
        (u := u) (t := t) ψ q
      -
    h3PreterminalTailCanonicalWeakVorticityZPairingOnElapsed
        (u := u) (t := t) ψ
        (h3EndpointElapsedZero q) := by
  have hSwap :=
    intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_swap_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  have hSlices :=
    hShort.2.2.prod_left_ae

  rw [hSwap]

  have hFTCae :
      ∀ᵐ x : Point3 ∂volume,
        (∫ r in (0 : ℝ)..(q : ℝ),
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x))
          =
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityZ
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x)
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityZ
              (logSpaceTimeVectorField u)
              t
              x) := by
    filter_upwards [hSlices] with x hx
    exact
      intervalIntegral_h3LoggedPreterminalVorticityZTemporalDerivative_eq_sub
        hNS ht hEnd ψ q x hx

  rw [integral_congr_ae hFTCae]

  have hQ :=
    h3PreterminalTailCanonical_test_mul_realVorticityZ_integrable
      hNS ht hEnd hTail ψ q

  have h0Raw :=
    h3PreterminalTailCanonical_test_mul_realVorticityZ_integrable
      hNS ht hEnd hTail ψ
      (h3EndpointElapsedZero q)

  have h0 :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (realVorticityZ
              (logSpaceTimeVectorField u)
              t
              x))
        (volume : Measure Point3) := by
    simpa only [
      h3EndpointElapsedZero_coe,
      add_zero
    ] using h0Raw

  rw [integral_sub hQ h0]

  unfold h3PreterminalTailCanonicalWeakVorticityZPairingOnElapsed
  simp only [
    h3EndpointElapsedZero_coe,
    add_zero
  ]

end

end Euclidean
end Bridge
end PrimeTensor
