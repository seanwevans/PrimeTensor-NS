import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalFirstFrechetTimeDerivativeCandidateContinuity

/-!
# Classicalization: continuity of the actual canonical first-Fréchet time derivative

The canonical reconstruction now has both ingredients needed to close the
ordinary first-spatial-derivative time regularity:

* an exact `HasDerivAt` formula at every strict positive interior restart time;
* continuity of the explicit Navier--Stokes derivative candidate.

This file transfers candidate continuity to the actual one-dimensional
`deriv`, exactly as in the older selected-representative chain, but now stated
entirely for the explicit canonical inverse-Fourier reconstruction.

On `(0,R)`, the canonical derivative formula holds pointwise.  Hence the
candidate is eventually equal to the actual derivative near any strict
interior base time.  Rewriting the derivative value at the base point by the
same formula and applying `ContinuousAt.congr'` closes continuity of the
actual derivative.

No new estimate, limit, or derivative interchange is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalFirstFrechetDerivTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The actual ordinary time derivative of one fixed coordinate evaluation of
the canonical selected first spatial Fréchet derivative is continuous at every
strict positive interior restart time. -/
theorem deriv_h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    ContinuousAt
      (deriv
        (fun r : ℝ =>
          (fderiv ℝ
              (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
                hν U₀ hA hU₀ r i)
              x) ea))
      s := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let f : ℝ → ℂ :=
    fun r =>
      (fderiv ℝ
          (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
            hν U₀ hA hU₀ r i)
          x) ea

  let G : ℝ → ℂ :=
    fun r =>
      (ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
                hν U₀ hA hU₀ r i)
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i)
          x) ea

  have hCandidate :
      ContinuousAt G s := by
    dsimp only [G, W, ea]
    exact
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_timeDerivativeCandidate_continuousAt
        hν U₀ hA hU₀ hs hsR i a x

  have hAt :
      deriv f s = G s := by
    have hDeriv :=
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ hs hsR i a x
    dsimp only at hDeriv
    dsimp only [f, G, W, ea]
    exact HasDerivAt.deriv hDeriv

  have hWindow :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 s := by
    apply Ioo_mem_nhds
    · exact hs
    · simpa only [R] using hsR

  have hEventuallyEq :
      G =ᶠ[𝓝 s] deriv f := by
    filter_upwards [hWindow] with r hr

    have hDeriv :=
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ hr.1
        (by
          simpa only [R] using hr.2)
        i a x

    dsimp only at hDeriv
    have hEq := HasDerivAt.deriv hDeriv

    dsimp only [f, G, W, ea]
    exact hEq.symm

  change
    Tendsto
      (deriv f)
      (𝓝 s)
      (𝓝 (deriv f s))

  rw [hAt]

  exact hCandidate.congr' hEventuallyEq

end

end Euclidean
end Bridge
end PrimeTensor
