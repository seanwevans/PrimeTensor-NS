import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalFirstFrechetTimeDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityFirstFrechetTimeDerivativeCandidateContinuity

/-!
# Classicalization: continuity of the canonical first-Fréchet time-derivative candidate

The explicit canonical reconstruction now has the same ordinary time
derivative formula as the generic selected H³ representative for every fixed
coordinate evaluation of its first spatial Fréchet derivative.

The pre-existing selected classicalization stack also proves that the
coefficient in that formula is continuous in time:

    ν Σ_k D³u[e_a,e_k,e_k] - D_a N.

This file transports that continuity to the canonical reconstruction.

At every strict positive interior base time, the open restart interval is a
neighborhood.  On that neighborhood the generic H³ `C¹` representative and
the canonical inverse-Fourier reconstruction are exactly equal.  Rewriting
their third spatial Fréchet derivatives through that local equality gives an
eventual equality between the old derivative candidate and the canonical one.

Continuity is then transferred with `ContinuousAt.congr'`.  No new estimate,
limit, or derivative interchange is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalFirstFrechetTimeDerivativeCandidateContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The Navier--Stokes time-derivative coefficient for one fixed coordinate
evaluation of the canonical selected first spatial Fréchet derivative is
continuous at every strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_timeDerivativeCandidate_continuousAt
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
      (fun r : ℝ =>
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
            x) ea)
      s := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Wold : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  have hBridge :
      W = Wold := by
    dsimp only [W, Wold]
    exact
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_eq_mildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hOld :
      ContinuousAt
        (fun r : ℝ =>
          (ν : ℂ) *
              (∑ k : Fin 3,
                iteratedFDeriv ℝ 3
                  (h3SpectralScalarC1Representative
                    (Wold r i))
                  x
                  ![
                    ea,
                    h3FourierAxisDirection (h3AxisOfFin3 k),
                    h3FourierAxisDirection (h3AxisOfFin3 k)
                  ])
            -
          (fderiv ℝ
              (h3RawFinLerayOuterProductDivergenceC0Representative
                (Wold r) (Wold r) i)
              x) ea)
        s := by
    dsimp only [Wold, ea]
    exact
      h3SelectedVelocity_C1_fderiv_coordinate_timeDerivativeCandidate_continuousAt
        hν U₀ hA hU₀ hs hsR i a x

  rw [← hBridge] at hOld

  have hWindow :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 s := by
    exact
      IsOpen.mem_nhds isOpen_Ioo
        ⟨hs, by simpa only [R] using hsR⟩

  have hEventuallyEq :
      (fun r : ℝ =>
        (ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3SpectralScalarC1Representative
                  (W r i))
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
            x) ea)
        =ᶠ[𝓝 s]
      (fun r : ℝ =>
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
            x) ea) := by
    filter_upwards [hWindow] with r hr

    have hCanonical :
        h3SpectralScalarC1Representative (W r i)
          =
        h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
          hν U₀ hA hU₀ r i := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_C1Representative_eq_canonical
          hν U₀ hA hU₀ hr.1
          (by simpa only [R] using hr.2.le)
          i

    rw [hCanonical]

  have hAt :
      (ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3SpectralScalarC1Representative
                  (W s i))
                x
                ![
                  ea,
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          -
        (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W s) (W s) i)
            x) ea
        =
      (ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
                  hν U₀ hA hU₀ s i)
                x
                ![
                  ea,
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          -
        (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W s) (W s) i)
            x) ea := by
    have hCanonical :
        h3SpectralScalarC1Representative (W s i)
          =
        h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
          hν U₀ hA hU₀ s i := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_C1Representative_eq_canonical
          hν U₀ hA hU₀ hs hsR.le i

    rw [hCanonical]

  have hCanonicalCandidate :=
    hOld.congr' hEventuallyEq

  change
    Tendsto
      (fun r : ℝ =>
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
            x) ea)
      (𝓝 s)
      (𝓝
        ((ν : ℂ) *
              (∑ k : Fin 3,
                iteratedFDeriv ℝ 3
                  (h3SpectralScalarC1Representative
                    (W s i))
                  x
                  ![
                    ea,
                    h3FourierAxisDirection (h3AxisOfFin3 k),
                    h3FourierAxisDirection (h3AxisOfFin3 k)
                  ])
            -
          (fderiv ℝ
              (h3RawFinLerayOuterProductDivergenceC0Representative
                (W s) (W s) i)
              x) ea))
    at hCanonicalCandidate

  rw [hAt] at hCanonicalCandidate

  dsimp only [W, ea] at hCanonicalCandidate ⊢
  exact hCanonicalCandidate

end

end Euclidean
end Bridge
end PrimeTensor
