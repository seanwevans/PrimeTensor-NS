import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalClassicalMild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityFirstFrechetTimeDerivative

/-!
# Classicalization: time derivative of the canonical first spatial derivative

The canonical raw Fourier route now meets the existing classical
heat-minus-Duhamel route at an exact pointwise spatial `C¹` representative.

The selected classicalization stack already proves an ordinary time derivative
for every fixed coordinate evaluation of the first spatial Fréchet derivative
of the generic H³ representative:

    d/dt D_a u
      =
    ν Σ_k D³u[e_a,e_k,e_k] - D_a N.

This file transports that theorem to the explicit canonical reconstruction.

The key point is local rather than global.  At a strict positive interior time
`t`, the open restart interval `(0,R)` is a neighborhood of `t`.  On that whole
neighborhood the generic H³ representative is exactly the canonical
inverse-Fourier reconstruction.  Therefore their fixed spatial derivative
evaluations are eventually equal at `t`, and
`HasDerivAt.congr_of_eventuallyEq` transports the already-proved time
derivative.

The coefficient at the base time is also rewritten through the exact
representative equality, so the resulting theorem is stated entirely with the
canonical spatial reconstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalFirstFrechetTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, one fixed coordinate
evaluation of the first spatial Fréchet derivative of the explicit canonical
selected reconstruction has the Navier--Stokes time derivative coefficient. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_fderiv_coordinate_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    HasDerivAt
      (fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
              hν U₀ hA hU₀ r i)
            x) ea)
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
                hν U₀ hA hU₀ t i)
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x) ea)
      t := by
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
      HasDerivAt
        (fun r : ℝ =>
          (fderiv ℝ
              (h3SpectralScalarC1Representative
                (Wold r i))
              x) ea)
        ((ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3SpectralScalarC1Representative
                  (Wold t i))
                x
                ![
                  ea,
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          -
        (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (Wold t) (Wold t) i)
            x) ea)
        t := by
    dsimp only [Wold, ea]
    exact
      h3SelectedVelocity_C1_fderiv_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i a x

  rw [← hBridge] at hOld

  have hCanonicalAt :
      h3SpectralScalarC1Representative (W t i)
        =
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
        hν U₀ hA hU₀ t i := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_C1Representative_eq_canonical
        hν U₀ hA hU₀ ht htR.le i

  rw [hCanonicalAt] at hOld

  have hInterior :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 t := by
    exact
      IsOpen.mem_nhds isOpen_Ioo
        ⟨ht, by simpa only [R] using htR⟩

  have hPathEq :
      (fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
              hν U₀ hA hU₀ r i)
            x) ea)
        =ᶠ[𝓝 t]
      (fun r : ℝ =>
        (fderiv ℝ
            (h3SpectralScalarC1Representative
              (W r i))
            x) ea) := by
    filter_upwards [hInterior] with r hr

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

    exact
      congrArg
        (fun f : H3FourierPoint3 → ℂ =>
          (fderiv ℝ f x) ea)
        hCanonical.symm

  have hCanonicalDerivative :
      HasDerivAt
        (fun r : ℝ =>
          (fderiv ℝ
              (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
                hν U₀ hA hU₀ r i)
              x) ea)
        ((ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
                  hν U₀ hA hU₀ t i)
                x
                ![
                  ea,
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          -
        (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x) ea)
        t :=
    hOld.congr_of_eventuallyEq hPathEq

  dsimp only [W, ea] at hCanonicalDerivative ⊢
  exact hCanonicalDerivative

end

end Euclidean
end Bridge
end PrimeTensor
