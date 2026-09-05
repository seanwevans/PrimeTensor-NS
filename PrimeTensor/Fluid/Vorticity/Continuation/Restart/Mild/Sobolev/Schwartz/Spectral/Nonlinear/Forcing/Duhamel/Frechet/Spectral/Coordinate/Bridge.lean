import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.F.Deriv.Coordinate.CLM
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Intertwining
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Assembly
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Spectral H³ coordinate evaluation of one positive-lag Duhamel kernel

The H³-valued Duhamel integral is built from the existing spectral
heat--Leray nonlinear kernel

    h3SpectralFinHeatLerayVelocityApply ν τ U V i.

For the fresh first-Fréchet quotient we need to commute one fixed spatial
coordinate derivative evaluation through that Bochner integral.  The
continuous linear functional accomplishing the evaluation was packaged in
`H3.Real.C1.FDerivCoordinateCLM`.

This file identifies its value on one positive-lag spectral kernel with the
already-developed explicit classical first-derivative representative:

    Eval_{a,x}(HeatLerayVelocityApply ν τ U V i)
      =
    D_a H_τ N(U,V)_i(x).

The proof contains no new estimate.

* The canonical H³ `C¹` representative of the spectral kernel is a.e. equal
  to its complex `L²` decoder.
* The explicit positive-lag `C³` heat-forcing representative is a.e. equal to
  the same decoder.
* Both representatives are continuous, so positivity of Euclidean volume on
  nonempty open sets upgrades the a.e. identity to an exact function identity.
* The existing Fréchet assembly theorem then identifies its coordinate
  derivative with the explicit first-derivative representative.

This is the pointwise integrand bridge needed before commuting the continuous
linear functional through the source-time Bochner integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3FrechetSpectralCoordinateBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a strictly positive heat lag, coordinate derivative evaluation of the
actual spectral H³ heat--Leray kernel is exactly the explicit fixed-lag
first-derivative representative. -/
theorem h3SpectralScalarC1CoordinateDerivativeEvaluationCLM_heatLerayVelocityApply
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarC1CoordinateDerivativeEvaluationCLM a x
        (h3SpectralFinHeatLerayVelocityApply
          ν τ hν hτ U V i)
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
      ν τ U V i a x := by
  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayVelocityApply
      ν τ hν hτ U V i

  have hC1AE :
      h3SpectralScalarC1Representative G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((h3SpectralScalarDecodeComplexL2 G :
          H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) :=
    h3SpectralScalarC1Representative_ae_eq_decodeComplexL2 G

  have hC3AE :
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((h3SpectralScalarDecodeComplexL2 G :
          H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp only [G]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_heatLerayDecodeComplexL2
        hν hτ U V i

  have hEqAE :
      h3SpectralScalarC1Representative G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i :=
    hC1AE.trans hC3AE.symm

  have hC1Cont :
      Continuous
        (h3SpectralScalarC1Representative G) :=
    (h3SpectralScalarC1Representative_contDiff_one G).continuous

  have hC3Cont :
      Continuous
        (h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i) :=
    (h3RawFinLerayOuterProductDivergenceHeatC3Representative_contDiff_three
      hν hτ U V i).continuous

  have hEqFun :
      h3SpectralScalarC1Representative G
        =
      h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i :=
    MeasureTheory.Measure.eq_of_ae_eq hEqAE hC1Cont hC3Cont

  rw [
    h3SpectralScalarC1CoordinateDerivativeEvaluationCLM_apply
  ]

  change
    (fderiv ℝ
        (h3SpectralScalarC1Representative G)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
      ν τ U V i a x

  rw [hEqFun]

  have hFrechet :=
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
      hν hτ U V i x

  rw [← hFrechet]

  unfold
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative

  exact
    h3AssembleCoordinateDerivative_axis
      (fun j =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ U V i j x)
      a

end

end Euclidean
end Bridge
end PrimeTensor
