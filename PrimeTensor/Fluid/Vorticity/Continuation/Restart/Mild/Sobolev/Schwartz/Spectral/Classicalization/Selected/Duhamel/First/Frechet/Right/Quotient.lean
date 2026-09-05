import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.History.Generator.Trace
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Fresh.Spectral.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Right.Quotient.Split

/-!
# Classicalization: selected Duhamel first-Fréchet right quotient

The old-history and fresh pieces of the selected Duhamel first spatial
Fréchet difference quotient are now closed separately.

The history quotient converges to the viscosity-weighted third spatial trace,

    ν * Σ_k D³D(t,x)[e_a,e_k,e_k],

while the actual shifted spectral fresh quotient converges to the
instantaneous forcing derivative,

    D_a N(W(t),W(t))_i(x).

The exact positive-increment quotient split identifies the full first-Fréchet
difference quotient with the sum of those two pieces.  Adding the two
`Tendsto` statements and using that split eventually on the right
neighborhood of zero therefore closes the complete selected Duhamel
first-Fréchet right-quotient limit.

No estimate, reconstruction argument, or new differentiation step is
introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetRightQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The complete selected Duhamel first spatial Fréchet difference quotient
converges from the right to viscosity times the third spatial trace plus the
instantaneous forcing coordinate derivative. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamel_C1_fderiv_coordinate_zero_right
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
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          ((fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν (t + h) hν W W i))
              x) ea
            -
          (fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν W W i))
              x) ea))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        ((ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 3
                (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                  ν t W W i)
                x
                ![
                  ea,
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          +
        (fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x) ea)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  have hHistory :=
    tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_fderiv_coordinate_zero_right_eq_viscosity_thirdTrace
      hν U₀ hA hU₀ ht htR.le i a x

  have hFresh :=
    tendsto_inv_smul_h3SelectedDuhamelFresh_fderiv_coordinate_zero_right
      hν U₀ hA hU₀ ht htR i a x

  dsimp only at hHistory hFresh

  have hSum :=
    hHistory.add hFresh

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          ((fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν (t + h) hν W W i))
              x) ea
            -
          (fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν W W i))
              x) ea))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h⁻¹ •
            ((fderiv ℝ
                (h3SelectedDuhamelHistoryHeatRepresentative
                  ν A t h hν U₀ hA hU₀ ht i)
                x) ea
              -
            (fderiv ℝ
                (h3SpectralScalarC1Representative
                  (h3SpectralFinHeatLerayDuhamel
                    ν t hν W W i))
                x) ea)
          +
        h⁻¹ •
          ((fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν h hν
                  (fun r => W (r + t))
                  (fun r => W (r + t))
                  i))
              x) ea)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    dsimp only [W, ea]
    exact
      inv_smul_sub_h3SelectedDuhamel_firstFrechet_coordinate_eq_history_add_fresh
        hν U₀ hA hU₀ ht hh i a x

  exact
    Tendsto.congr'
      hEq.symm
      hSum

end

end Euclidean
end Bridge
end PrimeTensor
