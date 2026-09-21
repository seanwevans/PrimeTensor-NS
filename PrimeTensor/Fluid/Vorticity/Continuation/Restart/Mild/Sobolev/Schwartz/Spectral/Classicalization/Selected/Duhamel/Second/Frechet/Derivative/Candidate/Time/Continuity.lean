import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fourth.Frechet.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Second.Frechet.Time.Continuity

/-!
# Classicalization: selected Duhamel second-Fréchet derivative candidate continuity

The selected Duhamel second-Fréchet right derivative has candidate

    ν * Σ_k D⁴D(t,x)[e_a,e_b,e_k,e_k]
      + D²N(W(t),W(t))(x)[e_a,e_b].

The fourth-order Duhamel jet is now time-continuous for every fixed ordered
canonical-coordinate evaluation, and the instantaneous forcing Hessian is
already time-continuous.

This file packages those facts into continuity of the complete order-two
Duhamel time-derivative candidate.  The diagonal fourth-order trace is only a
finite sum over the three spatial axes.

No new estimate, quotient argument, or mixed-derivative interchange is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetDerivativeCandidateTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

attribute [local instance 1100] NormedSpace.complexToReal

/-- For fixed leading coordinate directions `a,b`, the diagonal trace in the
last two slots of the selected Duhamel fourth spatial Fréchet derivative is
time-continuous at every strict positive interior restart time. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_fourthFrechet_ab_diagonalTrace_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        ∑ k : Fin 3,
          iteratedFDeriv ℝ 4
            (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν r W W i)
            x
            ![
              h3FourierAxisDirection (h3AxisOfFin3 a),
              h3FourierAxisDirection (h3AxisOfFin3 b),
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ])
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hdiag
      (k : Fin 3) :
      ContinuousAt
        (fun r : ℝ =>
          iteratedFDeriv ℝ 4
            (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν r W W i)
            x
            ![
              h3FourierAxisDirection (h3AxisOfFin3 a),
              h3FourierAxisDirection (h3AxisOfFin3 b),
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ])
        s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_fourthFrechet_coordinate_eval_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a b k k x

  have hsum :
      ContinuousAt
        (fun r : ℝ =>
          iteratedFDeriv ℝ 4
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν r W W i)
              x
              ![
                h3FourierAxisDirection (h3AxisOfFin3 a),
                h3FourierAxisDirection (h3AxisOfFin3 b),
                h3FourierAxisDirection (h3AxisOfFin3 (0 : Fin 3)),
                h3FourierAxisDirection (h3AxisOfFin3 (0 : Fin 3))
              ]
            +
          iteratedFDeriv ℝ 4
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν r W W i)
              x
              ![
                h3FourierAxisDirection (h3AxisOfFin3 a),
                h3FourierAxisDirection (h3AxisOfFin3 b),
                h3FourierAxisDirection (h3AxisOfFin3 (1 : Fin 3)),
                h3FourierAxisDirection (h3AxisOfFin3 (1 : Fin 3))
              ]
            +
          iteratedFDeriv ℝ 4
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν r W W i)
              x
              ![
                h3FourierAxisDirection (h3AxisOfFin3 a),
                h3FourierAxisDirection (h3AxisOfFin3 b),
                h3FourierAxisDirection (h3AxisOfFin3 (2 : Fin 3)),
                h3FourierAxisDirection (h3AxisOfFin3 (2 : Fin 3))
              ])
        s := by
    exact
      ((hdiag (0 : Fin 3)).add
        (hdiag (1 : Fin 3))).add
          (hdiag (2 : Fin 3))

  simpa only [Fin.sum_univ_three] using hsum

/-- The complete candidate for the ordinary time derivative of one ordered
canonical-coordinate evaluation of the selected Duhamel second spatial
Fréchet derivative is time-continuous. -/
theorem h3SelectedDuhamel_C1_secondFrechet_coordinate_derivativeCandidate_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    ContinuousAt
      (fun r : ℝ =>
        (ν : ℂ) *
            (∑ k : Fin 3,
              iteratedFDeriv ℝ 4
                (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                  ν r W W i)
                x
                ![
                  ea,
                  eb,
                  h3FourierAxisDirection (h3AxisOfFin3 k),
                  h3FourierAxisDirection (h3AxisOfFin3 k)
                ])
          +
        iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i)
          x
          ![ea, eb])
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let T : ℝ → ℂ :=
    fun r =>
      ∑ k : Fin 3,
        iteratedFDeriv ℝ 4
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν r W W i)
          x
          ![
            ea,
            eb,
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]

  let F : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W r) (W r) i)
        x
        ![ea, eb]

  have hTrace :
      ContinuousAt T s := by
    dsimp only [T, W, ea, eb]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_fourthFrechet_ab_diagonalTrace_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a b x

  have hViscous :
      ContinuousAt
        (fun r : ℝ => (ν : ℂ) * T r)
        s := by
    exact continuousAt_const.mul hTrace

  have hForcing :
      ContinuousAt F s := by
    dsimp only [F, W, ea, eb]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_secondFrechet_coordinate_continuousAt_time
        hν U₀ hA hU₀ hs hsR i a b x

  change
    ContinuousAt
      (fun r : ℝ =>
        (ν : ℂ) * T r + F r)
      s

  exact hViscous.add hForcing

end

end Euclidean
end Bridge
end PrimeTensor
