import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Complex.Temporal.Derivative.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Classicalization: real selected temporal derivative regularity

The complex selected C1 representative is now temporally C1 on the whole
strict relative restart interval `(0,R)` in the derivative criterion form

    DifferentiableOn ℝ f (Ioo 0 R)
      ∧
    ContinuousOn (deriv f) (Ioo 0 R).

The selected physical velocity is obtained by taking the real part of that
complex representative coordinatewise.  Rather than manually differentiating
`Complex.re`, this file converts the complex criterion to `ContDiffOn ℝ 1`,
post-composes with the continuous linear map `Complex.reCLM`, and converts back
to the same derivative criterion.

No new estimate, analytic hypothesis, or frontier proposition is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealTemporalDerivativeRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- On the whole strict relative restart interval, every selected reconstructed
real velocity component is differentiable in time and has continuous ordinary
time derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    let f : ℝ → ℝ :=
      fun s : ℝ =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ s x).component j
    let I : Set ℝ :=
      Set.Ioo
        0
        (h3FinHeatLerayRestartRadius ν A)
    DifferentiableOn ℝ f I
      ∧
    ContinuousOn (deriv f) I := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let ξ : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let fC : ℝ → ℂ :=
    fun s : ℝ =>
      h3SpectralScalarC1Representative
        (W s i) ξ

  let I : Set ℝ :=
    Set.Ioo 0 R

  have hComplexRegularity :
      DifferentiableOn ℝ fC I
        ∧
      ContinuousOn (deriv fC) I := by
    dsimp only [fC, I, W, i, ξ]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_temporalDerivativeRegularity
        hν U₀ hA hU₀
        (h3ClassicalizationFinOfAxis j)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hComplexCriterion :
      ContDiffOn ℝ 1 fC I
        ↔
      DifferentiableOn ℝ fC I
        ∧
      ContinuousOn (deriv fC) I := by
    simpa using
      (contDiffOn_succ_iff_deriv_of_isOpen
        (𝕜 := ℝ)
        (f := fC)
        (s := I)
        (n := 0)
        isOpen_Ioo)

  have hComplexC1 :
      ContDiffOn ℝ 1 fC I :=
    hComplexCriterion.2 hComplexRegularity

  have hRealC1 :
      ContDiffOn ℝ 1
        (Complex.reCLM ∘ fC)
        I :=
    hComplexC1.continuousLinearMap_comp Complex.reCLM

  have hRealCriterion :
      ContDiffOn ℝ 1
          (Complex.reCLM ∘ fC)
          I
        ↔
      DifferentiableOn ℝ
          (Complex.reCLM ∘ fC)
          I
        ∧
      ContinuousOn
          (deriv (Complex.reCLM ∘ fC))
          I := by
    simpa using
      (contDiffOn_succ_iff_deriv_of_isOpen
        (𝕜 := ℝ)
        (f := Complex.reCLM ∘ fC)
        (s := I)
        (n := 0)
        isOpen_Ioo)

  have hRealRegularity :
      DifferentiableOn ℝ
          (Complex.reCLM ∘ fC)
          I
        ∧
      ContinuousOn
          (deriv (Complex.reCLM ∘ fC))
          I :=
    hRealCriterion.1 hRealC1

  have hPathEq :
      (Complex.reCLM ∘ fC)
        =
      (fun s : ℝ => (fC s).re) := by
    funext s
    simp only [Function.comp_apply, Complex.reCLM_apply]

  rw [hPathEq] at hRealRegularity

  change
    DifferentiableOn ℝ
        (fun s : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s (h3ClassicalizationFinOfAxis j))
            x)
        I
      ∧
    ContinuousOn
        (deriv
          (fun s : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s (h3ClassicalizationFinOfAxis j))
              x))
        I

  unfold
    h3SpectralScalarRealC1RepresentativeOnPoint3
    h3SpectralScalarRealC1Representative

  simpa only [
    fC,
    i,
    ξ
  ] using hRealRegularity

end

end Euclidean
end Bridge
end PrimeTensor
