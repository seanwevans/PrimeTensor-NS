import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Selected.Second.Frechet.Time.Integrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.C1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Restart.Bound
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Full selected spatial C² regularity of the nonlinear Duhamel reconstruction

The endpoint quarter-Hölder branch has now reached the full second-Fréchet
level.

The fixed-lag first-Fréchet representative has the assembled Hessian as a
genuine Fréchet derivative.  The preceding checkpoint proved that the selected
retarded Hessian path is Bochner integrable, is dominated by nine copies of
the endpoint second-coordinate majorant, and integrates exactly to the
continuous selected Duhamel Hessian field.

This file spends those facts in Mathlib's Fréchet parametric-integral theorem.
First, the complete selected first-Fréchet Duhamel field is shown to have the
selected Hessian as its genuine Fréchet derivative.  Continuity of that
Hessian upgrades the first-derivative field to `ContDiff ℝ 1`.

Finally, the already-proved first-order Duhamel derivative witness and
`contDiff_succ_iff_hasFDerivAt` package the original nonlinear Duhamel
reconstruction as genuinely `ContDiff ℝ 2` in the full spatial variable.

No coordinatewise-to-Fréchet shortcut is used here: both derivative layers are
genuine Fréchet witnesses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedFullC2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-
Use Mathlib's canonical operator-norm structures explicitly at the two CLM
levels appearing in the second-Fréchet parametric integral.
-/
local instance h3SelectedFullC2FirstCLMNormedAddCommGroup :
    NormedAddCommGroup (H3FourierPoint3 →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance h3SelectedFullC2FirstCLMNormedSpace :
    NormedSpace ℝ (H3FourierPoint3 →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

local instance h3SelectedFullC2SecondCLMNormedAddCommGroup :
    NormedAddCommGroup
      (H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance h3SelectedFullC2SecondCLMNormedSpace :
    NormedSpace ℝ
      (H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ)) :=
  ContinuousLinearMap.toNormedSpace

/-- Along the selected restart path, the complete first-Fréchet Duhamel field
has the assembled selected Hessian as its genuine Fréchet derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_hasFDerivAt_secondFrechet
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    HasFDerivAt
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i)
      (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x)
      x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F :
      H3FourierPoint3 →
        ℝ →
          (H3FourierPoint3 →L[ℝ] ℂ) :=
    fun y s =>
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
        ν t W W i y s

  let F' :
      H3FourierPoint3 →
        ℝ →
          (H3FourierPoint3 →L[ℝ]
            (H3FourierPoint3 →L[ℝ] ℂ)) :=
    fun y s =>
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν t W W i y s

  let bound : ℝ → ℝ :=
    fun s =>
      9 *
        h3SelectedSecondCoordinateDerivativePathMajorant
          ν A t hν U₀ hA hU₀ i s

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hW :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖W s‖ ≤ 2 * A := by
    intro s hs
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hFInt :
      ∀ y : H3FourierPoint3,
        Integrable
          (F y)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    intro y
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
          ν t W W i y)
        (Set.Ioo (0 : ℝ) t)
        volume
    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_integrableOn_Ioo_of_continuous
        hν ht.le h2A h2A
        W W
        hWcont hWcont
        hW hW
        i y

  have hFMeas :
      ∀ᶠ y : H3FourierPoint3 in 𝓝 x,
        AEStronglyMeasurable
          (F y)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    Filter.Eventually.of_forall fun y =>
      (hFInt y).aestronglyMeasurable

  have hFxInt :
      Integrable
        (F x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hFInt x

  have hF'xInt :
      Integrable
        (F' x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
          ν t W W i x)
        (Set.Ioo (0 : ℝ) t)
        volume
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_selectedRestart_integrableOn_Ioo
        hν U₀ hA hU₀ ht htR i x

  have hF'xMeas :
      AEStronglyMeasurable
        (F' x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hF'xInt.aestronglyMeasurable

  have hMajorantInt :
      Integrable
        (h3SelectedSecondCoordinateDerivativePathMajorant
          ν A t hν U₀ hA hU₀ i)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3SelectedSecondCoordinateDerivativePathMajorant
          ν A t hν U₀ hA hU₀ i)
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    exact
      h3SelectedSecondCoordinateDerivativePathMajorant_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

  have hBoundInt :
      Integrable
        bound
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    simpa [bound] using hMajorantInt.const_mul (9 : ℝ)

  have hBound :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ y ∈ (Set.univ : Set H3FourierPoint3),
          ‖F' y s‖ ≤ bound s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro y hy
    dsimp only [F', bound]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_selectedRestart_le
        hν U₀ hA hU₀ hs i y

  have hDiff :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ y ∈ (Set.univ : Set H3FourierPoint3),
          HasFDerivAt (F · s) (F' y s) y := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro y hy

    dsimp only [F, F']

    change
      HasFDerivAt
        (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
          ν (t - s) (W s) (W s) i)
        (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
          ν (t - s) (W s) (W s) i y)
        y

    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_hasFDerivAt_secondFrechet
        hν
        (sub_pos.mpr hs.2)
        (W s)
        (W s)
        i
        y

  have hIntegral :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := (Set.univ : Set H3FourierPoint3))
      (F := F)
      (F' := F')
      (x₀ := x)
      (bound := bound)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
      Filter.univ_mem
      hFMeas
      hFxInt
      hF'xMeas
      hBound
      hBoundInt
      hDiff

  have hValueIntegral
      (y : H3FourierPoint3) :
      (∫ s : ℝ,
          F y s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i y := by
    calc
      (∫ s : ℝ,
          F y s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
          =
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
            ν t W W i y s := by
              rw [intervalIntegral.integral_of_le ht.le]
              rw [← restrict_Ioo_eq_restrict_Ioc]
      _ =
        h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
          ν t W W i y :=
            intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_eq_Duhamel
              hν ht.le h2A h2A
              W W
              hWcont hWcont
              hW hW
              i y

  have hDerivativeIntegral :
      (∫ s : ℝ,
          F' x s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x := by
    calc
      (∫ s : ℝ,
          F' x s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
          =
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
            ν t W W i x s := by
              rw [intervalIntegral.integral_of_le ht.le]
              rw [← restrict_Ioo_eq_restrict_Ioc]
      _ =
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
          ν t W W i x :=
            intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_eq_Duhamel_selectedRestart
              hν U₀ hA hU₀ ht htR i x

  change
    HasFDerivAt
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i)
      (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i x)
      x

  have hValueFunction :
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i)
        =
      (fun y : H3FourierPoint3 =>
        ∫ s : ℝ,
          F y s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t))) := by
    funext y
    exact (hValueIntegral y).symm

  rw [hValueFunction]
  rw [← hDerivativeIntegral]
  exact hIntegral

/-- The complete selected first-Fréchet Duhamel field is continuously
Fréchet-differentiable, with the selected Hessian as its derivative field. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_contDiff_one
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 1
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t W W i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  rw [contDiff_one_iff_hasFDerivAt]

  refine
    ⟨h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
        ν t W W i, ?_, ?_⟩

  · exact
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_selectedRestart_continuous
        hν U₀ hA hU₀ ht htR i

  · intro x
    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_hasFDerivAt_secondFrechet
        hν U₀ hA hU₀ ht htR i x

/-- Full selected spatial `C²` regularity of the nonlinear Duhamel
reconstruction.  Both derivative layers are genuine Fréchet derivatives. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_contDiff_two
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 2
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hW :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖W s‖ ≤ 2 * A := by
    intro s hs
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hFirstDerivative :
      ∀ x : H3FourierPoint3,
        HasFDerivAt
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
            ν t W W i x)
          x := by
    intro x
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasFDerivAt
        hν ht.le h2A h2A
        W W
        hWcont hWcont
        hW hW
        i x

  have hFirstDerivativeC1 :
      ContDiff ℝ 1
        (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
          ν t W W i) := by
    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_selectedRestart_contDiff_one
        hν U₀ hA hU₀ ht htR i

  have hC2 :
      ContDiff ℝ (1 + 1)
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i) := by
    exact
      (contDiff_succ_iff_hasFDerivAt).2
        ⟨h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
            ν t W W i,
          hFirstDerivativeC1,
          hFirstDerivative⟩

  exact hC2.of_le (by norm_num)

end
end Euclidean
end Bridge
end PrimeTensor
