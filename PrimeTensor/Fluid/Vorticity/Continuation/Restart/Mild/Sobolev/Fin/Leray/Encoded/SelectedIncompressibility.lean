import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.MildIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Physical.Solution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Retarded.Integrability

/-!
# Incompressibility of the Banach-selected finite H³ mild solution

`MildIncompressibility` proves the invariant for an arbitrary origin-based
heat--Leray mild path.  This file specializes that theorem to the concrete
Banach-selected solution already constructed on the physical restart interval.

There is only one analytic bookkeeping step.  The generic mild theorem asks
for genuine Bochner integrability of its Duhamel kernel.  The selected
normalized path has a canonical globally clamped physical-time extension; that
extension is continuous everywhere and bounded pointwise by the normalized
path's sup norm.  The existing retarded-integrability theorem therefore
supplies the required interval-integrability hypothesis at every
`q ∈ [0,τ]`.

Consequently, if the restart anchor is Fourier divergence-free, then every
physical-time slice selected by the Picard/Banach construction is Fourier
divergence-free as well.

No new Fourier algebra and no physical-space differentiation are used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3FinLeraySelectedIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The clamped physical-time extension of the selected normalized mild path
has an integrable retarded heat--Leray kernel up to every `q ∈ [0,τ]`. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_intervalIntegrable
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A *
          Real.sqrt τ
        ≤
      1)
    (q : Set.Icc (0 : ℝ) τ) :
    IntervalIntegrable
      (h3SpectralFinHeatLerayDuhamelIntegrand
        ν
        (q : ℝ)
        hν
        (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
          hν hτ U₀ hA hU₀ hsmall)
        (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
          hν hτ U₀ hA hU₀ hsmall))
      volume
      0
      (q : ℝ) := by

  let U : H3SpectralVelocityPath :=
    h3SpectralFinHeatLerayMildSolution
      hν hτ U₀ hA hU₀ hsmall

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hWcont : Continuous W := by
    dsimp only [
      W,
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
    ]
    exact
      continuous_h3PathPhysicalRealExtension τ U

  have hWbound :
      ∀ s ∈ Set.Ioc (0 : ℝ) (q : ℝ),
        ‖W s‖ ≤ ‖U‖ := by
    intro s hs
    dsimp only [
      W,
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
    ]
    exact
      norm_h3PathPhysicalRealExtension_le τ U s

  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν
      q.property.1
      (norm_nonneg U)
      (norm_nonneg U)
      W
      W
      hWcont
      hWcont
      hWbound
      hWbound

/-- Every physical-time slice of the concrete Banach-selected finite H³
heat--Leray mild solution is Fourier divergence-free whenever its restart
anchor is Fourier divergence-free. -/
theorem h3SpectralFinHeatLerayPhysicalMildSolution_divergenceFree
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A *
          Real.sqrt τ
        ≤
      1)
    (hDiv₀ : H3SpectralFinDivergenceFree U₀)
    (q : Set.Icc (0 : ℝ) τ) :
    H3SpectralFinDivergenceFree
      (h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ U₀ hA hU₀ hsmall q) := by

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (q : ℝ) hν W W)
        volume
        0
        (q : ℝ) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension_intervalIntegrable
        hν hτ U₀ hA hU₀ hsmall q

  have hMild :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall q

  have hMildW :
      h3SpectralVelocityHeatApplyNN
          ν hν.le (h3PhysicalTimePointNN q) U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν (q : ℝ) hν W W
        =
      W (q : ℝ) := by
    simpa only [
      W,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply
    ] using hMild

  have hDivW :
      H3SpectralFinDivergenceFree (W (q : ℝ)) := by
    exact
      h3SpectralFinHeatLerayMild_divergenceFree
        hν
        q.property.1
        U₀
        W
        hDiv₀
        hMildW
        hInt

  simpa only [
    W,
    h3SpectralFinHeatLerayPhysicalMildSolution_apply
  ] using hDivW

end
end Euclidean
end Bridge
end PrimeTensor
