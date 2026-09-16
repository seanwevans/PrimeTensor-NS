import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongProjectedRHSGronwallBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Envelope

/-!
# Automatic selected-gradient and interaction-integrability data

The Grönwall bridge still exposed four inputs:

1. a uniform selected first-gradient bound `B`;
2. integrability of the absolute weak--strong interaction density;
3. the old-transport whole-space IBP datum;
4. the branch derivative-difference = projected-RHS identity.

The first two are not genuine remaining hypotheses.

The selected restart spectral path has the global H³ bound

    ‖W(s)‖ ≤ 2E

for every real time.  Each coordinate has norm at most the vector norm, and the
existing first-derivative evaluation theorem gives

    |∂ᵢ Sⱼ(s,x)|
      ≤ C₁ ‖W(s)ⱼ‖
      ≤ C₁ (2E).

Thus we may take the explicit constant

    B = C₁ (2E).

With this bound, the absolute weak--strong interaction density satisfies

    interaction(x) ≤ 3 B |D(x)|².

The concrete square density is already integrable because `D ∈ L²`.  The
interaction density itself is continuous (all selected and old slices are
spatially `C¹`), so domination yields its integrability automatically.

After this file, the projected-RHS Grönwall data requires only:

* the temporal derivative identity;
* old-transport whole-space IBP.

No new Navier--Stokes estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAutomaticSpatialData
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit global first-gradient envelope for the selected restart. -/
noncomputable def h3PreterminalSelectedWeakStrongGradientEnvelope
    (E : ℝ) : ℝ :=
  h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * (2 * E)

/-- The explicit selected first-gradient envelope is nonnegative whenever
`1 ≤ E`. -/
theorem h3PreterminalSelectedWeakStrongGradientEnvelope_nonneg
    {E : ℝ}
    (hE : 1 ≤ E) :
    0 ≤ h3PreterminalSelectedWeakStrongGradientEnvelope E := by
  unfold h3PreterminalSelectedWeakStrongGradientEnvelope

  exact
    mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (mul_nonneg (by norm_num) (le_trans zero_le_one hE))

/-- Uniform coordinatewise first-gradient bound for the selected unit-viscosity
restart, valid at every real restart-relative time. -/
theorem h3PreterminalSelectedWeakStrongVelocity_spatial_d_le_gradientEnvelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (x : Point3)
    (j i : PrimeTensor.Axis Depth.three) :
    abs
      (spatial3.d
        i
        (fun y =>
          ((h3PreterminalSelectedWeakStrongVelocity
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail)
            s y).component j)
        x)
      ≤
    h3PreterminalSelectedWeakStrongGradientEnvelope E := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hEpos hU₀

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let a : Fin 3 :=
    h3ClassicalizationFinOfAxis i

  have hEvaluation :
      ‖spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s k))
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖W s k‖ := by
    have h :=
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
        (W s k) a x

    rw [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis i
    ] at h

    exact h

  have hCoordinate :
      ‖W s k‖ ≤ ‖W s‖ := by
    exact
      h3SpectralVelocity_coordinate_norm_le
        (W s) k

  have hWBound :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      (one_pos : (0 : ℝ) < 1)
      (h3FinHeatLerayRestartRadius_pos
        (1 : ℝ)
        hEpos).le
      U₀
      hEpos
      hU₀
      (h3FinHeatLerayRestartRadius_smallness
        (1 : ℝ)
        hEpos.le)

  have hPath :
      ‖W s‖ ≤ 2 * E := by
    dsimp only [W]

    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWBound.2 s

  have hScalar :
      ‖W s k‖ ≤ 2 * E :=
    hCoordinate.trans hPath

  have hBound :
      ‖spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s k))
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        (2 * E) :=
    hEvaluation.trans
      (mul_le_mul_of_nonneg_left
        hScalar
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg)

  have hSelectedComponent :
      (fun y : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
          s y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W s k) := by
    funext y

    unfold h3PreterminalSelectedWeakStrongVelocity
    unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

    rw [h3SpectralRealVelocityOfPath_component]

    rfl

  rw [hSelectedComponent]

  unfold h3PreterminalSelectedWeakStrongGradientEnvelope

  simpa only [Real.norm_eq_abs] using hBound

/-- The actual absolute weak--strong interaction density is continuous at each
closed elapsed time. -/
theorem h3PreterminalSelectedOldWeakStrongAbsInteractionDensity_continuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    Continuous
      (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)) := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]

    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  have hx :
      Continuous
        (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) · xAxis) :=
    selectedOldWeakStrongSelectedGradientProduct_continuous
      selected old (q : ℝ) xAxis hSelected hOld

  have hy :
      Continuous
        (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) · yAxis) :=
    selectedOldWeakStrongSelectedGradientProduct_continuous
      selected old (q : ℝ) yAxis hSelected hOld

  have hz :
      Continuous
        (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) · zAxis) :=
    selectedOldWeakStrongSelectedGradientProduct_continuous
      selected old (q : ℝ) zAxis hSelected hOld

  change
    Continuous
      (selectedOldWeakStrongAbsInteractionDensity
        selected old (q : ℝ))

  change
    Continuous
      (fun x : Point3 =>
        abs
            (selectedOldWeakStrongSelectedGradientProduct
              selected old (q : ℝ) x xAxis)
          +
        (abs
            (selectedOldWeakStrongSelectedGradientProduct
              selected old (q : ℝ) x yAxis)
          +
         abs
            (selectedOldWeakStrongSelectedGradientProduct
              selected old (q : ℝ) x zAxis)))

  exact
    hx.abs.add (hy.abs.add hz.abs)

/-- The absolute weak--strong interaction density is automatically integrable.
The proof uses continuity for measurability and the already-proved pointwise
quadratic estimate for domination by the concrete `L²` square density. -/
theorem h3PreterminalSelectedOldWeakStrongAbsInteractionDensity_integrable_auto
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    MeasureTheory.Integrable
      (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ))
      (volume : Measure Point3) := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  let B :=
    h3PreterminalSelectedWeakStrongGradientEnvelope E

  let square : Point3 → ℝ :=
    selectedOldVelocityDifferenceSquarePointwise
      selected old (q : ℝ)

  let interaction : Point3 → ℝ :=
    selectedOldWeakStrongAbsInteractionDensity
      selected old (q : ℝ)

  let majorant : Point3 → ℝ :=
    fun x => 3 * B * square x

  have hB :
      0 ≤ B := by
    dsimp only [B]

    exact
      h3PreterminalSelectedWeakStrongGradientEnvelope_nonneg hE

  have hGradient :
      ∀
        (x : Point3)
        (j i : PrimeTensor.Axis Depth.three),
        abs
          (spatial3.d
            i
            (fun y =>
              (selected (q : ℝ) y).component j)
            x)
          ≤
        B := by
    intro x j i
    dsimp only [selected, B]

    exact
      h3PreterminalSelectedWeakStrongVelocity_spatial_d_le_gradientEnvelope
        hNS ht hE hTail (q : ℝ) x j i

  have hSquare :
      MeasureTheory.Integrable square
        (volume : Measure Point3) := by
    dsimp only [square, selected, old]

    exact
      selectedOldVelocityDifferenceSquarePointwise_actual_integrable
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q

  have hMajorant :
      MeasureTheory.Integrable majorant
        (volume : Measure Point3) := by
    dsimp only [majorant]

    exact hSquare.const_mul (3 * B)

  have hInteractionContinuous :
      Continuous interaction := by
    dsimp only [interaction, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongAbsInteractionDensity_continuous
        hNS ht hEnd hE hTail q

  have hInteractionMeasurable :
      MeasureTheory.AEStronglyMeasurable interaction
        (volume : Measure Point3) :=
    hInteractionContinuous.aestronglyMeasurable

  have hDom :
      ∀ x : Point3,
        ‖interaction x‖ ≤ majorant x := by
    intro x

    have hPoint :
        interaction x ≤ majorant x := by
      dsimp only [interaction, majorant, square]

      exact
        selectedOldWeakStrongAbsInteractionDensity_le
          selected old (q : ℝ) x B hB
          (hGradient x)

    have hNonneg :
        0 ≤ interaction x := by
      dsimp only [interaction]
      unfold selectedOldWeakStrongAbsInteractionDensity
      positivity

    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]

    exact hPoint

  exact
    hMajorant.mono'
      hInteractionMeasurable
      (Filter.Eventually.of_forall hDom)

/-- The Grönwall bridge can now be populated from only the genuine remaining
temporal identity and the old-transport IBP datum.  The selected gradient
envelope and interaction integrability are automatic. -/
noncomputable def h3PreterminalSelectedOldWeakStrongProjectedRHSDerivativeDataOnElapsed_of_temporal_of_oldTransport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail)
    (hDerivative :
      ∀ q : Set.Icc (0 : ℝ) tau,
        hBranches.selectedDerivative (q : ℝ)
            - hBranches.oldDerivative (q : ℝ)
          =
        h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
    (hOldTransport :
      ∀ q : Set.Icc (0 : ℝ) tau,
        H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
          hNS ht hEnd hE hTail q) :
    H3PreterminalSelectedOldWeakStrongProjectedRHSDerivativeDataOnElapsed
      hNS ht hEnd hE hTail htauR hBranches := by
  refine
    { B :=
        h3PreterminalSelectedWeakStrongGradientEnvelope E
      B_nonneg :=
        h3PreterminalSelectedWeakStrongGradientEnvelope_nonneg hE
      derivativeDifference_eq_projectedRHS :=
        hDerivative
      selectedGradient_bound := ?_
      interaction_integrable := ?_
      oldTransport_integrationByParts :=
        hOldTransport }

  · intro q x j i

    exact
      h3PreterminalSelectedWeakStrongVelocity_spatial_d_le_gradientEnvelope
        hNS ht hE hTail (q : ℝ) x j i

  · intro q

    exact
      h3PreterminalSelectedOldWeakStrongAbsInteractionDensity_integrable_auto
        hNS ht hEnd hE hTail q

/-- With automatic spatial data, physical selected/old agreement follows from
only the temporal projected-RHS identity and old-transport whole-space IBP. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_temporalProjectedRHS_of_oldTransport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hBranches :
      H3PreterminalSelectedOldL2BranchDerivativeDataOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail)
    (hDerivative :
      ∀ q : Set.Icc (0 : ℝ) tau,
        hBranches.selectedDerivative (q : ℝ)
            - hBranches.oldDerivative (q : ℝ)
          =
        h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
    (hOldTransport :
      ∀ q : Set.Icc (0 : ℝ) tau,
        H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
          hNS ht hEnd hE hTail q)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      (one_pos : (0 : ℝ) < 1)
      (q : ℝ) hNS ht hE hTail := by
  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_weakStrongProjectedRHS
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      hBranches
      (h3PreterminalSelectedOldWeakStrongProjectedRHSDerivativeDataOnElapsed_of_temporal_of_oldTransport
        hNS
        ht
        hEnd
        hE
        hTail
        htauR
        hBranches
        hDerivative
        hOldTransport)
      q

end

end Euclidean
end Bridge
end PrimeTensor
