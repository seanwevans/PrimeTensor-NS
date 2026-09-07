import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.Order.Zero
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Point3Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.F.Deriv.Coordinate.CLM

/-!
# Physical L² temporal admissibility: selected first spatial jet

The preceding checkpoint proved genuine joint `(time,space)` continuity of the
selected velocity itself.

This file closes the first spatial jet.

For a weighted H³ scalar state, coordinate derivative evaluation at a fixed
point is already packaged as a bounded continuous linear functional of the
spectral state.  Its norm is controlled by

    C₁ ‖G‖.

That estimate controls state variation uniformly in the physical point.
For a fixed H³ state, the reconstructed real field is spatially `C¹`, so its
coordinate partial is continuous.  Splitting a joint increment into state and
space increments therefore proves joint continuity of

    (G,x) ↦ ∂ₐ Rep(G)(x).

Composing with the continuous selected H³ spectral path closes joint
`(time,space)` continuity of every selected first spatial velocity derivative.

After this checkpoint the selected velocity frontier consists only of the pure
second spatial derivatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalSelectedFirstSpatial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by the physical weak-test layer. -/
local instance point3NormTopologicalSpaceH3PhysicalL2TemporalSelectedFirstSpatial :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- A coordinate derivative of an arbitrary real physical H³ representative
is continuous in the spatial point. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_continuous
    (G : H3SpectralScalarState)
    (a : PrimeTensor.Axis Depth.three) :
    Continuous
      (spatial3.d
        a
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G)) := by
  let q : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3 G

  have hqC1 : SpatialC1 q := by
    dsimp only [q]
    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one G

  have hfun :
      (fun x : Point3 =>
        spatial3.d a q x)
        =
      (fun x : Point3 =>
        (fderiv ℝ q x) (axisDirection a)) := by
    funext x
    exact
      hqC1.partialDeriv_eq_fderiv_axisDirection
        x a

  have hfd :
      ContDiff ℝ 0 (fderiv ℝ q) := by
    have hqC1' : ContDiff ℝ 1 q := by
      simpa only [SpatialC1] using hqC1

    exact
      hqC1'.fderiv_right
        (by norm_num)

  change
    Continuous
      (fun x : Point3 =>
        spatial3.d a q x)

  rw [hfun]

  exact
    (hfd.clm_apply contDiff_const).continuous

/-- Uniform H³ state-difference bound for one real physical spatial
derivative. -/
theorem norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_sub_apply_le
    (F G : H3SpectralScalarState)
    (i : Fin 3)
    (x : Point3) :
    ‖spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 F)
          x
        -
      spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
          x‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      ‖F - G‖ := by
  let xH : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let D :
      H3SpectralScalarState →L[ℂ] ℂ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCLM
      i xH

  have hF :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
      F i x

  have hG :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
      G i x

  have hComplex :
      ‖D (F - G)‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖F - G‖ := by
    dsimp only [D, xH]

    rw [
      h3SpectralScalarC1CoordinateDerivativeEvaluationCLM_apply
    ]

    exact
      norm_h3SpectralScalarC1Representative_fderiv_apply_fin_le
        (F - G)
        i
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hRe :
      ‖(D (F - G)).re‖
        ≤
      ‖D (F - G)‖ := by
    simpa [Real.norm_eq_abs] using
      Complex.abs_re_le_norm
        (D (F - G))

  rw [hF, hG]

  change
    ‖(D F).re - (D G).re‖
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      ‖F - G‖

  have hMap :
      D (F - G) = D F - D G := by
    exact map_sub D F G

  have hReal :
      (D F).re - (D G).re
        =
      (D (F - G)).re := by
    rw [hMap]
    rfl

  rw [hReal]

  exact hRe.trans hComplex

/-- One real physical coordinate derivative is jointly continuous in spectral
state and physical point. -/
theorem continuous_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_state_point
    (i : Fin 3) :
    Continuous
      (fun z : H3SpectralScalarState × Point3 =>
        spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 z.1)
          z.2) := by
  rw [continuous_iff_continuousAt]
  intro z

  let J :
      H3SpectralScalarState → Point3 → ℝ :=
    fun G x =>
      spatial3.d
        (h3AxisOfFin3 i)
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        x

  change
    Tendsto
      (fun w : H3SpectralScalarState × Point3 =>
        J w.1 w.2)
      (𝓝 z)
      (𝓝 (J z.1 z.2))

  rw [tendsto_iff_norm_sub_tendsto_zero]

  have hStateNormContinuous :
      Continuous
        (fun w : H3SpectralScalarState × Point3 =>
          ‖w.1 - z.1‖) :=
    (continuous_fst.sub continuous_const).norm

  have hStateNormAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × Point3 =>
          ‖w.1 - z.1‖)
        z :=
    hStateNormContinuous.continuousAt

  have hStateNorm :
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          ‖w.1 - z.1‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          ‖w.1 - z.1‖)
        (𝓝 z)
        (𝓝 ‖z.1 - z.1‖)
      at hStateNormAt

    simpa only [sub_self, norm_zero] using hStateNormAt

  have hFixedSpatial :
      Continuous (J z.1) := by
    dsimp only [J]
    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_continuous
        z.1
        (h3AxisOfFin3 i)

  have hSpaceNormContinuous :
      Continuous
        (fun w : H3SpectralScalarState × Point3 =>
          ‖J z.1 w.2 - J z.1 z.2‖) :=
    ((hFixedSpatial.comp continuous_snd).sub continuous_const).norm

  have hSpaceNormAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × Point3 =>
          ‖J z.1 w.2 - J z.1 z.2‖)
        z :=
    hSpaceNormContinuous.continuousAt

  have hSpaceNorm :
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          ‖J z.1 w.2 - J z.1 z.2‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          ‖J z.1 w.2 - J z.1 z.2‖)
        (𝓝 z)
        (𝓝 ‖J z.1 z.2 - J z.1 z.2‖)
      at hSpaceNormAt

    simpa only [sub_self, norm_zero] using hSpaceNormAt

  have hCoefficientContinuous :
      Continuous
        (fun _ : H3SpectralScalarState × Point3 =>
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) :=
    continuous_const

  have hUpperContinuous :
      Continuous
        (fun w : H3SpectralScalarState × Point3 =>
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              ‖w.1 - z.1‖
            +
          ‖J z.1 w.2 - J z.1 z.2‖) :=
    (hCoefficientContinuous.mul hStateNormContinuous).add
      hSpaceNormContinuous

  have hUpperAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × Point3 =>
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              ‖w.1 - z.1‖
            +
          ‖J z.1 w.2 - J z.1 z.2‖)
        z :=
    hUpperContinuous.continuousAt

  have hUpper :
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              ‖w.1 - z.1‖
            +
          ‖J z.1 w.2 - J z.1 z.2‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              ‖w.1 - z.1‖
            +
          ‖J z.1 w.2 - J z.1 z.2‖)
        (𝓝 z)
        (𝓝
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              ‖z.1 - z.1‖
            +
          ‖J z.1 z.2 - J z.1 z.2‖))
      at hUpperAt

    simpa only [sub_self, norm_zero, mul_zero, zero_add] using hUpperAt

  have hNonneg :
      ∀ᶠ w in 𝓝 z,
        0 ≤ ‖J w.1 w.2 - J z.1 z.2‖ :=
    Filter.Eventually.of_forall
      (fun w =>
        norm_nonneg
          (J w.1 w.2 - J z.1 z.2))

  have hBound :
      ∀ᶠ w in 𝓝 z,
        ‖J w.1 w.2 - J z.1 z.2‖
          ≤
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            ‖w.1 - z.1‖
          +
        ‖J z.1 w.2 - J z.1 z.2‖ := by
    exact
      Filter.Eventually.of_forall
        (fun w => by
          have hState :
              ‖J w.1 w.2 - J z.1 w.2‖
                ≤
              h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                ‖w.1 - z.1‖ := by
            dsimp only [J]

            exact
              norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_sub_apply_le
                w.1 z.1 i w.2

          have hDecomp :
              J w.1 w.2 - J z.1 z.2
                =
              (J w.1 w.2 - J z.1 w.2)
                +
              (J z.1 w.2 - J z.1 z.2) := by
            ring

          rw [hDecomp]

          exact
            (norm_add_le _ _).trans
              (add_le_add
                hState
                (le_refl
                  ‖J z.1 w.2 - J z.1 z.2‖)))

  exact
    squeeze_zero'
      hNonneg
      hBound
      hUpper

/-- Joint first-spatial-derivative continuity along any continuous finite H³
spectral path. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_jointContinuous_of_finSpectralPath
    (W : ℝ → H3SpectralFinVectorState)
    (hW : Continuous W)
    (i a : Fin 3) :
    Continuous
      (fun z : ℝ × Point3 =>
        spatial3.d
          (h3AxisOfFin3 a)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W z.1 i))
          z.2) := by
  have hCoordinate :
      Continuous
        (fun s : ℝ => W s i) :=
    (continuous_apply i).comp hW

  have hPair :
      Continuous
        (fun z : ℝ × Point3 =>
          (W z.1 i, z.2)) :=
    Continuous.prodMk
      (hCoordinate.comp continuous_fst)
      continuous_snd

  rw [continuous_iff_continuousAt]
  intro z

  exact
    ContinuousAt.comp'
      (f := fun y : ℝ × Point3 =>
        (W y.1 i, y.2))
      (g := fun p : H3SpectralScalarState × Point3 =>
        spatial3.d
          (h3AxisOfFin3 a)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 p.1)
          p.2)
      (x := z)
      (continuous_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_state_point
        a).continuousAt
      hPair.continuousAt

/-- After the first spatial jet is closed, the remaining selected velocity
frontier is only the pure second spatial derivatives. -/
def H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  let V :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    fun q =>
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        q
  ∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (spatial3.d
            a
            (fun y : Point3 =>
              (V z.1 y).component j))
          z.2)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ)

/-- The selected first spatial jet is automatically jointly continuous; hence
the old first-plus-second spatial frontier follows from only the pure second
jet hypothesis. -/
theorem H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed_of_pureSecond
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSecond :
      H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed
        (tau := tau)
        hν hNS ht hE hTail) :
    H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed
      (tau := tau)
      hν hNS ht hE hTail := by
  unfold
    H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed
    at hSecond

  unfold
    H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed

  dsimp only at hSecond ⊢

  refine
    ⟨?_, hSecond⟩

  intro a j

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hWcont :
      Continuous W := by
    simpa only [
      W,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.1

  have hCoordinate :
      Continuous
        (fun z : ℝ × Point3 =>
          spatial3.d
            (h3AxisOfFin3
              (h3ClassicalizationFinOfAxis a))
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W z.1
                (h3ClassicalizationFinOfAxis j)))
            z.2) :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_jointContinuous_of_finSpectralPath
      W hWcont
      (h3ClassicalizationFinOfAxis j)
      (h3ClassicalizationFinOfAxis a)

  rw [
    h3AxisOfFin3_h3ClassicalizationFinOfAxis a
  ] at hCoordinate

  apply hCoordinate.continuousOn.congr
  intro z hz

  have hField :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ z.1 y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W z.1
          (h3ClassicalizationFinOfAxis j)) := by
    funext y

    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

    rw [
      h3SpectralRealVelocityOfPath_component
    ]

    rfl

  change
    spatial3.d
        a
        (fun y : Point3 =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            hν U₀ hA hU₀ z.1 y).component j)
        z.2
      =
    spatial3.d
        a
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W z.1
            (h3ClassicalizationFinOfAxis j)))
        z.2

  exact
    congrArg
      (fun f : Point3 → ℝ =>
        spatial3.d a f z.2)
      hField

/-- The final physical `L²` identity now needs only selected pure-second
velocity joint continuity and selected pressure-force joint continuity. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedPureSecondJets_and_pressureForceJointlyContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hSelectedSecond :
      H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed
        (tau := tau)
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
    (hSelectedPressure :
      H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab
        (tau := tau)
        hNS ht hE hTail) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hSelectedSpatial :
      H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed
        (tau := tau)
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail :=
    H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed_of_pureSecond
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hSelectedSecond

  exact
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedSpatialJets_and_pressureForceJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint
      hEvolution hTauR
      hSelectedSpatial hSelectedPressure

end

end Euclidean
end Bridge
end PrimeTensor
