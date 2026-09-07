import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.Spatial.Second.Pure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C0.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Raw.Outer.Divergence.Advection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Force

/-!
# Physical L² temporal admissibility: selected pressure-force joint continuity

The selected velocity, first spatial jet, and pure second spatial jet are now
genuinely jointly continuous on every elapsed slab inside the restart radius.

This file closes the last selected-side spacetime regularity frontier: the
selected pressure force.

The pressure-force reconstruction has the exact identity

    -∂ᵢp = Re Nᵢ(W,W) - Re (P N(W,W))ᵢ.

The two terms are handled differently.

* The unprojected term `Re N` is exactly the physical selected advection term.
  Joint continuity therefore follows from the already-closed joint continuity
  of selected velocity and its first spatial jet.

* The Leray-projected forcing reconstruction has a raw Fourier `L¹`
  state-difference estimate whose right-hand side is independent of the
  physical evaluation point.  Together with continuity of the selected H³
  path and fixed-state spatial continuity, the usual time-plus-space
  decomposition gives genuine joint continuity of the projected forcing.

Subtracting the two closes pressure-force joint continuity in elapsed time.
The final step is only the affine time change `r = s - t` to the absolute
continuation slab.

No separate-continuity inference is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalSelectedPressureForce
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by the physical weak-test layer. -/
local instance point3NormTopologicalSpaceH3PhysicalL2TemporalSelectedPressureForce :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-! ## Joint continuity of the projected instantaneous forcing -/

/-- The continuous physical Leray-forcing reconstruction is jointly continuous
along any continuous H³ finite-coordinate spectral path.

The time estimate is uniform in the spatial point, so this is stronger than an
appeal to separate continuity. -/
theorem h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_diagonal_jointContinuous_of_continuousPath
    (W : ℝ → H3SpectralFinVectorState)
    (hW : Continuous W)
    (i : Fin 3) :
    Continuous
      (fun z : ℝ × Point3 =>
        h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W z.1) (W z.1) i z.2) := by
  rw [continuous_iff_continuousAt]
  intro z

  let s : ℝ := z.1
  let x : Point3 := z.2

  let J : ℝ → Point3 → ℂ :=
    fun r y =>
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W r) (W r) i y

  let C : ℝ :=
    h3NonlinearForcingL1Coefficient

  let d : ℝ → ℝ :=
    fun r => ‖W r - W s‖

  let n : ℝ → ℝ :=
    fun r => ‖W r‖

  let R : ℝ → ℝ :=
    fun r =>
      C * d r * n r +
        C * ‖W s‖ * d r

  have hWAt :
      ContinuousAt W s :=
    hW.continuousAt

  have hdAt :
      ContinuousAt d s := by
    dsimp only [d]
    exact
      (hWAt.sub continuousAt_const).norm

  have hnAt :
      ContinuousAt n s := by
    dsimp only [n]
    exact hWAt.norm

  have hRAt :
      ContinuousAt R s := by
    dsimp only [R]
    exact
      (((continuousAt_const.mul hdAt).mul hnAt).add
        ((continuousAt_const.mul hdAt)))

  have hRs : R s = 0 := by
    simp [R, d]

  have hRtend :
      Tendsto
        R
        (𝓝 s)
        (𝓝 0) := by
    change
      Tendsto
        R
        (𝓝 s)
        (𝓝 (R s))
      at hRAt
    rw [hRs] at hRAt
    exact hRAt

  have hFst :
      Tendsto
        (fun w : ℝ × Point3 => w.1)
        (𝓝 z)
        (𝓝 s) := by
    dsimp only [s]
    exact continuousAt_fst

  have hTimeUpper :
      Tendsto
        (fun w : ℝ × Point3 => R w.1)
        (𝓝 z)
        (𝓝 0) :=
    hRtend.comp hFst

  have hFixedSpatial :
      Continuous (J s) := by
    dsimp only [J]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_continuous
        (W s) (W s) i

  have hSpaceNormContinuous :
      Continuous
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖) :=
    ((hFixedSpatial.comp continuous_snd).sub continuous_const).norm

  have hSpaceNormAt :
      ContinuousAt
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖)
        z :=
    hSpaceNormContinuous.continuousAt

  have hSpaceNorm :
      Tendsto
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : ℝ × Point3 =>
          ‖J s w.2 - J s x‖)
        (𝓝 z)
        (𝓝 ‖J s z.2 - J s x‖)
      at hSpaceNormAt

    have hx : z.2 = x := by
      rfl

    simpa only [hx, sub_self, norm_zero] using hSpaceNormAt

  have hUpper :
      Tendsto
        (fun w : ℝ × Point3 =>
          R w.1 +
            ‖J s w.2 - J s x‖)
        (𝓝 z)
        (𝓝 0) := by
    have hAdd :=
      hTimeUpper.add hSpaceNorm

    simpa only [zero_add] using hAdd

  have hNonneg :
      ∀ᶠ w in 𝓝 z,
        0 ≤ ‖J w.1 w.2 - J s x‖ :=
    Filter.Eventually.of_forall
      (fun w =>
        norm_nonneg
          (J w.1 w.2 - J s x))

  have hBound :
      ∀ᶠ w in 𝓝 z,
        ‖J w.1 w.2 - J s x‖
          ≤
        R w.1 +
          ‖J s w.2 - J s x‖ := by
    exact
      Filter.Eventually.of_forall
        (fun w => by
          have hTime :
              ‖J w.1 w.2 - J s w.2‖
                ≤
              R w.1 := by
            dsimp only [J, R, C, d, n]

            unfold
              h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3

            exact
              norm_h3RawFinLerayOuterProductDivergenceC0Representative_diagonal_sub_le_stateDifference
                (W w.1) (W s) i
                ((WithLp.toLp 2 : Point3 → H3FourierPoint3) w.2)

          have hDecomp :
              J w.1 w.2 - J s x
                =
              (J w.1 w.2 - J s w.2)
                +
              (J s w.2 - J s x) := by
            ring

          rw [hDecomp]

          exact
            (norm_add_le _ _).trans
              (add_le_add
                hTime
                (le_refl
                  ‖J s w.2 - J s x‖)))

  have hNorm :
      Tendsto
        (fun w : ℝ × Point3 =>
          ‖J w.1 w.2 - J s x‖)
        (𝓝 z)
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hBound
      hUpper

  change
    Tendsto
      (fun w : ℝ × Point3 =>
        J w.1 w.2)
      (𝓝 z)
      (𝓝 (J z.1 z.2))

  rw [tendsto_iff_norm_sub_tendsto_zero]

  dsimp only [s, x] at hNorm

  exact hNorm

/-! ## Joint continuity of selected physical advection -/

/-- Joint selected velocity and first-jet continuity gives joint continuity of
the selected physical advection term on the elapsed slab. -/
theorem h3PreterminalTailSelectedAdvectionJointlyContinuousOnElapsed_of_velocityJets
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSelected :
      H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
        (tau := tau)
        hν hNS ht hE hTail) :
    ∀ i : Fin 3,
      ContinuousOn
        (fun z : ℝ × Point3 =>
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν
              (h3PreterminalTailCanonicalAnchorSpectralState
                hNS ht hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                hNS ht hE hTail))
            z.1 z.2).component
              (h3AxisOfFin3 i))
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
  unfold
    H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
    at hSelected

  dsimp only at hSelected

  rcases hSelected with
    ⟨hValue, hFirst, hSecond⟩

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

  intro i

  change
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (V z.1 z.2).component xAxis
            *
          spatial3.d
            xAxis
            (fun y : Point3 =>
              (V z.1 y).component
                (h3AxisOfFin3 i))
            z.2
          +
        (
          (V z.1 z.2).component yAxis
              *
            spatial3.d
              yAxis
              (fun y : Point3 =>
                (V z.1 y).component
                  (h3AxisOfFin3 i))
              z.2
            +
          (V z.1 z.2).component zAxis
              *
            spatial3.d
              zAxis
              (fun y : Point3 =>
                (V z.1 y).component
                  (h3AxisOfFin3 i))
              z.2
        ))
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ)

  exact
    ((hValue xAxis).mul
        (hFirst
          xAxis
          (h3AxisOfFin3 i))).add
      (((hValue yAxis).mul
          (hFirst
            yAxis
            (h3AxisOfFin3 i))).add
        ((hValue zAxis).mul
          (hFirst
            zAxis
            (h3AxisOfFin3 i))))

/-! ## Relative-time selected pressure force -/

/-- The selected pressure force is jointly continuous on every strict elapsed
slab inside the restart radius. -/
theorem h3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnElapsed_of_le_restartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    ∀ i : Fin 3,
      ContinuousOn
        (fun z : ℝ × Point3 =>
          PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3RawFinPressureRealC1OfPath
              (h3PreterminalTailCanonicalSelectedRestart
                (one_pos : (0 : ℝ) < 1)
                hNS ht hE hTail))
            z.1 z.2
            (h3AxisOfFin3 i))
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hW :
      Continuous W := by
    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart,
      U₀,
      hA,
      hU₀
    ]

    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)

  have hSelectedSecond :
      H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed
        (tau := tau)
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail :=
    H3PreterminalTailSelectedVelocityPureSecondSpatialJetsJointlyContinuousOnElapsed_of_le_restartRadius
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hTauR

  have hSelectedSpatial :
      H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed
        (tau := tau)
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail :=
    H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed_of_pureSecond
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hSelectedSecond

  have hSelectedVelocity :
      H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
        (tau := tau)
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail :=
    H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed_of_spatialJets
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hSelectedSpatial

  have hAdvection :=
    h3PreterminalTailSelectedAdvectionJointlyContinuousOnElapsed_of_velocityJets
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hSelectedVelocity

  intro i

  have hLerayComplex :
      Continuous
        (fun z : ℝ × Point3 =>
          h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W z.1) (W z.1) i z.2) :=
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_diagonal_jointContinuous_of_continuousPath
      W hW i

  have hLerayReal :
      Continuous
        (fun z : ℝ × Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W z.1) (W z.1) i z.2).re) := by
    change
      Continuous
        (fun z : ℝ × Point3 =>
          Complex.reCLM
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W z.1) (W z.1) i z.2))

    exact
      Complex.reCLM.continuous.comp
        hLerayComplex

  have hDifference :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalTailCanonicalAnchorSpectralState
                hNS ht hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                hNS ht hE hTail))
            z.1 z.2).component
              (h3AxisOfFin3 i)
            -
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W z.1) (W z.1) i z.2).re)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) :=
    (hAdvection i).sub
      hLerayReal.continuousOn

  apply hDifference.congr

  intro z hz

  have hz0 : 0 ≤ z.1 :=
    hz.1.1.le

  have hzR :
      z.1 ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    le_trans hz.1.2.le hTauR

  dsimp only [W]

  rw [
    h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
  ]

  rw [
    h3PreterminalTailCanonicalSelectedRealVelocity_rawOuterDivergence_fourierInv_re_eq_advection
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hz0 hzR
      i z.2
  ]

/-! ## Absolute-time selected pressure force -/

/-- The absolute selected pressure-force frontier is automatic on every slab
whose elapsed length lies inside the restart radius. -/
theorem H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab_of_le_restartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hTauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab
      (tau := tau)
      hNS ht hE hTail := by
  unfold
    H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab

  intro j

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hRelative :=
    h3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnElapsed_of_le_restartRadius
      hNS ht hE hTail hTauR i

  let shiftBack : ℝ × Point3 → ℝ × Point3 :=
    fun z => (z.1 - t, z.2)

  have hShiftBack :
      Continuous shiftBack := by
    dsimp only [shiftBack]
    fun_prop

  have hMaps :
      MapsTo
        shiftBack
        (Set.Ioo t (t + tau) ×ˢ Set.univ)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
    intro z hz

    exact
      ⟨
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
        Set.mem_univ z.2
      ⟩

  have hComp :
      ContinuousOn
        ((fun z : ℝ × Point3 =>
          PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3RawFinPressureRealC1OfPath
              (h3PreterminalTailCanonicalSelectedRestart
                (one_pos : (0 : ℝ) < 1)
                hNS ht hE hTail))
            z.1 z.2
            (h3AxisOfFin3 i)) ∘
          shiftBack)
        (Set.Ioo t (t + tau) ×ˢ Set.univ) :=
    hRelative.comp
      hShiftBack.continuousOn
      hMaps

  apply hComp.congr

  intro z hz

  dsimp only [
    Function.comp_apply,
    shiftBack,
    i
  ]

  unfold
    h3PreterminalTailCanonicalSelectedPressureAbsolute

  dsimp only

  rw [
    h3AxisOfFin3_h3ClassicalizationFinOfAxis
      j
  ]

  unfold
    PrimeTensor.Bridge.RealFluid.pressureForceComponent

  rfl

/-- All selected spacetime regularity frontiers in the temporal dominated-FTC
branch are now discharged.  The only remaining non-endpoint hypothesis in
this theorem is the pre-existing physical-evolution/overlap hypothesis. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_physicalEvolution_and_restartRadius
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
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hSelectedPressure :
      H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab
        (tau := tau)
        hNS ht hE hTail :=
    H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab_of_le_restartRadius
      hNS ht hE hTail hTauR

  exact
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedPressureForceJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint
      hEvolution hTauR
      hSelectedPressure

end

end Euclidean
end Bridge
end PrimeTensor
