import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Joint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Continuity

/-!
# Physical L² temporal admissibility: selected zero-order joint continuity

The previous reductions isolate the remaining temporal dominated-FTC input on
the selected restart side.

This file closes the zero-order velocity part honestly.

The key observation is that the H³ inverse-Fourier decoder is jointly
continuous in spectral state and physical point.  Its proof uses the exact
subtraction linearity of the classical representative together with the
uniform H³ point-evaluation estimate:

    ‖Rep(G - G₀)(x)‖ ≤ C ‖G - G₀‖.

Thus the state variation is controlled uniformly in `x`, while the spatial
variation at fixed `G₀` is ordinary `C¹` continuity.

Composing that joint decoder with the already-continuous selected H³ spectral
path gives genuine joint `(time,space)` continuity of every selected velocity
component.

Consequently the selected velocity-jet frontier no longer needs a separate
zero-order hypothesis: only first spatial derivatives and pure second spatial
derivatives remain.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalSelectedZeroOrder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by the physical weak-test layer. -/
local instance point3NormTopologicalSpaceH3PhysicalL2TemporalSelectedZeroOrder :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The complex H³ inverse-Fourier representative is jointly continuous in
spectral state and Fourier-space point.

The proof splits a joint increment into

    Rep(G,x) - Rep(G₀,x₀)
      =
    [Rep(G,x) - Rep(G₀,x)]
      +
    [Rep(G₀,x) - Rep(G₀,x₀)].

The first bracket is uniformly controlled by the H³ state norm; the second is
ordinary spatial continuity of the fixed `C¹` representative `Rep(G₀)`. -/
theorem continuous_h3SpectralScalarC1Representative_state_point :
    Continuous
      (fun z : H3SpectralScalarState × H3FourierPoint3 =>
        h3SpectralScalarC1Representative z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro z

  change
    Tendsto
      (fun w : H3SpectralScalarState × H3FourierPoint3 =>
        h3SpectralScalarC1Representative w.1 w.2)
      (𝓝 z)
      (𝓝 (h3SpectralScalarC1Representative z.1 z.2))

  rw [tendsto_iff_norm_sub_tendsto_zero]

  have hStateNormContinuous :
      Continuous
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖w.1 - z.1‖) :=
    (continuous_fst.sub continuous_const).norm

  have hStateNormAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖w.1 - z.1‖)
        z :=
    hStateNormContinuous.continuousAt

  have hStateNorm :
      Tendsto
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖w.1 - z.1‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖w.1 - z.1‖)
        (𝓝 z)
        (𝓝 ‖z.1 - z.1‖)
      at hStateNormAt

    simpa only [sub_self, norm_zero] using hStateNormAt

  have hFixedSpatial :
      Continuous
        (h3SpectralScalarC1Representative z.1) :=
    (h3SpectralScalarC1Representative_contDiff_one z.1).continuous

  have hSpaceNormContinuous :
      Continuous
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖) :=
    ((hFixedSpatial.comp continuous_snd).sub continuous_const).norm

  have hSpaceNormAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖)
        z :=
    hSpaceNormContinuous.continuousAt

  have hSpaceNorm :
      Tendsto
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖)
        (𝓝 z)
        (𝓝
          ‖h3SpectralScalarC1Representative z.1 z.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖)
      at hSpaceNormAt

    simpa only [sub_self, norm_zero] using hSpaceNormAt

  have hCoefficientContinuous :
      Continuous
        (fun _ : H3SpectralScalarState × H3FourierPoint3 =>
          h3RawFourierL1DeweightingCoefficient) :=
    continuous_const

  have hUpperContinuous :
      Continuous
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖) :=
    (hCoefficientContinuous.mul hStateNormContinuous).add
      hSpaceNormContinuous

  have hUpperAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖)
        z :=
    hUpperContinuous.continuousAt

  have hUpper :
      Tendsto
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × H3FourierPoint3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarC1Representative z.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖)
        (𝓝 z)
        (𝓝
          (h3RawFourierL1DeweightingCoefficient * ‖z.1 - z.1‖
            +
          ‖h3SpectralScalarC1Representative z.1 z.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖))
      at hUpperAt

    simpa only [sub_self, norm_zero, mul_zero, zero_add] using hUpperAt

  have hNonneg :
      ∀ᶠ w in 𝓝 z,
        0 ≤
          ‖h3SpectralScalarC1Representative w.1 w.2
              -
            h3SpectralScalarC1Representative z.1 z.2‖ :=
    Filter.Eventually.of_forall
      (fun w =>
        norm_nonneg
          (h3SpectralScalarC1Representative w.1 w.2
            -
          h3SpectralScalarC1Representative z.1 z.2))

  have hBound :
      ∀ᶠ w in 𝓝 z,
        ‖h3SpectralScalarC1Representative w.1 w.2
            -
          h3SpectralScalarC1Representative z.1 z.2‖
          ≤
        h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
          +
        ‖h3SpectralScalarC1Representative z.1 w.2
            -
          h3SpectralScalarC1Representative z.1 z.2‖ := by
    exact
      Filter.Eventually.of_forall
        (fun w => by
          have hState :
              ‖h3SpectralScalarC1Representative w.1 w.2
                  -
                h3SpectralScalarC1Representative z.1 w.2‖
                ≤
              h3RawFourierL1DeweightingCoefficient *
                ‖w.1 - z.1‖ :=
            norm_h3SpectralScalarC1Representative_sub_apply_le
              w.1 z.1 w.2

          have hDecomp :
              h3SpectralScalarC1Representative w.1 w.2
                    -
                  h3SpectralScalarC1Representative z.1 z.2
                =
              (h3SpectralScalarC1Representative w.1 w.2
                    -
                  h3SpectralScalarC1Representative z.1 w.2)
                +
              (h3SpectralScalarC1Representative z.1 w.2
                    -
                  h3SpectralScalarC1Representative z.1 z.2) := by
            ring

          rw [hDecomp]

          exact
            (norm_add_le _ _).trans
              (add_le_add
                hState
                (le_refl
                  ‖h3SpectralScalarC1Representative z.1 w.2
                      -
                    h3SpectralScalarC1Representative z.1 z.2‖)))

  exact
    squeeze_zero'
      hNonneg
      hBound
      hUpper

/-- Difference estimate for the real `Point3` representative, uniform in the
physical point. -/
theorem norm_h3SpectralScalarRealC1RepresentativeOnPoint3_sub_apply_le
    (F G : H3SpectralScalarState)
    (x : Point3) :
    ‖h3SpectralScalarRealC1RepresentativeOnPoint3 F x
        -
      h3SpectralScalarRealC1RepresentativeOnPoint3 G x‖
      ≤
    h3RawFourierL1DeweightingCoefficient * ‖F - G‖ := by
  let xH : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let z : ℂ :=
    h3SpectralScalarC1Representative F xH
      -
    h3SpectralScalarC1Representative G xH

  have hComplex :
      ‖z‖
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖F - G‖ := by
    dsimp only [z, xH]
    exact
      norm_h3SpectralScalarC1Representative_sub_apply_le
        F G
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hRe :
      ‖z.re‖ ≤ ‖z‖ := by
    simpa [Real.norm_eq_abs] using
      Complex.abs_re_le_norm z

  calc
    ‖h3SpectralScalarRealC1RepresentativeOnPoint3 F x
        -
      h3SpectralScalarRealC1RepresentativeOnPoint3 G x‖
        =
      ‖z.re‖ := by
        dsimp only [z, xH]
        unfold
          h3SpectralScalarRealC1RepresentativeOnPoint3
          h3SpectralScalarRealC1Representative
        rfl
    _ ≤ ‖z‖ := hRe
    _ ≤
      h3RawFourierL1DeweightingCoefficient * ‖F - G‖ :=
      hComplex

/-- The real physical H³ decoder is jointly continuous in spectral state and
ordinary `Point3`.

This is proved directly on `Point3`; no topology transport through the Fourier
`PiLp` carrier is required. -/
theorem continuous_h3SpectralScalarRealC1RepresentativeOnPoint3_state_point :
    Continuous
      (fun z : H3SpectralScalarState × Point3 =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro z

  change
    Tendsto
      (fun w : H3SpectralScalarState × Point3 =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          w.1 w.2)
      (𝓝 z)
      (𝓝
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          z.1 z.2))

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
      Continuous
        (h3SpectralScalarRealC1RepresentativeOnPoint3 z.1) :=
    (h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
      z.1).continuous

  have hSpaceNormContinuous :
      Continuous
        (fun w : H3SpectralScalarState × Point3 =>
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖) :=
    ((hFixedSpatial.comp continuous_snd).sub continuous_const).norm

  have hSpaceNormAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × Point3 =>
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖)
        z :=
    hSpaceNormContinuous.continuousAt

  have hSpaceNorm :
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖)
        (𝓝 z)
        (𝓝
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖)
      at hSpaceNormAt

    simpa only [sub_self, norm_zero] using hSpaceNormAt

  have hCoefficientContinuous :
      Continuous
        (fun _ : H3SpectralScalarState × Point3 =>
          h3RawFourierL1DeweightingCoefficient) :=
    continuous_const

  have hUpperContinuous :
      Continuous
        (fun w : H3SpectralScalarState × Point3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖) :=
    (hCoefficientContinuous.mul hStateNormContinuous).add
      hSpaceNormContinuous

  have hUpperAt :
      ContinuousAt
        (fun w : H3SpectralScalarState × Point3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖)
        z :=
    hUpperContinuous.continuousAt

  have hUpper :
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖)
        (𝓝 z)
        (𝓝 0) := by
    change
      Tendsto
        (fun w : H3SpectralScalarState × Point3 =>
          h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
            +
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖)
        (𝓝 z)
        (𝓝
          (h3RawFourierL1DeweightingCoefficient * ‖z.1 - z.1‖
            +
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖))
      at hUpperAt

    simpa only [sub_self, norm_zero, mul_zero, zero_add] using hUpperAt

  have hNonneg :
      ∀ᶠ w in 𝓝 z,
        0 ≤
          ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                w.1 w.2
              -
            h3SpectralScalarRealC1RepresentativeOnPoint3
                z.1 z.2‖ :=
    Filter.Eventually.of_forall
      (fun w =>
        norm_nonneg
          (h3SpectralScalarRealC1RepresentativeOnPoint3
              w.1 w.2
            -
          h3SpectralScalarRealC1RepresentativeOnPoint3
              z.1 z.2))

  have hBound :
      ∀ᶠ w in 𝓝 z,
        ‖h3SpectralScalarRealC1RepresentativeOnPoint3
              w.1 w.2
            -
          h3SpectralScalarRealC1RepresentativeOnPoint3
              z.1 z.2‖
          ≤
        h3RawFourierL1DeweightingCoefficient * ‖w.1 - z.1‖
          +
        ‖h3SpectralScalarRealC1RepresentativeOnPoint3
              z.1 w.2
            -
          h3SpectralScalarRealC1RepresentativeOnPoint3
              z.1 z.2‖ := by
    exact
      Filter.Eventually.of_forall
        (fun w => by
          have hState :
              ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                    w.1 w.2
                  -
                h3SpectralScalarRealC1RepresentativeOnPoint3
                    z.1 w.2‖
                ≤
              h3RawFourierL1DeweightingCoefficient *
                ‖w.1 - z.1‖ :=
            norm_h3SpectralScalarRealC1RepresentativeOnPoint3_sub_apply_le
              w.1 z.1 w.2

          have hDecomp :
              h3SpectralScalarRealC1RepresentativeOnPoint3
                    w.1 w.2
                  -
                h3SpectralScalarRealC1RepresentativeOnPoint3
                    z.1 z.2
                =
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                    w.1 w.2
                  -
                h3SpectralScalarRealC1RepresentativeOnPoint3
                    z.1 w.2)
                +
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                    z.1 w.2
                  -
                h3SpectralScalarRealC1RepresentativeOnPoint3
                    z.1 z.2) := by
            ring

          rw [hDecomp]

          exact
            (norm_add_le _ _).trans
              (add_le_add
                hState
                (le_refl
                  ‖h3SpectralScalarRealC1RepresentativeOnPoint3
                        z.1 w.2
                      -
                    h3SpectralScalarRealC1RepresentativeOnPoint3
                        z.1 z.2‖)))

  exact
    squeeze_zero'
      hNonneg
      hBound
      hUpper

/-- Joint continuity of one reconstructed real coordinate along any
continuous three-coordinate H³ spectral path. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_jointContinuous_of_finSpectralPath
    (W : ℝ → H3SpectralFinVectorState)
    (hW : Continuous W)
    (i : Fin 3) :
    Continuous
      (fun z : ℝ × Point3 =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W z.1 i)
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
        h3SpectralScalarRealC1RepresentativeOnPoint3
          p.1 p.2)
      (x := z)
      continuous_h3SpectralScalarRealC1RepresentativeOnPoint3_state_point.continuousAt
      hPair.continuousAt

/-- The genuinely remaining selected velocity-jet frontier after zero-order
joint continuity has been discharged. -/
def H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed
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
  (∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (fun y : Point3 =>
            (V z.1 y).component j)
          z.2)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ))
    ∧
  (∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (spatial3.d
            a
            (fun y : Point3 =>
              (V z.1 y).component j))
          z.2)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ))

/-- Zero-order selected velocity joint continuity is unconditional, so the
full selected velocity-jet package follows from only the first- and
pure-second-spatial jet hypotheses. -/
theorem H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed_of_spatialJets
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSpatial :
      H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed
        (tau := tau)
        hν hNS ht hE hTail) :
    H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
      (tau := tau)
      hν hNS ht hE hTail := by
  unfold
    H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed
    at hSpatial

  unfold
    H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed

  dsimp only at hSpatial ⊢

  rcases hSpatial with
    ⟨hFirst, hSecond⟩

  refine
    ⟨?_, hFirst, hSecond⟩

  intro j

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
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W z.1 (h3ClassicalizationFinOfAxis j))
            z.2) :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_jointContinuous_of_finSpectralPath
      W hWcont
      (h3ClassicalizationFinOfAxis j)

  have hEq :
      (fun z : ℝ × Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ z.1 z.2).component j)
        =
      (fun z : ℝ × Point3 =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W z.1 (h3ClassicalizationFinOfAxis j))
          z.2) := by
    funext z

    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

    rw [
      h3SpectralRealVelocityOfPath_component
    ]

    rfl

  rw [hEq]

  exact hCoordinate.continuousOn

/-- The final physical `L²` vector identity can therefore use the reduced
selected velocity frontier: only joint continuity of first and pure second
spatial velocity jets remains, together with selected pressure-force joint
continuity. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedSpatialJets_and_pressureForceJointlyContinuous
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
    (hSelectedSpatial :
      H3PreterminalTailSelectedVelocitySpatialJetsJointlyContinuousOnElapsed
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
  have hSelectedVelocity :
      H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed
        (tau := tau)
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail :=
    H3PreterminalTailSelectedVelocityJetsJointlyContinuousOnElapsed_of_spatialJets
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      hSelectedSpatial

  exact
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_selectedMomentumFieldsJointlyContinuous
      hNS ht htau hEnd hE hTail hEndpoint
      hEvolution hTauR
      hSelectedVelocity hSelectedPressure

end

end Euclidean
end Bridge
end PrimeTensor
