import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPressureLocalFill
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPressureMomentumAbsoluteTime
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityMixedRegularityReduction

/-!
# Momentum transport to the canonical H³ local fill

The selected pressure and momentum identities are now available in absolute
continuation time, while the final PDE remainder is stated for the canonical
old/selected overlap local fill.

This file performs only representation transport.

* Before `T`, the local fill agrees with the logged preterminal solution on an
  open time neighborhood, so its temporal derivative transports by
  `EventuallyEq.deriv_eq`; its spatial advection and Laplacian transport by
  exact fixed-time field equality.  The pressure splice is the old pressure,
  so the original `PreterminalNavierStokes3.momentum` theorem applies.
* At and after `T`, physical-tail evolution identifies the local fill with the
  shifted selected real restart on an open neighborhood.  The same transport
  then reduces the target to the already-proved absolute selected momentum
  identity.

The only algebraic bridge added here converts the project's nonempty
three-axis fold in `RealFluid.laplacianVector` to the `Fin 3` sum used by the
spectral classicalization theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedPressureMomentumLocalFill
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- In dimension three, the project `Axis.fold` Laplacian is exactly the
`Fin 3` coordinate sum used by the selected spectral PDE. -/
theorem realFluid_laplacianVector_component_eq_fin_sum_three
    (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    (PrimeTensor.Bridge.RealFluid.laplacianVector
      spatial3 v s x).component j
      =
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (v s y).component j))
        x := by
  change
    PrimeTensor.Axis.fold
        (· + ·)
        Depth.three
        (fun i =>
          spatial3.d
            i
            (spatial3.d
              i
              (fun y : Point3 =>
                (v s y).component j))
            x)
      =
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (v s y).component j))
        x

  rw [PrimeTensor.Bridge.Euclidean.axis_fold_three]

  simp only [
    Fin.sum_univ_three,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rw [add_assoc]

/-- The `Axis Depth.three → Fin 3` classicalization index is inverse to
the concrete `Fin 3 → Axis Depth.three` bridge.  Keep this proof isolated from
tensor-component expressions so dependent `Axis` elimination never occurs in
the momentum target itself. -/
@[simp]
theorem h3AxisOfFin3_h3ClassicalizationFinOfAxis_local
    (j : PrimeTensor.Axis Depth.three) :
    h3AxisOfFin3 (h3ClassicalizationFinOfAxis j) = j := by
  cases j with
  | first =>
      rfl
  | next j =>
      cases j with
      | first =>
          rfl
      | next j =>
          cases j with
          | first =>
              rfl

/-- Axis-indexed form of the selected absolute-time momentum theorem.

Only the temporal derivative is evaluated through the shifted absolute-time
velocity path.  Advection and Laplacian stay in the restart clock `s - t`,
exactly matching `SelectedPressureMomentumAbsoluteTime`. -/
theorem h3PreterminalTailCanonicalSelectedRestartAbsolute_pressure_momentum_axis
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs :
      s ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let vSelectedAbsolute :
        SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
      fun τ =>
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalTailCanonicalAnchorSpectralState
            hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          (τ - t)
    (
      PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
        temporal vSelectedAbsolute s x
    ).component j
      +
    (
      PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath W)
        (s - t) x
    ).component j
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3PreterminalTailCanonicalSelectedPressureAbsolute
          hNS ht hE hTail)
        s x j
      +
    (
      PrimeTensor.Bridge.RealFluid.laplacianVector
        spatial3
        (h3SpectralRealVelocityOfPath W)
        (s - t) x
    ).component j := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let vSelectedAbsolute :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    fun τ =>
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        (τ - t)

  rw [
    realFluid_laplacianVector_component_eq_fin_sum_three
      (h3SpectralRealVelocityOfPath W)
      (s - t) x j
  ]

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxis :
      h3AxisOfFin3 i = j := by
    dsimp only [i]
    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis_local j

  have h :=
    h3PreterminalTailCanonicalSelectedRestartAbsolute_pressure_momentum_fin
      hNS ht hE hTail hs i x

  rw [← hAxis]

  simpa only [
    W,
    vSelectedAbsolute,
    PrimeTensor.Bridge.RealFluid.temporalVectorDerivative,
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
    h3PreterminalTailCanonicalSelectedRestart,
    h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
    h3SpectralVelocityRealC1RepresentativeOnPoint3
  ] using h

/-- The piecewise pressure from `SelectedPressureLocalFill` satisfies the
normalized unit-viscosity momentum equation with the actual canonical local-fill
velocity throughout `(0,S)`. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_pressureMomentum
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hTS : T < S)
    (hSR :
      S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PreterminalTailUnitViscosityMomentumAt
      hNS ht hE hTail
      (h3PreterminalTailCanonicalSelectedPressureLocalFill
        hNS ht hE hTail)
      S := by
  intro s hs x j

  let vFill :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
      hNS ht hE hTail S

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T := by
    dsimp only [pOld]
    exact Classical.choose_spec hNS

  by_cases hBefore : s < T

  · have hsOld : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hs.1, hBefore⟩

    have hNeighborhood :
        Set.Ioo (0 : ℝ) T ∈ 𝓝 s :=
      Ioo_mem_nhds hs.1 hBefore

    have hFieldEq
        (r : ℝ)
        (hr : r ∈ Set.Ioo (0 : ℝ) T) :
        vFill r = logSpaceTimeVectorField u r := by
      have hrS : r ∈ Set.Ioo (0 : ℝ) S :=
        ⟨hr.1, lt_trans hr.2 hTS⟩

      have hAgree :
          logSpaceTimeVectorField u r
            =
          h3PreterminalTailCanonicalSelectedOverlapGlue
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail r :=
        h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail r hr

      dsimp only [vFill]

      rw [
        h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
          hNS ht hE hTail hrS
      ]

      exact hAgree.symm

    have hTimeEq :
        (fun r : ℝ =>
          (vFill r x).component j)
          =ᶠ[𝓝 s]
        (fun r : ℝ =>
          (logSpaceTimeVectorField u r x).component j) := by
      filter_upwards [hNeighborhood] with r hr
      rw [hFieldEq r hr]

    have hTemporalEq :
        (
          PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
            temporal vFill s x
        ).component j
          =
        (
          PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
            temporal (logSpaceTimeVectorField u) s x
        ).component j := by
      unfold PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
      change
        deriv
            (fun r : ℝ => (vFill r x).component j)
            s
          =
        deriv
            (fun r : ℝ =>
              (logSpaceTimeVectorField u r x).component j)
            s
      exact hTimeEq.deriv_eq

    have hSliceEq :
        vFill s = logSpaceTimeVectorField u s :=
      hFieldEq s hsOld

    have hAdvectionEq :
        (
          PrimeTensor.Bridge.RealFluid.advection
            spatial3 vFill s x
        ).component j
          =
        (
          PrimeTensor.Bridge.RealFluid.advection
            spatial3 (logSpaceTimeVectorField u) s x
        ).component j := by
      unfold PrimeTensor.Bridge.RealFluid.advection
      rw [hSliceEq]

    have hLaplacianEq :
        (
          PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3 vFill s x
        ).component j
          =
        (
          PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3 (logSpaceTimeVectorField u) s x
        ).component j := by
      unfold
        PrimeTensor.Bridge.RealFluid.laplacianVector
        PrimeTensor.Bridge.RealFluid.laplacian
      rw [hSliceEq]

    have hPressureEq :
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3PreterminalTailCanonicalSelectedPressureLocalFill
              hNS ht hE hTail)
            s x j
          =
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3 pOld s x j := by
      unfold
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
        h3PreterminalTailCanonicalSelectedPressureLocalFill
      simp only [dif_pos hBefore, pOld]

    rw [
      hTemporalEq,
      hAdvectionEq,
      hPressureEq,
      hLaplacianEq
    ]

    exact hPDE.momentum s hsOld x j

  · have hsT : T ≤ s :=
      le_of_not_gt hBefore

    have hts : t < s :=
      lt_of_lt_of_le ht.2 hsT

    have hSUpper :
        S < t + h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      linarith [hSR]

    have hsSelected :
        s ∈ Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨hts, lt_trans hs.2 hSUpper⟩

    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail

    let vSelectedAbsolute :
        SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
      fun r =>
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalTailCanonicalAnchorSpectralState
            hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          (r - t)

    have hNeighborhood :
        Set.Ioo t S ∈ 𝓝 s :=
      Ioo_mem_nhds hts hs.2

    have hFieldEq
        (r : ℝ)
        (hr : r ∈ Set.Ioo t S) :
        vFill r = vSelectedAbsolute r := by
      have hrS : r ∈ Set.Ioo (0 : ℝ) S :=
        ⟨lt_trans ht.1 hr.1, hr.2⟩

      have hrR :
          r - t ≤
            h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        have hlt :
            r - t <
              h3FinHeatLerayRestartRadius (1 : ℝ) E := by
          linarith [hr.2, hSR]
        exact hlt.le

      have hEq :
          h3PreterminalTailCanonicalSelectedOverlapGlue
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail r
            =
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalTailCanonicalAnchorSpectralState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
              hNS ht hE hTail)
            (r - t) :=
        h3PreterminalTailCanonicalSelectedOverlapGlue_eq_selected_on_restartWindow
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail hEvolution
          r hr.1 hrR

      dsimp only [vFill, vSelectedAbsolute]

      rw [
        h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
          hNS ht hE hTail hrS
      ]

      exact hEq

    have hTimeEq :
        (fun r : ℝ =>
          (vFill r x).component j)
          =ᶠ[𝓝 s]
        (fun r : ℝ =>
          (vSelectedAbsolute r x).component j) := by
      filter_upwards [hNeighborhood] with r hr
      rw [hFieldEq r hr]

    have hTemporalEq :
        (
          PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
            temporal vFill s x
        ).component j
          =
        (
          PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
            temporal vSelectedAbsolute s x
        ).component j := by
      unfold PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
      change
        deriv
            (fun r : ℝ => (vFill r x).component j)
            s
          =
        deriv
            (fun r : ℝ =>
              (vSelectedAbsolute r x).component j)
            s
      exact hTimeEq.deriv_eq

    have hSliceEq :
        vFill s = vSelectedAbsolute s :=
      hFieldEq s ⟨hts, hs.2⟩

    have hSelectedSliceEq :
        vSelectedAbsolute s
          =
        h3SpectralRealVelocityOfPath W (s - t) := by
      dsimp only [vSelectedAbsolute, W]
      simp only [
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
        h3PreterminalTailCanonicalSelectedRestart
      ]

    have hSliceEqRelative :
        vFill s
          =
        h3SpectralRealVelocityOfPath W (s - t) :=
      hSliceEq.trans hSelectedSliceEq

    have hAdvectionEq :
        (
          PrimeTensor.Bridge.RealFluid.advection
            spatial3 vFill s x
        ).component j
          =
        (
          PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath W)
            (s - t) x
        ).component j := by
      unfold PrimeTensor.Bridge.RealFluid.advection
      rw [hSliceEqRelative]

    have hLaplacianEq :
        (
          PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3 vFill s x
        ).component j
          =
        (
          PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (h3SpectralRealVelocityOfPath W)
            (s - t) x
        ).component j := by
      unfold
        PrimeTensor.Bridge.RealFluid.laplacianVector
        PrimeTensor.Bridge.RealFluid.laplacian
      rw [hSliceEqRelative]

    have hPressureEq :
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3PreterminalTailCanonicalSelectedPressureLocalFill
              hNS ht hE hTail)
            s x j
          =
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3
            (h3PreterminalTailCanonicalSelectedPressureAbsolute
              hNS ht hE hTail)
            s x j := by
      unfold
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
        h3PreterminalTailCanonicalSelectedPressureLocalFill
      simp only [dif_neg hBefore]

    have hSelected :=
      h3PreterminalTailCanonicalSelectedRestartAbsolute_pressure_momentum_axis
        hNS ht hE hTail hsSelected x j

    rw [
      hTemporalEq,
      hAdvectionEq,
      hPressureEq,
      hLaplacianEq
    ]

    simpa only [W, vSelectedAbsolute] using hSelected

end

end Euclidean
end Bridge
end PrimeTensor
