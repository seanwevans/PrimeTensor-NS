import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailGlueThirdJetContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.TailLocalWellPosedness

/-!
# Classicalization: unit-viscosity local PDE frontier

The spectral construction carries an explicit viscosity parameter `ν`, while
`PreterminalNavierStokes3` is the normalized real equation with unit
Laplacian coefficient.  This file makes that coefficient match explicit by
specializing the final classicalization frontier to `ν = 1`.

The previous seam increments have already proved, from physical tail evolution:

* exact old-branch agreement before `T`;
* exact selected/preterminal pointwise overlap;
* equality of the piecewise glue with the shifted selected real restart on the
  whole positive restart window;
* spatial `C³` on every old slice and every selected-window slice;
* complete third-jet continuity at `T` whenever `T - t < R`.

Only one harmless total-function issue remains.  `RealVelocitySpatialC3` asks
for spatial `C³` at every real time, although the Navier--Stokes restart only
exists on `(0,S)`.  We therefore package the canonical glue as

    glue(s),  0 < s < S
    0,        otherwise.

This does not change the field anywhere used by `PreterminalNavierStokes3`,
agreement before `T`, or terminal regularity.  It makes global slice-wise
spatial `C³` automatic outside the local interval.

The remaining genuinely PDE-side statement is then minimal:

* choose `S` with `T < S < t + R`;
* produce a pressure making this filled field a normalized
  `PreterminalNavierStokes3` solution on `(0,S)`.

Together with the already-isolated unit-viscosity physical-tail evolution
frontier, that local PDE statement implies `H3ControlProducesExtension`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailUnitViscosityFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Total-field packaging of the canonical selected-overlap glue.

Inside the actual local existence interval `(0,S)` it is exactly the glue.
Outside that interval it is the spatially constant zero vector field. -/
noncomputable def h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (S : ℝ) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  fun s x =>
    if s ∈ Set.Ioo (0 : ℝ) S then
      h3PreterminalTailCanonicalSelectedOverlapGlue
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
        s x
    else
      ⟨fun _ => 0⟩

@[simp]
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs : s ∈ Set.Ioo (0 : ℝ) S) :
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
        hNS ht hE hTail S s
      =
    h3PreterminalTailCanonicalSelectedOverlapGlue
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail s := by
  unfold h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
  simp [hs]

@[simp]
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_zero_of_not_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs : s ∉ Set.Ioo (0 : ℝ) S) :
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
        hNS ht hE hTail S s
      =
    (fun _ : Point3 => ⟨fun _ => 0⟩) := by
  unfold h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
  simp [hs]

/-- If `T < S`, the filled field still agrees exactly with the old logged
solution throughout `(0,T)`. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_agreesBeforeT
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hTS : T < S) :
    RealRestartAgreesBeforeT
      u
      (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
        hNS ht hE hTail S)
      T := by
  intro s hs

  have hsS :
      s ∈ Set.Ioo (0 : ℝ) S :=
    ⟨hs.1, lt_trans hs.2 hTS⟩

  rw [
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
      hNS ht hE hTail hsS
  ]

  exact
    h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
      s hs

/-- If the local endpoint lies strictly inside the selected radius, the filled
field is spatially `C³` at every real time.

Inside `(0,S)` this is the old/preterminal regularity before `T` or selected
positive-time smoothing at and after `T`.  Outside `(0,S)` the slice is the
constant zero function. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_spatialC3
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
    RealVelocitySpatialC3
      (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
        hNS ht hE hTail S) := by
  intro s j

  by_cases hs : s ∈ Set.Ioo (0 : ℝ) S

  · rw [
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
        hNS ht hE hTail hs
    ]

    by_cases hBefore : s < T

    · exact
        h3PreterminalTailCanonicalSelectedOverlapGlue_spatialC3At_beforeT
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail
          ⟨hs.1, hBefore⟩
          j

    · have hTs : T ≤ s :=
        le_of_not_gt hBefore

      have hts : t < s :=
        lt_of_lt_of_le ht.2 hTs

      have hsR :
          s - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        have hsS : s < S := hs.2
        linarith

      exact
        h3PreterminalTailCanonicalSelectedOverlapGlue_spatialC3At_restartWindow
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail hEvolution
          hts hsR j

  · have hZero :
        SpatialC3
          (fun _ : Point3 => (0 : ℝ)) := by
      unfold SpatialC3
      exact contDiff_const

    have hFillZero :=
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_zero_of_not_mem
        hNS ht hE hTail hs

    have hComponent :
        (fun y : Point3 =>
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S s y).component j)
          =
        (fun _ : Point3 => (0 : ℝ)) := by
      funext y
      rw [hFillZero]

    rw [hComponent]

    exact hZero

/-- Filling outside `(0,S)` does not change terminal third-jet continuity when
`T` lies in that interval. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_thirdJetContinuousAt_terminal
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
    (hCross :
      T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (x : Point3) :
    RealVelocityThirdJetContinuousAt
      (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
        hNS ht hE hTail S)
      T
      x := by
  intro a b c j

  have hGlue :=
    h3PreterminalTailCanonicalSelectedOverlapGlue_thirdJetContinuousAt_terminal
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail hEvolution hCross x

  have hGlueComponent :=
    hGlue a b c j

  have hTPositive : 0 < T :=
    lt_trans ht.1 ht.2

  have hTInterior :
      T ∈ Set.Ioo (0 : ℝ) S :=
    ⟨hTPositive, hTS⟩

  have hNhds :
      Set.Ioo (0 : ℝ) S ∈ 𝓝 T :=
    isOpen_Ioo.mem_nhds hTInterior

  have hEventually :
      (fun s : ℝ =>
        spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d
              c
              (fun y =>
                (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                  hNS ht hE hTail S s y).component j)))
          x)
        =ᶠ[𝓝 T]
      (fun s : ℝ =>
        spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d
              c
              (fun y =>
                (h3PreterminalTailCanonicalSelectedOverlapGlue
                  (one_pos : (0 : ℝ) < 1)
                  hNS ht hE hTail s y).component j)))
          x) := by
    filter_upwards [hNhds] with s hs

    have hEq :=
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
        hNS ht hE hTail hs

    have hFunctions :
        (fun y =>
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S s y).component j)
          =
        (fun y =>
          (h3PreterminalTailCanonicalSelectedOverlapGlue
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail s y).component j) := by
      funext y
      rw [hEq]

    rw [hFunctions]

  exact
    hGlueComponent.congr_of_eventuallyEq
      hEventually

/-- The exact remaining normalized PDE statement at one retained H³ tail.

The crossing condition is supplied separately.  The PDE frontier only has to
choose an endpoint `S` strictly between the old terminal time and the selected
restart endpoint and provide a pressure for the filled canonical field there. -/
def H3PreterminalTailUnitViscosityLocalPDEAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E →
    ∃
      (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
      (S : ℝ),
        T < S
          ∧
        S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E
          ∧
        PreterminalNavierStokes3
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S)
          p
          S

/-- One local PDE witness plus physical-tail evolution already produces the
complete real restart package at this anchor. -/
theorem h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hCross :
      T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht hE hTail) :
    ∃
      (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
      (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
      (S : ℝ),
        T < S
          ∧
        RealRestartAgreesBeforeT u v T
          ∧
        PreterminalNavierStokes3 v p S
          ∧
        RealVelocitySpatialC3 v
          ∧
        (∀ x : Point3,
          RealVelocityThirdJetContinuousAt v T x) := by
  obtain ⟨p, S, hTS, hSR, hPDE⟩ :=
    hLocalPDE hCross

  let v :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
      hNS ht hE hTail S

  have hAgree :
      RealRestartAgreesBeforeT u v T := by
    dsimp only [v]
    exact
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_agreesBeforeT
        hNS ht hE hTail hTS

  have hSpatial :
      RealVelocitySpatialC3 v := by
    dsimp only [v]
    exact
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_spatialC3
        hNS ht hE hTail hEvolution hTS hSR

  have hThird :
      ∀ x : Point3,
        RealVelocityThirdJetContinuousAt v T x := by
    intro x
    dsimp only [v]
    exact
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_thirdJetContinuousAt_terminal
        hNS ht hE hTail hEvolution hTS hCross x

  exact
    ⟨
      v,
      p,
      S,
      hTS,
      hAgree,
      hPDE,
      hSpatial,
      hThird
    ⟩

/-- Unit-viscosity local PDE frontier for every retained canonical H³ tail for
which the explicit selected radius crosses `T`. -/
def H3PreterminalTailUnitViscosityLocalPDEFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht hE hTail

/-- The unit-viscosity strong/mild evolution frontier plus the genuinely local
normalized PDE frontier imply the real H³ restart theorem.

The restart anchor is chosen close enough to `T` that the explicit positive
spectral radius crosses the old terminal time. -/
theorem h3ControlProducesRealRestart_of_unitViscosityPhysicalTailFrontiers
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesRealRestart := by
  intro u T hAdmissible hTail

  rcases hTail with
    ⟨a, M, ha, hM, hBound⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE :
      1 ≤ E :=
    one_le_velocityH3CoordinateBudget hM

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  have hTailLength :
      0 < T - a := by
    linarith [ha.2]

  let ε : ℝ :=
    min
      ((T - a) / 2)
      (R / 2)

  have hHalfTail :
      0 < (T - a) / 2 := by
    linarith

  have hHalfRadius :
      0 < R / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - a) / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεRadius :
      ε ≤ R / 2 := by
    dsimp only [ε]
    exact min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have ht₀Lower :
      a ≤ t₀ := by
    dsimp only [t₀]
    linarith

  have ht₀Upper :
      t₀ < T := by
    dsimp only [t₀]
    linarith

  have ht₀Positive :
      0 < t₀ :=
    lt_of_lt_of_le ha.1 ht₀Lower

  have ht₀ :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht₀Positive, ht₀Upper⟩

  have hCanonicalTail :
      CanonicalH3TailDataFrom
        u t₀ T E := by
    intro s hs

    have hsOld :
        s ∈ Set.Ico a T :=
      ⟨le_trans ht₀Lower hs.1, hs.2⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsOld

    exact
      ⟨
        velocityH3IntegrableAt_of_bound hsBound,
        velocityH3EnergyAt_le_coordinateBudget_of_bound hsBound
      ⟩

  have hCross :
      T - t₀
        <
      h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    dsimp only [t₀, R] at hεRadius ⊢
    linarith

  have hEvo :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t₀ hAdmissible ht₀ hE hCanonicalTail :=
    hEvolution
      E hE u T t₀
      hAdmissible ht₀ hCanonicalTail

  have hPDEAt :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hAdmissible ht₀ hE hCanonicalTail :=
    hLocalPDE
      E hE u T t₀
      hAdmissible ht₀ hCanonicalTail

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hAdmissible ht₀ hE hCanonicalTail
      hEvo hCross hPDEAt

/-- Consequently, only the unit-viscosity physical-tail evolution frontier and
the local normalized PDE/pressure frontier remain before the original H³
continuation theorem. -/
theorem h3ControlProducesExtension_of_unitViscosityPhysicalTailFrontiers
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscosityPhysicalTailFrontiers
        hEvolution hLocalPDE)

end
end Euclidean
end Bridge
end PrimeTensor
