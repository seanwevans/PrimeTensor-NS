import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Forcing.Pairing.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Transport.Physical.L2.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalWeak

/-!
# Selected--old weak--strong advection representatives

The forcing-pairing bridge has reduced the nonlinear Leray term to the
quotient-safe physical `L²` vectors

    A_selected,  A_old,

obtained from the unprojected raw outer-product divergences.

The transport stack, however, is written with the literal classical fields

    S(s,x) = selected restart velocity,
    O(s,x) = old velocity at absolute time t+s,

and their explicit advection components `realAdvectionComponent`.

This file closes that representation seam.

For the selected slice, the constant spectral path at the state `U_selected(q)`
has exactly the same real spatial slice as the selected restart velocity at
elapsed time `q`.

For the old slice, the existing canonical snapshot component identity gives the
same statement pointwise for the constant path at `U_old(q)` and the logged old
velocity at absolute time `t+q`.

Consequently the generic quotient-safe physical advection coordinates have the
actual classical advection components as almost-everywhere representatives on
both branches.

No energy estimate, cancellation, or integration by parts is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAdvectionRepresentatives
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A constant spectral path at the selected unit-viscosity state has exactly
the selected restart's real spatial velocity slice. -/
theorem h3SpectralRealVelocityOfPath_const_selectedUnit_eq_selectedWeakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    h3SpectralRealVelocityOfPath
        (fun _ : ℝ =>
          h3PreterminalSelectedUnitSpectralStateOnRadius
            hNS ht hE hTail q)
        0
      =
    (h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail)
      (q : ℝ) := by
  funext x

  apply tensor_eq_of_component_eq
  intro a

  unfold
    h3PreterminalSelectedWeakStrongVelocity
    h3PreterminalSelectedUnitSpectralStateOnRadius
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

  rfl

/-- A constant spectral path at an old canonical elapsed snapshot has exactly
the logged old physical velocity slice at absolute time `t+q`. -/
theorem h3SpectralRealVelocityOfPath_const_oldElapsed_eq_oldWeakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3SpectralRealVelocityOfPath
        (fun _ : ℝ =>
          h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q)
        0
      =
    (h3PreterminalOldElapsedWeakStrongVelocity u t)
      (q : ℝ) := by
  funext x

  apply tensor_eq_of_component_eq
  intro a

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis a

  have hAxis :
      h3AxisOfFin3 k = a := by
    dsimp only [k]
    cases a with
    | first =>
        rfl
    | next a =>
        cases a with
        | first =>
            rfl
        | next a =>
            cases a with
            | first =>
                rfl

  have hComponent :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed_component_eq_old
      hNS ht hEnd hTail q k

  have hx := congrFun hComponent x

  change
    h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        (h3ClassicalizationFinOfAxis a)
        x
      =
    ((h3PreterminalOldElapsedWeakStrongVelocity u t)
      (q : ℝ) x).component a

  unfold h3PreterminalOldElapsedWeakStrongVelocity

  calc
    h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        (h3ClassicalizationFinOfAxis a)
        x
        =
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3
          (h3ClassicalizationFinOfAxis a))
        x := by
          simpa only [k] using hx
    _ =
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        a
        x := by
          exact
            congrArg
              (fun j : PrimeTensor.Axis Depth.three =>
                loggedVelocityComponent
                  u (t + (q : ℝ)) j x)
              hAxis
    _ =
      (logSpaceTimeVectorField
        u
        (t + (q : ℝ))
        x).component a := by
          rfl

/-- The quotient-safe selected unprojected physical nonlinear coordinate is
represented almost everywhere by the actual selected classical advection
component at elapsed time `q`. -/
theorem h3WeakStrongAdvectionPhysicalL2_selectedUnit_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    ((h3WeakStrongAdvectionPhysicalL2
        (h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail q)
        i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      realAdvectionComponent
        (h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
        (q : ℝ)
        x
        (h3AxisOfFin3 i)) := by
  let U :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q

  let S :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hGeneric :=
    h3WeakStrongAdvectionPhysicalL2_ae
      U
      (by
        dsimp only [U]
        exact
          h3PreterminalSelectedUnitSpectralStateOnRadius_realizable
            hNS ht hE hTail q)
      (by
        dsimp only [U]
        exact
          h3PreterminalSelectedUnitSpectralStateOnRadius_rawDivergenceFree
            hNS ht hE hTail q)
      i

  have hVelocity :
      h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U)
          0
        =
      S (q : ℝ) := by
    dsimp only [U, S]
    exact
      h3SpectralRealVelocityOfPath_const_selectedUnit_eq_selectedWeakStrong
        hNS ht hE hTail q

  filter_upwards [hGeneric] with x hx

  calc
    (h3WeakStrongAdvectionPhysicalL2 U i : H3ScalarL2) x
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U))
        0 x).component
          (h3AxisOfFin3 i) :=
      hx
    _ =
      realAdvectionComponent
        (h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U))
        0 x
        (h3AxisOfFin3 i) := by
          exact
            realFluid_advection_component_eq_realAdvectionComponent_zeroWeak
              (h3SpectralRealVelocityOfPath
                (fun _ : ℝ => U))
              0 x
              (h3AxisOfFin3 i)
    _ =
      realAdvectionComponent
        S
        (q : ℝ)
        x
        (h3AxisOfFin3 i) := by
          unfold realAdvectionComponent
          rw [hVelocity]

/-- The quotient-safe old unprojected physical nonlinear coordinate is
represented almost everywhere by the actual old classical advection component
at absolute time `t+q`, equivalently elapsed time `q` in the old weak--strong
field. -/
theorem h3WeakStrongAdvectionPhysicalL2_oldElapsed_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    ((h3WeakStrongAdvectionPhysicalL2
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      realAdvectionComponent
        (h3PreterminalOldElapsedWeakStrongVelocity u t)
        (q : ℝ)
        x
        (h3AxisOfFin3 i)) := by
  let U :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let O :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  have hGeneric :=
    h3WeakStrongAdvectionPhysicalL2_ae
      U
      (by
        dsimp only [U]
        exact
          h3PreterminalTailCanonicalSpectralStateOnElapsed_realizable
            hNS ht hEnd hTail q)
      (by
        dsimp only [U]
        exact
          h3PreterminalTailCanonicalSpectralStateOnElapsed_rawDivergenceFree
            hNS ht hEnd hTail q)
      i

  have hVelocity :
      h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U)
          0
        =
      O (q : ℝ) := by
    dsimp only [U, O]
    exact
      h3SpectralRealVelocityOfPath_const_oldElapsed_eq_oldWeakStrong
        hNS ht hEnd hTail q

  filter_upwards [hGeneric] with x hx

  calc
    (h3WeakStrongAdvectionPhysicalL2 U i : H3ScalarL2) x
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U))
        0 x).component
          (h3AxisOfFin3 i) :=
      hx
    _ =
      realAdvectionComponent
        (h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U))
        0 x
        (h3AxisOfFin3 i) := by
          exact
            realFluid_advection_component_eq_realAdvectionComponent_zeroWeak
              (h3SpectralRealVelocityOfPath
                (fun _ : ℝ => U))
              0 x
              (h3AxisOfFin3 i)
    _ =
      realAdvectionComponent
        O
        (q : ℝ)
        x
        (h3AxisOfFin3 i) := by
          unfold realAdvectionComponent
          rw [hVelocity]

end

end Euclidean
end Bridge
end PrimeTensor
