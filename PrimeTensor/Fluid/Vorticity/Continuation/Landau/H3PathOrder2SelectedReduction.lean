import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderwiseMixedCommutation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.H3PathAdmissible
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongCurlWeakFTCGlobalClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Mixed.Derivative.Absolute.Time

/-!
# Reduce H³-path order-two mixed commutation to the selected restart

`H3PathOrderwiseMixedCommutation` split the higher mixed-time obstruction into
independent order-two and order-three statements.

This file removes all old-branch overlap bookkeeping from the order-two side.

For every strict target time of an H³-path-admissible solution:

1. scalar H³-energy continuity supplies a bounded local canonical restart
   window around the target;
2. the already-closed pressure-free curl weak-FTC argument gives pointwise
   selected/old physical agreement at every positive elapsed time in that
   window;
3. therefore the selected and old scalar spatial slices are equal on an open
   time neighborhood of the target;
4. `HasDerivAt.congr_of_eventuallyEq` transports an order-two selected mixed
   derivative to the old branch;
5. `EventuallyEq.deriv_eq` transports the temporal coefficient, so the
   derivative value becomes exactly `D²(∂ₜu)` for the old velocity.

Hence the remaining order-two analytic task is purely selected-side:
positive-time differentiation of the second spatial derivative of the canonical
restart.

No uniform terminal-tail H³ bound is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3PathOrder2SelectedReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Selected order-two target -/

/--
The exact selected-side order-two mixed derivative needed by the H³ energy
argument, written in absolute time.

The restart is parameterized by elapsed time `τ - t₀`, but the
`HasDerivAt` statement is based at the absolute time `s`.  This is the natural
shape for transport through selected/old overlap.
-/
def H3CanonicalSelectedOrder2MixedTimeCommutationOnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀
        (s : ℝ),
          s ∈
            Set.Ioo
              t₀
              (t₀ + h3FinHeatLerayRestartRadius (1 : ℝ) E) →
          ∀
            (j i k : PrimeTensor.Axis Depth.three)
            (x : Point3),
              HasDerivAt
                (fun τ : ℝ =>
                  spatial3.d
                    i
                    (spatial3.d
                      k
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          (h3PreterminalSelectedDecoderAnchorState
                            hNS ht₀ hTail)
                          (lt_of_lt_of_le zero_lt_one hE)
                          (norm_h3PreterminalSelectedDecoderAnchorState_le
                            hNS ht₀ hE hTail)
                          (τ - t₀)
                          y).component j))
                    x)
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (fun y : Point3 =>
                      temporal.d
                        (fun τ : ℝ =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            (h3PreterminalSelectedDecoderAnchorState
                              hNS ht₀ hTail)
                            (lt_of_lt_of_le zero_lt_one hE)
                            (norm_h3PreterminalSelectedDecoderAnchorState_le
                              hNS ht₀ hE hTail)
                            (τ - t₀)
                            y).component j)
                        s))
                  x)
                s

/-! ## Transport selected order two to the old H³ path -/

/--
The selected positive-time order-two theorem implies old H³-path order-two
mixed commutation.

All selected/old equality needed for the transport is already automatic from
the canonical H³ local restart and the pressure-free curl weak-FTC closure.
-/
theorem h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail_of_selected
    (hSelected :
      H3CanonicalSelectedOrder2MixedTimeCommutationOnRestartRadius) :
    H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail := by

  intro u T hH3 a hClass

  intro s hs j i k x

  have hsAbs :
      s ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans hClass.terminal_start.1 hs.1,
        hs.2
      ⟩

  rcases
    hH3.exists_localCanonicalRestartWindowAt hsAbs
  with
    ⟨
      t₀,
      S,
      E,
      ht₀,
      hST,
      hE,
      hTail,
      hq0,
      hqR,
      hts,
      hsS
    ⟩

  have hS :
      0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes
      hS
      (le_of_lt hST)

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hsRestart :
      s ∈ Set.Ioo t₀ (t₀ + R) := by
    constructor
    · linarith [hq0]
    · dsimp only [R]
      linarith [hqR]

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₀ hNSShort ht₀ hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₀ hNSShort ht₀ hTail

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u S t₀ hNSShort ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort
      ht₀
      hE
      hTail
      hWeakFTC

  let upper : ℝ :=
    min S (t₀ + R)

  have hsUpper :
      s < upper := by
    dsimp only [upper]
    exact
      lt_min
        hsS
        hsRestart.2

  have hNeighborhood :
      Set.Ioo t₀ upper ∈ 𝓝 s :=
    Ioo_mem_nhds
      hsRestart.1
      hsUpper

  let selectedSlice :
      ℝ → ScalarField3 :=
    fun r y =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNSShort ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNSShort ht₀ hE hTail)
        (r - t₀)
        y).component j

  have hScalarEq
      (r : ℝ)
      (hr : r ∈ Set.Ioo t₀ upper) :
      selectedSlice r
        =
      loggedVelocityComponent u r j := by

    have hrS :
        r < S := by
      exact
        lt_of_lt_of_le
          hr.2
          (by
            dsimp only [upper]
            exact min_le_left _ _)

    have hrRAbs :
        r < t₀ + R := by
      exact
        lt_of_lt_of_le
          hr.2
          (by
            dsimp only [upper]
            exact min_le_right _ _)

    have hqPos :
        0 < r - t₀ := by
      linarith [hr.1]

    have hqR :
        r - t₀ ≤
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      dsimp only [R] at hrRAbs
      linarith

    let q :
        Set.Ioc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨r - t₀, hqPos, hqR⟩

    have hEnd :
        t₀ + (q : ℝ) < S := by
      dsimp only [q]
      linarith

    have hAgreement :
        H3PreterminalSelectedPhysicalAgreementAt
          (one_pos : (0 : ℝ) < 1)
          (q : ℝ)
          hNSShort ht₀ hE hTail :=
      hPhysical q hEnd

    let jj : Fin 3 :=
      h3ClassicalizationFinOfAxis j

    funext y

    have hPoint :=
      hAgreement jj y

    dsimp only [q] at hPoint
    dsimp only [jj] at hPoint

    rw [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j
    ] at hPoint

    dsimp only [selectedSlice]

    simpa only [
      loggedVelocityComponent
    ] using
      (show
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNSShort ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNSShort ht₀ hE hTail)
              (r - t₀)
              y).component j
          =
        (logSpaceTimeVectorField u r y).component j by
          convert hPoint using 1 <;> ring)

  have hSpatialEq :
      (fun r : ℝ =>
        spatial3.d
          i
          (spatial3.d
            k
            (selectedSlice r))
          x)
        =ᶠ[𝓝 s]
      (fun r : ℝ =>
        spatial3.d
          i
          (spatial3.d
            k
            (loggedVelocityComponent u r j))
          x) := by

    filter_upwards [hNeighborhood] with r hr

    exact
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i (spatial3.d k f) x)
        (hScalarEq r hr)

  have hTimeEq
      (y : Point3) :
      (fun r : ℝ =>
        (logSpaceTimeVectorField u r y).component j)
        =ᶠ[𝓝 s]
      (fun r : ℝ =>
        selectedSlice r y) := by

    filter_upwards [hNeighborhood] with r hr

    have hEq :=
      congrFun
        (hScalarEq r hr)
        y

    simpa only [loggedVelocityComponent] using hEq.symm

  have hTemporalFieldEq :
      (fun y : Point3 =>
        temporal.d
          (fun r : ℝ =>
            selectedSlice r y)
          s)
        =
      loggedVelocityTemporalComponent u s j := by

    funext y

    have hDerivEq :
        deriv
            (fun r : ℝ =>
              (logSpaceTimeVectorField u r y).component j)
            s
          =
        deriv
            (fun r : ℝ =>
              selectedSlice r y)
            s :=
      (hTimeEq y).deriv_eq

    change
      deriv
          (fun r : ℝ =>
            selectedSlice r y)
          s
        =
      deriv
          (fun r : ℝ =>
            (logSpaceTimeVectorField u r y).component j)
          s

    exact hDerivEq.symm

  have hCoefficientEq :
      spatial3.d
          i
          (spatial3.d
            k
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  selectedSlice r y)
                s))
          x
        =
      spatial3.d
          i
          (spatial3.d
            k
            (loggedVelocityTemporalComponent u s j))
          x :=
    congrArg
      (fun f : ScalarField3 =>
        spatial3.d i (spatial3.d k f) x)
      hTemporalFieldEq

  have hSelectedAt :
      HasDerivAt
        (fun τ : ℝ =>
          spatial3.d
            i
            (spatial3.d
              k
              (selectedSlice τ))
            x)
        (spatial3.d
          i
          (spatial3.d
            k
            (fun y : Point3 =>
              temporal.d
                (fun τ : ℝ =>
                  selectedSlice τ y)
                s))
          x)
        s := by

    dsimp only [selectedSlice]

    exact
      hSelected
        E u S t₀
        hNSShort ht₀ hE hTail
        s
        (by
          simpa only [R] using hsRestart)
        j i k x

  have hOldRaw :
      HasDerivAt
        (fun r : ℝ =>
          spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityComponent u r j))
            x)
        (spatial3.d
          i
          (spatial3.d
            k
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  selectedSlice r y)
                s))
          x)
        s :=
    hSelectedAt.congr_of_eventuallyEq
      hSpatialEq.symm

  exact
    hOldRaw.congr_deriv
      hCoefficientEq

/-! ## BKM endpoint with old order two removed -/

/--
BKM continuation after replacing the old/path order-two commutation hypothesis
by the purely selected positive-time order-two target.

The remaining differentiation inputs are now:

* selected canonical order-two mixed differentiation;
* H³-path order-three mixed commutation;
* derivative majorants.

Thus the next analytic increment may work entirely inside the selected
restart calculus for order two.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_selectedOrder2_of_order3Mixed_of_majorants_of_growth
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hSelected2 :
      H3CanonicalSelectedOrder2MixedTimeCommutationOnRestartRadius)
    (hMixed3 :
      H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_orderwiseMixed_of_majorants_of_growth
      hLow
      (h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail_of_selected
        hSelected2)
      hMixed3
      hMajorants
      hGrowth

end

end Euclidean
end Bridge
end PrimeTensor
