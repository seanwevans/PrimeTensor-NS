import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Closure

/-!
# Reduce H³-path order-three mixed commutation to the selected restart

The order-two mixed-time branch is now closed.  The remaining higher mixed
commutation input in the H³ energy argument is order three:

    d/dt (D³u) = D³(∂ₜu).

As at order two, the old/path statement contains no new analytic difficulty
once a local canonical selected restart is available.  Around each strict
target time, the already-closed selected/old physical agreement identifies the
entire scalar spatial slice on an open time neighborhood.  Equality of fields
therefore transports all three concrete spatial derivatives at once, while
eventual equality of the pointwise time paths transports the temporal
derivative coefficient.

This file isolates the exact remaining selected-side analytic target and proves
that it implies the old H³-path order-three commutation frontier.

No new estimate, selected-side differentiation, or uniform terminal-tail H³
bound is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3PathOrder3SelectedReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Selected order-three target -/

/--
The exact selected-side order-three mixed derivative needed by the H³ energy
argument, written in absolute time.

The restart is parameterized by elapsed time `τ - t₀`, while the
`HasDerivAt` statement is based at the absolute target time `s`.
-/
def H3CanonicalSelectedOrder3MixedTimeCommutationOnRestartRadius : Prop :=
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
            (j i k l : PrimeTensor.Axis Depth.three)
            (x : Point3),
              HasDerivAt
                (fun τ : ℝ =>
                  spatial3.d
                    i
                    (spatial3.d
                      k
                      (spatial3.d
                        l
                        (fun y : Point3 =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            (h3PreterminalSelectedDecoderAnchorState
                              hNS ht₀ hTail)
                            (lt_of_lt_of_le zero_lt_one hE)
                            (norm_h3PreterminalSelectedDecoderAnchorState_le
                              hNS ht₀ hE hTail)
                            (τ - t₀)
                            y).component j)))
                    x)
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (spatial3.d
                      l
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
                          s)))
                  x)
                s

/-! ## Transport selected order three to the old H³ path -/

/--
The selected positive-time order-three theorem implies old H³-path order-three
mixed commutation.

All selected/old equality needed for the transport is supplied by the same
local canonical restart and pressure-free curl weak-FTC closure already used at
order two.
-/
theorem h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail_of_selected
    (hSelected :
      H3CanonicalSelectedOrder3MixedTimeCommutationOnRestartRadius) :
    H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail := by

  intro u T hH3 a hClass

  intro s hs j i k l x

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
      linarith [hrS]

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
            (spatial3.d
              l
              (selectedSlice r)))
          x)
        =ᶠ[𝓝 s]
      (fun r : ℝ =>
        spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (loggedVelocityComponent u r j)))
          x) := by

    filter_upwards [hNeighborhood] with r hr

    exact
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i
            (spatial3.d k
              (spatial3.d l f))
            x)
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
            (spatial3.d
              l
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    selectedSlice r y)
                  s)))
          x
        =
      spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (loggedVelocityTemporalComponent u s j)))
          x :=
    congrArg
      (fun f : ScalarField3 =>
        spatial3.d i
          (spatial3.d k
            (spatial3.d l f))
          x)
      hTemporalFieldEq

  have hSelectedAt :
      HasDerivAt
        (fun τ : ℝ =>
          spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (selectedSlice τ)))
            x)
        (spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (fun y : Point3 =>
                temporal.d
                  (fun τ : ℝ =>
                    selectedSlice τ y)
                  s)))
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
        j i k l x

  have hOldRaw :
      HasDerivAt
        (fun r : ℝ =>
          spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityComponent u r j)))
            x)
        (spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    selectedSlice r y)
                  s)))
          x)
        s :=
    hSelectedAt.congr_of_eventuallyEq
      hSpatialEq.symm

  exact
    hOldRaw.congr_deriv
      hCoefficientEq

/-! ## BKM endpoint with both old mixed-commutation branches removed -/

/--
After the closed order-two theorem, the only remaining mixed-commutation input
to this BKM reduction is the selected order-three restart theorem.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_selectedOrder3_of_majorants_of_growth
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hSelected3 :
      H3CanonicalSelectedOrder3MixedTimeCommutationOnRestartRadius)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_orderwiseMixed_of_majorants_of_growth
      hLow
      h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail
      (h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail_of_selected
        hSelected3)
      hMajorants
      hGrowth

end

end Euclidean
end Bridge
end PrimeTensor
