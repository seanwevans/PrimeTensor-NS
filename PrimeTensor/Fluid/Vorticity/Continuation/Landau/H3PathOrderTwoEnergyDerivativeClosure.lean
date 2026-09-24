import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedStrongL2FromCoefficientContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedEnergyReduction

/-!
# Close the old H³-path order-two energy derivative

The selected order-two Hilbert-space problem is now completely closed:
`h3CanonicalSelectedOrder2RelativeEnergyDerivativeOnRestartRadius_closed`
gives the exact elapsed-time derivative of the selected second-jet scalar
energy.

Two bookkeeping steps remain.

First, compose elapsed time with

    τ ↦ τ - t₀

to obtain the corresponding selected absolute-time scalar energy derivative.
The chain derivative is `1`, so only the temporal coefficient requires an
explicit equality; this follows from the already-closed selected temporal
regularity.

Second, repeat the selected/old germ transport already used at order one.
Local selected/old physical agreement gives equality of the scalar order-two
energy paths on a neighborhood of every strict H³ energy-class time.
`EventuallyEq.deriv_eq` identifies the selected temporal coefficient with the
old temporal derivative, and function equality transports both spatial
derivatives.

Thus the selected order-two theorem gives the exact old identity

    d/dt E₂(u,t) = F₂(u,t)

with no additional domination, PDE, pressure, or transport argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoEnergyDerivativeClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Relative selected energy → absolute selected energy -/

/-- Absolute-time form of the selected order-two scalar energy derivative. -/
def H3CanonicalSelectedOrder2EnergyDerivativeOnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ s : ℝ,
        s ∈
          Set.Ioo
            t₀
            (t₀ + h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        HasDerivAt
          (fun τ : ℝ =>
            ∑ j : PrimeTensor.Axis Depth.three,
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  spatialSquareEnergy
                    (spatial3.d i
                      (spatial3.d k
                        (fun y : Point3 =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            (h3PreterminalSelectedDecoderAnchorState
                              hNS ht₀ hTail)
                            (lt_of_lt_of_le zero_lt_one hE)
                            (norm_h3PreterminalSelectedDecoderAnchorState_le
                              hNS ht₀ hE hTail)
                            (τ - t₀)
                            y).component j))))
          (∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d i
                    (spatial3.d k
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          (h3PreterminalSelectedDecoderAnchorState
                            hNS ht₀ hTail)
                          (lt_of_lt_of_le zero_lt_one hE)
                          (norm_h3PreterminalSelectedDecoderAnchorState_le
                            hNS ht₀ hE hTail)
                          (s - t₀)
                          y).component j)))
                  (spatial3.d i
                    (spatial3.d k
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
                          s))))
          s

/-- The elapsed-time selected order-two energy derivative transports through
`τ ↦ τ - t₀` to the absolute-time selected statement. -/
theorem h3CanonicalSelectedOrder2EnergyDerivativeOnRestartRadius_of_relative
    (hRelative :
      H3CanonicalSelectedOrder2RelativeEnergyDerivativeOnRestartRadius) :
    H3CanonicalSelectedOrder2EnergyDerivativeOnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail
  intro s hs

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let q : ℝ :=
    s - t₀

  have hq0 : 0 < q := by
    dsimp only [q]
    exact sub_pos.mpr hs.1

  have hqR :
      q < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    dsimp only [q]
    linarith [hs.2]

  have hq :
      q ∈
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨hq0, hqR⟩

  have hRelativeAt :=
    hRelative
      E u T t₀ hNS ht₀ hE hTail
      q hq

  have hShift :
      HasDerivAt
        (fun τ : ℝ => τ - t₀)
        1
        s := by
    simpa using
      (hasDerivAt_id s).sub_const t₀

  have hAbsoluteRaw :
      HasDerivAt
        (fun τ : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d i
                    (spatial3.d k
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          U₀ hA hU₀
                          (τ - t₀)
                          y).component j))))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        U₀ hA hU₀
                        q y).component j)))
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      temporal.d
                        (fun r : ℝ =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            U₀ hA hU₀
                            r y).component j)
                        q))))
        s := by

    have hComp :=
      hRelativeAt.scomp s hShift

    simpa only [
      Function.comp_def,
      one_smul,
      q,
      U₀, hA, hU₀
    ] using hComp

  have hTemporalFieldEq
      (j : PrimeTensor.Axis Depth.three) :
      (fun y : Point3 =>
        temporal.d
          (fun τ : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (τ - t₀)
              y).component j)
          s)
        =
      (fun y : Point3 =>
        temporal.d
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          q) := by

    funext y

    have hRegularity :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        y j

    dsimp only at hRegularity

    have hfDiff :
        DifferentiableAt ℝ
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          q := by
      exact
        (hRegularity.1 q hq).differentiableAt
          (isOpen_Ioo.mem_nhds hq)

    have hf :
        HasDerivAt
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          (deriv
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀
                r
                y).component j)
            q)
          q :=
      hfDiff.hasDerivAt

    have hComp :=
      hf.comp s hShift

    change
      deriv
          (fun τ : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (τ - t₀)
              y).component j)
          s
        =
      deriv
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          q

    simpa only [
      Function.comp_def,
      mul_one,
      q
    ] using hComp.deriv

  have hCoefficientEq :
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      U₀ hA hU₀
                      q y).component j)))
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    temporal.d
                      (fun r : ℝ =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          U₀ hA hU₀
                          r y).component j)
                      q))))
        =
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      U₀ hA hU₀
                      (s - t₀) y).component j)))
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    temporal.d
                      (fun τ : ℝ =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          U₀ hA hU₀
                          (τ - t₀) y).component j)
                      s)))) := by

    apply Finset.sum_congr rfl
    intro j hj

    apply Finset.sum_congr rfl
    intro i hi

    apply Finset.sum_congr rfl
    intro k hk

    have hTime :
        spatial3.d i
            (spatial3.d k
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      U₀ hA hU₀
                      r y).component j)
                  q))
          =
        spatial3.d i
          (spatial3.d k
            (fun y : Point3 =>
              temporal.d
                (fun τ : ℝ =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    (one_pos : (0 : ℝ) < 1)
                    U₀ hA hU₀
                    (τ - t₀) y).component j)
                s)) :=
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i (spatial3.d k f))
        (hTemporalFieldEq j).symm

    rw [hTime]

  exact
    hAbsoluteRaw.congr_deriv
      hCoefficientEq

/-! ## Absolute selected energy → old H³ path energy -/

/-- Selected order-two scalar energy differentiation transports to the exact
old canonical order-two energy derivative at every strict H³ energy-class
time. -/
theorem h3PathEnergyClassProducesOrder2EnergyDerivativeIdentity_of_selected
    (hSelected :
      H3CanonicalSelectedOrder2EnergyDerivativeOnRestartRadius)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
      (velocityH3Energy2At u)
      (velocityH3FormalDerivative2At u s)
      s := by

  have hsAbs :
      s ∈ Set.Ioo (0 : ℝ) T :=
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
      ℝ →
        PrimeTensor.Axis Depth.three →
          ScalarField3 :=
    fun r j y =>
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
      (hr : r ∈ Set.Ioo t₀ upper)
      (j : PrimeTensor.Axis Depth.three) :
      selectedSlice r j
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

    have hqR' :
        r - t₀ ≤
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      dsimp only [R] at hrRAbs
      linarith

    let q :
        Set.Ioc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨r - t₀, hqPos, hqR'⟩

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
          convert hPoint using 1; ring)

  have hsLocal :
      s ∈ Set.Ioo t₀ upper :=
    ⟨hsRestart.1, hsUpper⟩

  have hEnergyEq :
      (fun r : ℝ =>
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d i
                  (spatial3.d k
                    (selectedSlice r j))))
        =ᶠ[𝓝 s]
      velocityH3Energy2At u := by

    filter_upwards [hNeighborhood] with r hr

    unfold velocityH3Energy2At

    apply Finset.sum_congr rfl
    intro j hj

    apply Finset.sum_congr rfl
    intro i hi

    apply Finset.sum_congr rfl
    intro k hk

    have hField :
        spatial3.d i
            (spatial3.d k
              (selectedSlice r j))
          =
        spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u r j)) :=
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i (spatial3.d k f))
        (hScalarEq r hr j)

    rw [hField]

  have hTimeEq
      (j : PrimeTensor.Axis Depth.three)
      (y : Point3) :
      (fun r : ℝ =>
        (logSpaceTimeVectorField u r y).component j)
        =ᶠ[𝓝 s]
      (fun r : ℝ =>
        selectedSlice r j y) := by

    filter_upwards [hNeighborhood] with r hr

    have hEq :=
      congrFun
        (hScalarEq r hr j)
        y

    simpa only [loggedVelocityComponent] using hEq.symm

  have hTemporalFieldEq
      (j : PrimeTensor.Axis Depth.three) :
      (fun y : Point3 =>
        temporal.d
          (fun r : ℝ =>
            selectedSlice r j y)
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
              selectedSlice r j y)
            s :=
      (hTimeEq j y).deriv_eq

    change
      deriv
          (fun r : ℝ =>
            selectedSlice r j y)
          s
        =
      deriv
          (fun r : ℝ =>
            (logSpaceTimeVectorField u r y).component j)
          s

    exact hDerivEq.symm

  have hBaseFieldEq
      (j : PrimeTensor.Axis Depth.three) :
      selectedSlice s j
        =
      loggedVelocityComponent u s j :=
    hScalarEq s hsLocal j

  have hCoefficientEq :
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i
                (spatial3.d k
                  (selectedSlice s j)))
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    temporal.d
                      (fun r : ℝ =>
                        selectedSlice r j y)
                      s))))
        =
      velocityH3FormalDerivative2At u s := by

    unfold velocityH3FormalDerivative2At

    apply Finset.sum_congr rfl
    intro j hj

    apply Finset.sum_congr rfl
    intro i hi

    apply Finset.sum_congr rfl
    intro k hk

    have hBase :
        spatial3.d i
            (spatial3.d k
              (selectedSlice s j))
          =
        spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u s j)) :=
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i (spatial3.d k f))
        (hBaseFieldEq j)

    have hTime :
        spatial3.d i
            (spatial3.d k
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    selectedSlice r j y)
                  s))
          =
        spatial3.d i
          (spatial3.d k
            (loggedVelocityTemporalComponent u s j)) :=
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i (spatial3.d k f))
        (hTemporalFieldEq j)

    rw [hBase, hTime]

  have hSelectedAt :
      HasDerivAt
        (fun τ : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d i
                    (spatial3.d k
                      (selectedSlice τ j))))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (selectedSlice s j)))
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      temporal.d
                        (fun τ : ℝ =>
                          selectedSlice τ j y)
                        s))))
        s := by

    dsimp only [selectedSlice]

    exact
      hSelected
        E u S t₀
        hNSShort ht₀ hE hTail
        s
        (by
          simpa only [R] using hsRestart)

  have hOldRaw :
      HasDerivAt
        (velocityH3Energy2At u)
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (selectedSlice s j)))
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      temporal.d
                        (fun τ : ℝ =>
                          selectedSlice τ j y)
                        s))))
        s :=
    hSelectedAt.congr_of_eventuallyEq
      hEnergyEq.symm

  exact
    hOldRaw.congr_deriv
      hCoefficientEq

/-! ## Closed order-two identity -/

/-- The old H³ path order-two energy derivative identity is now closed
outright. -/
theorem h3PathEnergyClassProducesOrder2EnergyDerivativeIdentity_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
      (velocityH3Energy2At u)
      (velocityH3FormalDerivative2At u s)
      s := by

  exact
    h3PathEnergyClassProducesOrder2EnergyDerivativeIdentity_of_selected
      (h3CanonicalSelectedOrder2EnergyDerivativeOnRestartRadius_of_relative
        h3CanonicalSelectedOrder2RelativeEnergyDerivativeOnRestartRadius_closed)
      hH3 hClass hs

end

end Euclidean
end Bridge
end PrimeTensor
