import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderZeroEnergyDerivativeClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder2SelectedReduction

/-!
# Reduce the first-order H³ energy derivative to the selected restart

Order zero is now closed outright.  At order one the old preterminal
regularity already supplies the genuine mixed derivative

    d/dt (∂ᵢuⱼ) = ∂ᵢ(∂ₜuⱼ).

Thus the historical order-one obstruction is not mixed commutation; it is only
the differentiation of the whole-space square integral.

This file moves that last order-one analytic task entirely to the smooth
selected restart.

For one canonical restart define the selected first-order scalar energy by

    Σⱼ Σᵢ ∫ |∂ᵢ Sⱼ|².

Its candidate derivative is the corresponding finite sum of selected
`spatialEnergyPairing`s with the selected absolute-time temporal derivative.

Assume only that this selected scalar energy has that derivative on every
strict positive restart time.  Local selected/old physical agreement then
gives, on a neighborhood of any strict H³-path energy-class time,

    S(τ) = u(τ).

Function equality transports all first spatial derivatives.  Germ equality
therefore transports the scalar `HasDerivAt`, while `EventuallyEq.deriv_eq`
identifies the selected temporal coefficient with the old temporal derivative.

Consequently the selected order-one scalar theorem implies the exact canonical

    HasDerivAt
      (velocityH3Energy1At u)
      (velocityH3FormalDerivative1At u s)
      s.

No old-branch domination package is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedEnergyReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Pure selected-restart order-one scalar energy differentiation target.

The path is written in absolute time, while the selected restart itself is
evaluated at elapsed time `τ - t₀`.
-/
def H3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius : Prop :=
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
                spatialSquareEnergy
                  (spatial3.d
                    i
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
          (∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d
                  i
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      (h3PreterminalSelectedDecoderAnchorState
                        hNS ht₀ hTail)
                      (lt_of_lt_of_le zero_lt_one hE)
                      (norm_h3PreterminalSelectedDecoderAnchorState_le
                        hNS ht₀ hE hTail)
                      (s - t₀)
                      y).component j))
                (spatial3.d
                  i
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
          s

/--
Selected first-order scalar energy differentiation transports to the exact old
canonical first-order energy derivative at every strict H³ energy-class time.
-/
theorem h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selected
    (hSelected :
      H3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
      (velocityH3Energy1At u)
      (velocityH3FormalDerivative1At u s)
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
          convert hPoint using 1 <;> ring)

  have hsLocal :
      s ∈ Set.Ioo t₀ upper :=
    ⟨hsRestart.1, hsUpper⟩

  have hEnergyEq :
      (fun r : ℝ =>
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (spatial3.d i (selectedSlice r j)))
        =ᶠ[𝓝 s]
      velocityH3Energy1At u := by
    filter_upwards [hNeighborhood] with r hr

    unfold velocityH3Energy1At

    apply Finset.sum_congr rfl
    intro j hj

    apply Finset.sum_congr rfl
    intro i hi

    have hField :
        spatial3.d i (selectedSlice r j)
          =
        spatial3.d i (loggedVelocityComponent u r j) :=
      congrArg
        (spatial3.d i)
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
          spatialEnergyPairing
            (spatial3.d i (selectedSlice s j))
            (spatial3.d
              i
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    selectedSlice r j y)
                  s)))
        =
      velocityH3FormalDerivative1At u s := by
    unfold velocityH3FormalDerivative1At

    apply Finset.sum_congr rfl
    intro j hj

    apply Finset.sum_congr rfl
    intro i hi

    have hBase :
        spatial3.d i (selectedSlice s j)
          =
        spatial3.d i
          (loggedVelocityComponent u s j) :=
      congrArg
        (spatial3.d i)
        (hBaseFieldEq j)

    have hTime :
        spatial3.d
            i
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  selectedSlice r j y)
                s)
          =
        spatial3.d
          i
          (loggedVelocityTemporalComponent u s j) :=
      congrArg
        (spatial3.d i)
        (hTemporalFieldEq j)

    rw [hBase, hTime]

  have hSelectedAt :
      HasDerivAt
        (fun τ : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d i (selectedSlice τ j)))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i (selectedSlice s j))
              (spatial3.d
                i
                (fun y : Point3 =>
                  temporal.d
                    (fun τ : ℝ =>
                      selectedSlice τ j y)
                    s)))
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
        (velocityH3Energy1At u)
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i (selectedSlice s j))
              (spatial3.d
                i
                (fun y : Point3 =>
                  temporal.d
                    (fun τ : ℝ =>
                      selectedSlice τ j y)
                    s)))
        s :=
    hSelectedAt.congr_of_eventuallyEq
      hEnergyEq.symm

  exact
    hOldRaw.congr_deriv
      hCoefficientEq

/--
Order zero is closed outright, so a selected order-one scalar theorem gives the
first two canonical energy derivative identities together.
-/
theorem h3PathEnergyClassProducesOrder01EnergyDerivativeIdentities_of_selected
    (hSelected :
      H3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
        (velocityH3Energy0At u)
        (velocityH3FormalDerivative0At u s)
        s
      ∧
    HasDerivAt
        (velocityH3Energy1At u)
        (velocityH3FormalDerivative1At u s)
        s := by
  exact
    ⟨
      h3PathEnergyClassProducesOrder0EnergyDerivativeIdentity_closed
        hH3 hClass hs,
      h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selected
        hSelected hH3 hClass hs
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
