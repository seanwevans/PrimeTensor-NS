import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAdvectionRepresentatives
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongTransportCancellation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Pressure.Classical.Bridge

/-!
# Selected--old weak--strong transport pairing bound

The Fourier/Leray side is now finished:

    ⟪D, NΔ⟫
      =
    ⟪D, A_selected - A_old⟫,

and the two quotient-safe physical advection vectors have the actual classical
advection components as almost-everywhere representatives.

This file performs the physical relative-energy calculation.

Write

    S = selected restart velocity,
    O(s) = old velocity at absolute time t+s,
    D = S - O.

Componentwise,

    (S·∇)S - (O·∇)O
      =
    (D·∇)S + O·∇D.

The old branch is a genuine preterminal Navier--Stokes solution at absolute
time `t+q`.  An honest whole-space scalar transport IBP datum therefore kills

    ∫ D_j (O·∇D_j) = 0

for each coordinate.

The surviving signed weak--strong density is bounded in absolute value by the
already-established absolute interaction density.  Combining that with

    ∫ absInteraction ≤ 3 B ‖D‖²

gives the exact nonlinear energy estimate required downstream:

    -2 ⟪D, NΔ⟫ ≤ 6 B ‖D‖².

At this checkpoint the remaining analytic inputs are explicit:

* a coordinatewise selected-gradient envelope `B`;
* integrability of the absolute interaction density;
* honest old-transport whole-space IBP for the three difference coordinates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportPairingBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One coordinate of the surviving weak--strong interaction
`D_j ((D · ∇)S_j)`.  Keeping this coordinate product behind a named
definition prevents `Fin 3` specialization from unfolding the vector value
down to the raw tensor `IndexTuple` projection. -/
noncomputable def selectedOldWeakStrongSelectedGradientProduct
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=
  ((selected s x).component j - (old s x).component j)
    *
  realAdvectionSelectedGradientDifferenceComponent
    selected old s x j

/-- Signed three-component weak--strong interaction density. -/
noncomputable def selectedOldWeakStrongSignedInteractionDensity
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3) : ℝ :=
  selectedOldWeakStrongSelectedGradientProduct
      selected old s x xAxis
    +
  (
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x yAxis
      +
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x zAxis
  )

/-- The signed weak--strong density is pointwise dominated by the sum of the
three absolute interaction densities. -/
theorem abs_selectedOldWeakStrongSignedInteractionDensity_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3) :
    abs
        (selectedOldWeakStrongSignedInteractionDensity
          selected old s x)
      ≤
    selectedOldWeakStrongAbsInteractionDensity
      selected old s x := by
  let px : ℝ :=
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x xAxis

  let py : ℝ :=
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x yAxis

  let pz : ℝ :=
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x zAxis

  have hxy :
      abs (py + pz) ≤ abs py + abs pz :=
    abs_add_le py pz

  have hx :
      abs (px + (py + pz))
        ≤
      abs px + abs (py + pz) :=
    abs_add_le px (py + pz)

  have hSigned :
      selectedOldWeakStrongSignedInteractionDensity
          selected old s x
        =
      px + (py + pz) := by
    rfl

  have hDensity :
      selectedOldWeakStrongAbsInteractionDensity
          selected old s x
        =
      abs px + (abs py + abs pz) := by
    rfl

  rw [hSigned, hDensity]

  linarith

/-- One selected-gradient interaction coordinate is a continuous
physical-space function whenever both velocity slices are spatially `C¹`. -/
theorem selectedOldWeakStrongSelectedGradientProduct_continuous
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected s x).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old s x).component k)) :
    Continuous
      (selectedOldWeakStrongSelectedGradientProduct
        selected old s · j) := by
  have hDifference
      (k : PrimeTensor.Axis Depth.three) :
      Continuous
        (fun x : Point3 =>
          (selected s x).component k
            -
          (old s x).component k) :=
    (hSelected k).continuous.sub (hOld k).continuous

  have hDerivative
      (a : PrimeTensor.Axis Depth.three) :
      Continuous
        (spatial3.d
          a
          (fun y : Point3 =>
            (selected s y).component j)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      (hSelected j) a

  unfold
    selectedOldWeakStrongSelectedGradientProduct
    realAdvectionSelectedGradientDifferenceComponent

  exact
    (hDifference j).mul
      (((hDifference xAxis).mul (hDerivative xAxis)).add
        (((hDifference yAxis).mul (hDerivative yAxis)).add
          ((hDifference zAxis).mul (hDerivative zAxis))))

/-- Every one of the three selected-gradient interaction coordinates is
pointwise dominated by the full absolute weak--strong interaction density. -/
theorem abs_selectedOldWeakStrongSelectedGradientProduct_le_absDensity
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3)
    (i : Fin 3) :
    abs
        (selectedOldWeakStrongSelectedGradientProduct
          selected old s x (h3AxisOfFin3 i))
      ≤
    selectedOldWeakStrongAbsInteractionDensity
      selected old s x := by
  let px : ℝ :=
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x xAxis

  let py : ℝ :=
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x yAxis

  let pz : ℝ :=
    selectedOldWeakStrongSelectedGradientProduct
      selected old s x zAxis

  have hx : 0 ≤ abs px := abs_nonneg px
  have hy : 0 ≤ abs py := abs_nonneg py
  have hz : 0 ≤ abs pz := abs_nonneg pz

  have hDensity :
      selectedOldWeakStrongAbsInteractionDensity
          selected old s x
        =
      abs px + (abs py + abs pz) := by
    rfl

  rw [hDensity]

  fin_cases i

  · change abs px ≤ abs px + (abs py + abs pz)
    linarith

  · change abs py ≤ abs px + (abs py + abs pz)
    linarith

  · change abs pz ≤ abs px + (abs py + abs pz)
    linarith

/-- The selected restart velocity is spatially `C¹` componentwise at every
restart-relative time. -/
theorem h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (fun x : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          hν hNS ht hE hTail)
          s x).component j) := by
  unfold
    h3PreterminalSelectedWeakStrongVelocity
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

  change
    SpatialC1
      (h3SpectralScalarRealC1RepresentativeOnPoint3
        ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν
          (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht hE hTail)
          s)
          (h3ClassicalizationFinOfAxis j)))

  exact
    h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
      ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν
        (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht hE hTail)
        s)
        (h3ClassicalizationFinOfAxis j))

/-- The elapsed old weak--strong velocity is spatially `C¹` componentwise at
every closed elapsed time. -/
theorem h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (_hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (fun x : Point3 =>
        ((h3PreterminalOldElapsedWeakStrongVelocity u t)
          (q : ℝ) x).component j) := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hC3 :
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) x).component j) :=
    hPDE.regularity.velocity_spatial_three
      (t + (q : ℝ)) hAbs j

  have hC1 :
      SpatialC1
        (fun x : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) x).component j) :=
    hC3.of_le (by norm_num)

  simpa only [
    h3PreterminalOldElapsedWeakStrongVelocity
  ] using hC1

/-- Honest old-transport whole-space integration-by-parts data for the actual
selected-minus-old velocity difference coordinates at one elapsed time. -/
def H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) : Prop :=
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t
  ∀ j : PrimeTensor.Axis Depth.three,
    TransportScalarIntegrationByPartsAt
      (logSpaceTimeVectorField u)
      (t + (q : ℝ))
      (selectedOldVelocityDifferenceComponent
        selected old (q : ℝ) j)

/-- At one elapsed time, the explicit old-transport term is exactly scalar
transport by the absolute-time old preterminal velocity. -/
theorem h3PreterminalSelectedOldWeakStrongOldTransport_eq_scalarTransport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : PrimeTensor.Axis Depth.three) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity
        u t
    (fun x : Point3 =>
      realAdvectionOldTransportDifferenceComponent
        selected old (q : ℝ) x j)
      =
    h3ScalarTransport
      (logSpaceTimeVectorField u)
      (t + (q : ℝ))
      (selectedOldVelocityDifferenceComponent
        selected old (q : ℝ) j) := by
  dsimp only

  funext x

  unfold
    realAdvectionOldTransportDifferenceComponent
    h3ScalarTransport
    selectedOldVelocityDifferenceComponent
    h3PreterminalOldElapsedWeakStrongVelocity

  rfl

/-- Honest old-transport IBP makes the concrete componentwise old-transport
product integrable. -/
theorem h3PreterminalSelectedOldWeakStrongOldTransport_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (hIBP :
      H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q)
    (j : PrimeTensor.Axis Depth.three) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity
        u t
    MeasureTheory.Integrable
      (fun x : Point3 =>
        ((selected (q : ℝ) x).component j
            - (old (q : ℝ) x).component j)
          *
        realAdvectionOldTransportDifferenceComponent
          selected old (q : ℝ) x j)
      (volume : Measure Point3) := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]
    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]
    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  have hf :
      SpatialC1
        (selectedOldVelocityDifferenceComponent
          selected old (q : ℝ) j) :=
    selectedOldVelocityDifferenceComponent_spatialC1
      selected old (q : ℝ) j
      hSelected hOld

  have hPairing :
      MeasureTheory.Integrable
        (fun x : Point3 =>
          selectedOldVelocityDifferenceComponent
              selected old (q : ℝ) j x
            *
          h3ScalarTransport
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            (selectedOldVelocityDifferenceComponent
              selected old (q : ℝ) j)
            x)
        (volume : Measure Point3) :=
    transportScalarPairingIntegrable_of_integrationByParts
      hPDE hAbs hf (hIBP j)

  have hTransport :=
    h3PreterminalSelectedOldWeakStrongOldTransport_eq_scalarTransport
      hNS ht hEnd hE hTail q j

  rw [← hTransport] at hPairing

  simpa only [
    selectedOldVelocityDifferenceComponent
  ] using hPairing

/-- Honest old-transport IBP gives the exact skew cancellation

    ∫ D_j (O · ∇D_j) = 0

for every component. -/
theorem integral_h3PreterminalSelectedOldWeakStrongOldTransport_eq_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (hIBP :
      H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q)
    (j : PrimeTensor.Axis Depth.three) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity
        u t
    (∫ x : Point3,
      ((selected (q : ℝ) x).component j
          - (old (q : ℝ) x).component j)
        *
      realAdvectionOldTransportDifferenceComponent
        selected old (q : ℝ) x j
      ∂volume)
      =
    0 := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]
    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]
    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  have hf :
      SpatialC1
        (selectedOldVelocityDifferenceComponent
          selected old (q : ℝ) j) :=
    selectedOldVelocityDifferenceComponent_spatialC1
      selected old (q : ℝ) j
      hSelected hOld

  have hCancel :
      spatialEnergyPairing
          (selectedOldVelocityDifferenceComponent
            selected old (q : ℝ) j)
          (h3ScalarTransport
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            (selectedOldVelocityDifferenceComponent
              selected old (q : ℝ) j))
        =
      0 :=
    spatialEnergyPairing_scalarTransport_eq_zero
      hPDE hAbs hf (hIBP j).2

  have hTransport :=
    h3PreterminalSelectedOldWeakStrongOldTransport_eq_scalarTransport
      hNS ht hEnd hE hTail q j

  rw [← hTransport] at hCancel

  unfold
    spatialEnergyPairing
    selectedOldVelocityDifferenceComponent
    at hCancel

  linarith

/-- Local quotient bridge under the measure-space instance used by the
weak--strong transport stack. -/
theorem h3ScalarL2_inner_eq_integral_mul_of_ae_weakStrong
    (F G : H3ScalarL2)
    {f g : ScalarField3}
    (hF :
      (F : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      f)
    (hG :
      (G : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      g) :
    inner ℝ F G
      =
    ∫ x : Point3, f x * g x ∂volume := by
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [hF, hG] with x hxF hxG

  rw [hxF, hxG]

  simp [RCLike.inner_apply, mul_comm]

/-- The concrete nonlinear Hilbert pairing is exactly the sum of the three
classical selected-minus-old advection-difference pairings. -/
theorem inner_selectedOldUnitLerayForcingDifference_eq_classicalAdvectionIntegrals
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity
        u t
    let D :=
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
    inner ℝ
        D
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
            -
          (old (q : ℝ) x).component (h3AxisOfFin3 i))
          *
        (realAdvectionComponent
            selected (q : ℝ) x (h3AxisOfFin3 i)
          -
         realAdvectionComponent
            old (q : ℝ) x (h3AxisOfFin3 i))
        ∂volume := by
  dsimp only

  let qR :=
    h3PreterminalElapsedToSelectedUnitRadius htauR q

  let USel :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail qR

  let UOld :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  let D :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  let AS :=
    h3WeakStrongAdvectionPhysicalL2Hilbert USel

  let AO :=
    h3WeakStrongAdvectionPhysicalL2Hilbert UOld

  have hForcing :
      inner ℝ
          D
          (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
            hNS ht hEnd hE hTail htauR q)
        =
      inner ℝ D (AS - AO) := by
    have h :=
      inner_selectedOldUnitLerayForcingDifference_eq_advectionDifference
        hNS ht hEnd hE hTail htauR q

    dsimp only [qR, USel, UOld, D, AS, AO] at h ⊢
    exact h

  rw [hForcing]

  rw [PiLp.inner_apply]

  apply Finset.sum_congr rfl
  intro i hi

  have hDRep :
      ((D i : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (selected (q : ℝ) x).component (h3AxisOfFin3 i)
          -
        (old (q : ℝ) x).component (h3AxisOfFin3 i)) := by
    have h :=
      h3PreterminalSelectedOldVelocityDifference_coordinate_ae
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q i

    change
      (fun x : Point3 =>
        (selected (q : ℝ) x).component (h3AxisOfFin3 i)
          -
        (old (q : ℝ) x).component (h3AxisOfFin3 i))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (D i : H3ScalarL2) x)
      at h

    exact h.symm

  have hARep :
      ((((AS - AO) i : H3ScalarL2) : Point3 → ℝ))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        realAdvectionComponent
            selected (q : ℝ) x (h3AxisOfFin3 i)
          -
        realAdvectionComponent
            old (q : ℝ) x (h3AxisOfFin3 i)) := by
    have hSel :=
      h3WeakStrongAdvectionPhysicalL2_selectedUnit_ae
        hNS ht hE hTail qR i

    have hOld :=
      h3WeakStrongAdvectionPhysicalL2_oldElapsed_ae
        hNS ht hEnd hTail q i

    have hSub :=
      MeasureTheory.Lp.coeFn_sub
        (AS i)
        (AO i)

    have hCoord :
        (AS - AO) i = AS i - AO i := by
      simp only [PiLp.sub_apply]

    filter_upwards [hSub, hSel, hOld] with
        x hxSub hxSel hxOld

    have hqR :
        (qR : ℝ) = (q : ℝ) := by
      dsimp only [qR]
      exact
        h3PreterminalElapsedToSelectedUnitRadius_coe
          htauR q

    rw [hqR] at hxSel

    have hxSel' :
        (AS i : H3ScalarL2) x
          =
        realAdvectionComponent
          selected (q : ℝ) x (h3AxisOfFin3 i) := by
      simpa only [
        AS,
        h3WeakStrongAdvectionPhysicalL2Hilbert,
        PiLp.toLp_apply,
        USel,
        selected
      ] using hxSel

    have hxOld' :
        (AO i : H3ScalarL2) x
          =
        realAdvectionComponent
          old (q : ℝ) x (h3AxisOfFin3 i) := by
      simpa only [
        AO,
        h3WeakStrongAdvectionPhysicalL2Hilbert,
        PiLp.toLp_apply,
        UOld,
        old
      ] using hxOld

    calc
      ((AS - AO) i : H3ScalarL2) x
          =
        ((AS i - AO i : H3ScalarL2) : Point3 → ℝ) x := by
          rw [hCoord]
      _ =
        (AS i : H3ScalarL2) x - (AO i : H3ScalarL2) x := by
          simpa only [Pi.sub_apply] using hxSub
      _ =
        realAdvectionComponent
            selected (q : ℝ) x (h3AxisOfFin3 i)
          -
        realAdvectionComponent
            old (q : ℝ) x (h3AxisOfFin3 i) := by
          rw [hxSel', hxOld']

  exact
    h3ScalarL2_inner_eq_integral_mul_of_ae_weakStrong
      (D i)
      ((AS - AO) i)
      hDRep
      hARep

/-- The surviving selected-gradient interaction product is integrable in every
coordinate because its absolute value is dominated by the already-integrable
absolute interaction density. -/
theorem h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (hInteraction :
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3))
    (i : Fin 3) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity u t
    MeasureTheory.Integrable
      (selectedOldWeakStrongSelectedGradientProduct
        selected old (q : ℝ) · (h3AxisOfFin3 i))
      (volume : Measure Point3) := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]
    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]
    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  have hInteraction' :
      MeasureTheory.Integrable
        (selectedOldWeakStrongAbsInteractionDensity
          selected old (q : ℝ))
        (volume : Measure Point3) := by
    change
      MeasureTheory.Integrable
        (selectedOldWeakStrongAbsInteractionDensity
          selected old (q : ℝ))
        (volume : Measure Point3)
      at hInteraction
    exact hInteraction

  have hContinuous :
      Continuous
        (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) · (h3AxisOfFin3 i)) :=
    selectedOldWeakStrongSelectedGradientProduct_continuous
      selected old (q : ℝ) (h3AxisOfFin3 i)
      hSelected hOld

  exact
    hInteraction'.mono'
      hContinuous.aestronglyMeasurable
      (Filter.Eventually.of_forall
        (fun x => by
          simpa only [Real.norm_eq_abs] using
            abs_selectedOldWeakStrongSelectedGradientProduct_le_absDensity
              selected old (q : ℝ) x i))

/-- The Leray-forcing difference pairing equals the integral of the signed
weak--strong interaction density once the old transport is cancelled. -/
theorem inner_selectedOldUnitLerayForcingDifference_eq_signedInteractionIntegral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (hIBP :
      H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q)
    (hInteraction :
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3)) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity u t
    let D :=
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
    inner ℝ
        D
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      =
    ∫ x : Point3,
      selectedOldWeakStrongSignedInteractionDensity
        selected old (q : ℝ) x
      ∂volume := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  have hClassical :=
    inner_selectedOldUnitLerayForcingDifference_eq_classicalAdvectionIntegrals
      hNS ht hEnd hE hTail htauR q

  change
    inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      =
    _
    at hClassical

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]
    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]
    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  have hCoord
      (i : Fin 3) :
      (∫ x : Point3,
        ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
            -
          (old (q : ℝ) x).component (h3AxisOfFin3 i))
          *
        (realAdvectionComponent
            selected (q : ℝ) x (h3AxisOfFin3 i)
          -
         realAdvectionComponent
            old (q : ℝ) x (h3AxisOfFin3 i))
        ∂volume)
        =
      ∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x (h3AxisOfFin3 i)
        ∂volume := by
    have hSelInt :=
      h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
        hNS ht hEnd hE hTail q hInteraction i

    have hOldInt :=
      h3PreterminalSelectedOldWeakStrongOldTransport_integrable
        hNS ht hEnd hE hTail q hIBP
        (h3AxisOfFin3 i)

    have hOldZero :=
      integral_h3PreterminalSelectedOldWeakStrongOldTransport_eq_zero
        hNS ht hEnd hE hTail q hIBP
        (h3AxisOfFin3 i)

    have hPointwise :
        (fun x : Point3 =>
          ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
              -
            (old (q : ℝ) x).component (h3AxisOfFin3 i))
            *
          (realAdvectionComponent
              selected (q : ℝ) x (h3AxisOfFin3 i)
            -
           realAdvectionComponent
              old (q : ℝ) x (h3AxisOfFin3 i)))
          =
        (fun x : Point3 =>
          selectedOldWeakStrongSelectedGradientProduct
            selected old (q : ℝ) x (h3AxisOfFin3 i)
          +
          ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
              -
            (old (q : ℝ) x).component (h3AxisOfFin3 i))
            *
          realAdvectionOldTransportDifferenceComponent
            selected old (q : ℝ) x (h3AxisOfFin3 i)) := by
      funext x

      rw [
        realAdvectionComponent_sub_eq_selectedGradient_add_oldTransport
          selected old (q : ℝ) x (h3AxisOfFin3 i)
          hSelected hOld
      ]

      unfold selectedOldWeakStrongSelectedGradientProduct
      ring

    rw [hPointwise]
    rw [integral_add hSelInt hOldInt]
    rw [hOldZero, add_zero]

  rw [hClassical]

  change
    (∑ i : Fin 3,
      ∫ x : Point3,
        ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
            -
          (old (q : ℝ) x).component (h3AxisOfFin3 i))
          *
        (realAdvectionComponent
            selected (q : ℝ) x (h3AxisOfFin3 i)
          -
         realAdvectionComponent
            old (q : ℝ) x (h3AxisOfFin3 i))
        ∂volume)
      =
    ∫ x : Point3,
      selectedOldWeakStrongSignedInteractionDensity
        selected old (q : ℝ) x
      ∂volume

  rw [Fin.sum_univ_three]
  rw [hCoord (0 : Fin 3), hCoord (1 : Fin 3), hCoord (2 : Fin 3)]

  have h0 :
      MeasureTheory.Integrable
        (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) · xAxis)
        (volume : Measure Point3) := by
    simpa only [h3AxisOfFin3_zero] using
      h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
        hNS ht hEnd hE hTail q hInteraction (0 : Fin 3)

  have h1 :
      MeasureTheory.Integrable
        (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) · yAxis)
        (volume : Measure Point3) := by
    simpa only [h3AxisOfFin3_one] using
      h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
        hNS ht hEnd hE hTail q hInteraction (1 : Fin 3)

  have h2 :
      MeasureTheory.Integrable
        (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) · zAxis)
        (volume : Measure Point3) := by
    simpa only [h3AxisOfFin3_two] using
      h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
        hNS ht hEnd hE hTail q hInteraction (2 : Fin 3)

  change
    (∫ x : Point3,
      selectedOldWeakStrongSelectedGradientProduct
        selected old (q : ℝ) x xAxis
      ∂volume)
      +
    (∫ x : Point3,
      selectedOldWeakStrongSelectedGradientProduct
        selected old (q : ℝ) x yAxis
      ∂volume)
      +
    (∫ x : Point3,
      selectedOldWeakStrongSelectedGradientProduct
        selected old (q : ℝ) x zAxis
      ∂volume)
      =
    ∫ x : Point3,
      selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x xAxis
        +
      (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x yAxis
        +
       selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x zAxis)
      ∂volume

  symm

  calc
    (∫ x : Point3,
      selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x xAxis
        +
      (selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x yAxis
        +
       selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x zAxis)
      ∂volume)
        =
      (∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x xAxis
        ∂volume)
        +
      (∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
            selected old (q : ℝ) x yAxis
          +
        selectedOldWeakStrongSelectedGradientProduct
            selected old (q : ℝ) x zAxis
        ∂volume) := by
          exact integral_add h0 (h1.add h2)
    _ =
      (∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x xAxis
        ∂volume)
        +
      ((∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x yAxis
        ∂volume)
        +
       (∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x zAxis
        ∂volume)) := by
          rw [integral_add h1 h2]
    _ =
      ((∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x xAxis
        ∂volume)
        +
       (∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x yAxis
        ∂volume))
        +
      (∫ x : Point3,
        selectedOldWeakStrongSelectedGradientProduct
          selected old (q : ℝ) x zAxis
        ∂volume) := by
          ring

/-- The signed weak--strong density is integrable under the same explicit
old-transport IBP assumptions. -/
theorem h3PreterminalSelectedOldWeakStrongSignedInteractionDensity_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (hInteraction :
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3)) :
    MeasureTheory.Integrable
      (selectedOldWeakStrongSignedInteractionDensity
        (h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
        (h3PreterminalOldElapsedWeakStrongVelocity u t)
        (q : ℝ))
      (volume : Measure Point3) := by
  have h0 :=
    h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
      hNS ht hEnd hE hTail q hInteraction (0 : Fin 3)

  have h1 :=
    h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
      hNS ht hEnd hE hTail q hInteraction (1 : Fin 3)

  have h2 :=
    h3PreterminalSelectedOldWeakStrongSelectedGradient_integrable
      hNS ht hEnd hE hTail q hInteraction (2 : Fin 3)

  simp only [
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ] at h0 h1 h2

  unfold selectedOldWeakStrongSignedInteractionDensity

  exact h0.add (h1.add h2)

/-- Absolute value of the nonlinear Leray-forcing difference pairing is
controlled by the integrated absolute weak--strong interaction density. -/
theorem abs_inner_selectedOldUnitLerayForcingDifference_le_absInteraction
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (hIBP :
      H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q)
    (hInteraction :
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3)) :
    abs
        (inner ℝ
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q)
          (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
            hNS ht hEnd hE hTail htauR q))
      ≤
    ∫ x : Point3,
      h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) x
      ∂volume := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  have hPair :=
    inner_selectedOldUnitLerayForcingDifference_eq_signedInteractionIntegral
      hNS ht hEnd hE hTail htauR q hIBP hInteraction

  have hSigned :
      MeasureTheory.Integrable
        (selectedOldWeakStrongSignedInteractionDensity
          selected old (q : ℝ))
        (volume : Measure Point3) := by
    dsimp only [selected, old]
    exact
      h3PreterminalSelectedOldWeakStrongSignedInteractionDensity_integrable
        hNS ht hEnd hE hTail q hInteraction

  have hAbsPoint :
      ∀ x : Point3,
        abs
            (selectedOldWeakStrongSignedInteractionDensity
              selected old (q : ℝ) x)
          ≤
        h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ) x := by
    intro x

    change
      abs
          (selectedOldWeakStrongSignedInteractionDensity
            selected old (q : ℝ) x)
        ≤
      selectedOldWeakStrongAbsInteractionDensity
        selected old (q : ℝ) x

    exact
      abs_selectedOldWeakStrongSignedInteractionDensity_le
        selected old (q : ℝ) x

  rw [hPair]

  calc
    abs
        (∫ x : Point3,
          selectedOldWeakStrongSignedInteractionDensity
            selected old (q : ℝ) x
          ∂volume)
        ≤
      ∫ x : Point3,
        abs
          (selectedOldWeakStrongSignedInteractionDensity
            selected old (q : ℝ) x)
        ∂volume :=
      abs_integral_le_integral_abs
    _ ≤
      ∫ x : Point3,
        h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ) x
        ∂volume := by
      exact
        MeasureTheory.integral_mono
          hSigned.abs
          hInteraction
          hAbsPoint

/-- Final nonlinear relative-energy estimate at one elapsed time:

    -2 ⟪D, NΔ⟫ ≤ 6 B ‖D‖².

The factor `6` is exactly `2 × 3`: the energy derivative contributes the
factor `2`, while the three-coordinate weak--strong estimate contributes `3`.
-/
theorem neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hGradient :
      ∀
        (x : Point3)
        (j i : PrimeTensor.Axis Depth.three),
        abs
          (spatial3.d
            i
            (fun y =>
              ((h3PreterminalSelectedWeakStrongVelocity
                (one_pos : (0 : ℝ) < 1)
                hNS ht hE hTail)
                (q : ℝ) y).component j)
            x)
          ≤ B)
    (hInteraction :
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3))
    (hIBP :
      H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q) :
    -2 *
      inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤
    6 * B *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q‖ ^ 2 := by
  let D :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  let N :=
    h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
      hNS ht hEnd hE hTail htauR q

  have hAbs :
      abs (inner ℝ D N)
        ≤
      ∫ x : Point3,
        h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ) x
        ∂volume := by
    dsimp only [D, N]
    exact
      abs_inner_selectedOldUnitLerayForcingDifference_le_absInteraction
        hNS ht hEnd hE hTail htauR q
        hIBP hInteraction

  have hIntegral :
      (∫ x : Point3,
        h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ) x
        ∂volume)
        ≤
      3 * B * ‖D‖ ^ 2 := by
    dsimp only [D]
    exact
      integral_h3PreterminalSelectedOldWeakStrongAbsInteractionDensity_le_norm_sq
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
        B hB hGradient hInteraction

  have hNeg :
      -(inner ℝ D N)
        ≤
      abs (inner ℝ D N) :=
    neg_le_abs (inner ℝ D N)

  calc
    -2 * inner ℝ D N
        =
      2 * (-(inner ℝ D N)) := by
        ring
    _ ≤
      2 * abs (inner ℝ D N) := by
        exact
          mul_le_mul_of_nonneg_left
            hNeg
            (by norm_num)
    _ ≤
      2 *
        (∫ x : Point3,
          h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ) x
          ∂volume) := by
        exact
          mul_le_mul_of_nonneg_left
            hAbs
            (by norm_num)
    _ ≤
      2 * (3 * B * ‖D‖ ^ 2) := by
        exact
          mul_le_mul_of_nonneg_left
            hIntegral
            (by norm_num)
    _ =
      6 * B * ‖D‖ ^ 2 := by
        ring

end

end Euclidean
end Bridge
end PrimeTensor
