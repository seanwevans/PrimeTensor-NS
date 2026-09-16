import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAlternateSignedInteraction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongTransportPairingBound

/-!
# Alternate weak--strong Leray-forcing pairing bound

The alternate convection decomposition is now complete at the spatial level:

    (S · ∇)S - (O · ∇)O
      =
    S · ∇D + D · ∇O,

where `D = S - O`.

The selected pure-transport piece has zero energy pairing under the selected
scalar-flux condition, while the old-gradient interaction satisfies

    |∫ Σ_j D_j ((D · ∇)O_j)|
      ≤
    3 B ‖D‖²,

with the endpoint-independent envelope

    B = C₁ (2E).

This file reconnects that alternate physical calculation to the already-proved
Leray-forcing Hilbert pairing.

The only extra analytic datum kept explicit here is integrability of each
selected pure-transport energy density.  This is strictly weaker/more local
than the previous old-branch whole-space IBP package and is isolated so it can
be discharged from the selected restart regularity/decay in the next
checkpoint.
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

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAlternateForcingPairingBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every one of the three old-gradient interaction coordinates is pointwise
dominated by the full alternate absolute interaction density. -/
theorem abs_selectedOldWeakStrongOldGradientProduct_le_absDensity
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3)
    (i : Fin 3) :
    abs
        (selectedOldWeakStrongOldGradientProduct
          selected old s x (h3AxisOfFin3 i))
      ≤
    selectedOldWeakStrongOldGradientAbsInteractionDensity
      selected old s x := by
  let px : ℝ :=
    selectedOldWeakStrongOldGradientProduct
      selected old s x xAxis

  let py : ℝ :=
    selectedOldWeakStrongOldGradientProduct
      selected old s x yAxis

  let pz : ℝ :=
    selectedOldWeakStrongOldGradientProduct
      selected old s x zAxis

  have hx : 0 ≤ abs px := abs_nonneg px
  have hy : 0 ≤ abs py := abs_nonneg py
  have hz : 0 ≤ abs pz := abs_nonneg pz

  have hDensity :
      selectedOldWeakStrongOldGradientAbsInteractionDensity
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

/-- Each concrete old-gradient interaction coordinate is integrable. -/
theorem h3PreterminalSelectedOldWeakStrongOldGradient_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity u t
    Integrable
      (selectedOldWeakStrongOldGradientProduct
        selected old (q : ℝ) · (h3AxisOfFin3 i))
      (volume : Measure Point3) := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  have hAbs :
      Integrable
        (selectedOldWeakStrongOldGradientAbsInteractionDensity
          selected old (q : ℝ))
        (volume : Measure Point3) := by
    dsimp only [selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradientAbsInteractionDensity_integrable
        hNS ht hEnd hE hTail q

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

  have hContinuous :
      Continuous
        (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) · (h3AxisOfFin3 i)) :=
    selectedOldWeakStrongOldGradientProduct_continuous
      selected old (q : ℝ) (h3AxisOfFin3 i)
      hSelected hOld

  exact
    hAbs.mono'
      hContinuous.aestronglyMeasurable
      (Filter.Eventually.of_forall
        (fun x => by
          simpa only [Real.norm_eq_abs] using
            abs_selectedOldWeakStrongOldGradientProduct_le_absDensity
              selected old (q : ℝ) x i))

/-- Integrability datum needed only to split the selected pure-transport
summand from the old-gradient summand under the Bochner integral.

The cancellation itself needs only
`H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt`. -/
def H3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
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
    h3PreterminalOldElapsedWeakStrongVelocity u t

  ∀ j : PrimeTensor.Axis Depth.three,
    Integrable
      (fun x : Point3 =>
        ((selected (q : ℝ) x).component j
            -
          (old (q : ℝ) x).component j)
          *
        realAdvectionSelectedTransportDifferenceComponent
          selected old (q : ℝ) x j)
      (volume : Measure Point3)

/-- Under selected transport cancellation, each classical advection-difference
coordinate pairing reduces to the old-gradient weak--strong interaction. -/
theorem integral_selectedOldAdvectionDifference_eq_oldGradient
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
    (hFlux :
      H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
        hNS ht hEnd hE hTail q)
    (hTransportIntegrable :
      H3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
        hNS ht hEnd hE hTail q)
    (i : Fin 3) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity u t
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
      selectedOldWeakStrongOldGradientProduct
        selected old (q : ℝ) x (h3AxisOfFin3 i)
      ∂volume := by
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

  have hTransportInt :
      Integrable
        (fun x : Point3 =>
          ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
              -
            (old (q : ℝ) x).component (h3AxisOfFin3 i))
            *
          realAdvectionSelectedTransportDifferenceComponent
            selected old (q : ℝ) x (h3AxisOfFin3 i))
        (volume : Measure Point3) :=
    hTransportIntegrable (h3AxisOfFin3 i)

  have hOldGradientInt :
      Integrable
        (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) · (h3AxisOfFin3 i))
        (volume : Measure Point3) := by
    dsimp only [selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongOldGradient_integrable
        hNS ht hEnd hE hTail q i

  have hTransportZero :
      (∫ x : Point3,
        ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
            -
          (old (q : ℝ) x).component (h3AxisOfFin3 i))
          *
        realAdvectionSelectedTransportDifferenceComponent
          selected old (q : ℝ) x (h3AxisOfFin3 i)
        ∂volume)
        =
      0 := by
    have h :=
      spatialEnergyPairing_selectedTransportDifference_eq_zero
        hNS ht hEnd hE hTail htauR q hFlux
        (h3AxisOfFin3 i)

    dsimp only at h

    unfold
      spatialEnergyPairing
      selectedOldVelocityDifferenceComponent
      at h

    linarith

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
        ((selected (q : ℝ) x).component (h3AxisOfFin3 i)
            -
          (old (q : ℝ) x).component (h3AxisOfFin3 i))
          *
        realAdvectionSelectedTransportDifferenceComponent
          selected old (q : ℝ) x (h3AxisOfFin3 i)
        +
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x (h3AxisOfFin3 i)) := by
    funext x

    rw [
      realAdvectionComponent_sub_eq_selectedTransport_add_oldGradient
        selected old (q : ℝ) x (h3AxisOfFin3 i)
        hSelected hOld
    ]

    unfold selectedOldWeakStrongOldGradientProduct
    ring

  rw [hPointwise]
  rw [integral_add hTransportInt hOldGradientInt]
  rw [hTransportZero, zero_add]

/-- The concrete Leray-forcing difference pairing is exactly the alternate
signed old-gradient interaction integral. -/
theorem inner_selectedOldUnitLerayForcingDifference_eq_oldGradientSignedInteractionIntegral
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
    (hFlux :
      H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
        hNS ht hEnd hE hTail q)
    (hTransportIntegrable :
      H3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
        hNS ht hEnd hE hTail q) :
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
      selectedOldWeakStrongOldGradientSignedInteractionDensity
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
      selectedOldWeakStrongOldGradientSignedInteractionDensity
        selected old (q : ℝ) x
      ∂volume

  rw [Fin.sum_univ_three]

  rw [
    integral_selectedOldAdvectionDifference_eq_oldGradient
      hNS ht hEnd hE hTail htauR q
      hFlux hTransportIntegrable (0 : Fin 3),
    integral_selectedOldAdvectionDifference_eq_oldGradient
      hNS ht hEnd hE hTail htauR q
      hFlux hTransportIntegrable (1 : Fin 3),
    integral_selectedOldAdvectionDifference_eq_oldGradient
      hNS ht hEnd hE hTail htauR q
      hFlux hTransportIntegrable (2 : Fin 3)
  ]

  have h0 :
      Integrable
        (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) · xAxis)
        (volume : Measure Point3) := by
    simpa only [h3AxisOfFin3_zero] using
      h3PreterminalSelectedOldWeakStrongOldGradient_integrable
        hNS ht hEnd hE hTail q (0 : Fin 3)

  have h1 :
      Integrable
        (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) · yAxis)
        (volume : Measure Point3) := by
    simpa only [h3AxisOfFin3_one] using
      h3PreterminalSelectedOldWeakStrongOldGradient_integrable
        hNS ht hEnd hE hTail q (1 : Fin 3)

  have h2 :
      Integrable
        (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) · zAxis)
        (volume : Measure Point3) := by
    simpa only [h3AxisOfFin3_two] using
      h3PreterminalSelectedOldWeakStrongOldGradient_integrable
        hNS ht hEnd hE hTail q (2 : Fin 3)

  change
    (∫ x : Point3,
      selectedOldWeakStrongOldGradientProduct
        selected old (q : ℝ) x xAxis
      ∂volume)
      +
    (∫ x : Point3,
      selectedOldWeakStrongOldGradientProduct
        selected old (q : ℝ) x yAxis
      ∂volume)
      +
    (∫ x : Point3,
      selectedOldWeakStrongOldGradientProduct
        selected old (q : ℝ) x zAxis
      ∂volume)
      =
    ∫ x : Point3,
      selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x xAxis
        +
      (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x yAxis
        +
       selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x zAxis)
      ∂volume

  symm

  calc
    (∫ x : Point3,
      selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x xAxis
        +
      (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x yAxis
        +
       selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x zAxis)
      ∂volume)
        =
      (∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x xAxis
        ∂volume)
        +
      (∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
            selected old (q : ℝ) x yAxis
          +
        selectedOldWeakStrongOldGradientProduct
            selected old (q : ℝ) x zAxis
        ∂volume) := by
          exact integral_add h0 (h1.add h2)
    _ =
      (∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x xAxis
        ∂volume)
        +
      ((∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x yAxis
        ∂volume)
        +
       (∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x zAxis
        ∂volume)) := by
          rw [integral_add h1 h2]
    _ =
      ((∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x xAxis
        ∂volume)
        +
       (∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x yAxis
        ∂volume))
        +
      (∫ x : Point3,
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x zAxis
        ∂volume) := by
          ring

/-- Alternate weak--strong nonlinear energy estimate with no old-transport IBP:

    -2 ⟪D, NΔ⟫ ≤ 6 B ‖D‖².

Only selected pure-transport flux cancellation and pairing integrability remain
explicit. -/
theorem neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate
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
    (hFlux :
      H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
        hNS ht hEnd hE hTail q)
    (hTransportIntegrable :
      H3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
        hNS ht hEnd hE hTail q) :
    -2 *
      inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
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

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  let I : ℝ :=
    ∫ x : Point3,
      selectedOldWeakStrongOldGradientSignedInteractionDensity
        selected old (q : ℝ) x
      ∂volume

  have hPair :
      inner ℝ D N = I := by
    dsimp only [D, N, I, selected, old]

    exact
      inner_selectedOldUnitLerayForcingDifference_eq_oldGradientSignedInteractionIntegral
        hNS ht hEnd hE hTail htauR q
        hFlux hTransportIntegrable

  have hAbs :
      abs I
        ≤
      3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        ‖D‖ ^ 2 := by
    dsimp only [I, selected, old, D]

    exact
      abs_integral_h3PreterminalSelectedOldWeakStrongOldGradientSignedInteractionDensity_le_norm_sq
        hNS ht hEnd hE hTail q

  calc
    -2 * inner ℝ D N
        =
      2 * (-I) := by
        rw [hPair]
        ring
    _ ≤
      2 * abs I := by
        exact
          mul_le_mul_of_nonneg_left
            (neg_le_abs I)
            (by norm_num)
    _ ≤
      2 *
        (3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          ‖D‖ ^ 2) := by
        exact
          mul_le_mul_of_nonneg_left
            hAbs
            (by norm_num)
    _ =
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        ‖D‖ ^ 2 := by
          ring

end

end Euclidean
end Bridge
end PrimeTensor
