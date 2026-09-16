import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAlternateSelectedTransportIBP

/-!
# Automatic integrability for the selected pure-transport seam

The alternate weak--strong route now has a single honest selected-transport
IBP datum

    Integrable (div (S D_j²))
      ∧
    ∫ div (S D_j²) = 0.

This file discharges the *integrability* half automatically.

The key observation is that the full classical advection-difference pairing
density

    D_j ((S · ∇)S_j - (O · ∇)O_j)

is already an `L¹` function for free: both factors are represented by genuine
physical `L²` objects in the existing forcing-pairing bridge.  The alternate
split says

    full pairing density
      =
    selected pure-transport density
      +
    old-gradient interaction density.

The old-gradient interaction was proved integrable in the preceding alternate
transport stack, hence subtraction gives automatic integrability of the
selected pure-transport density.

Selected incompressibility and the pointwise flux identity then imply
automatic integrability of

    div (S D_j²).

Consequently the honest selected-transport IBP package is equivalent, for this
concrete weak--strong pair, to the single boundary-at-infinity statement

    ∫ div (S D_j²) = 0.

The final theorem therefore recovers the nonlinear `6 B ‖D‖²` estimate from
the selected flux-vanishing predicate alone.
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

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAlternateSelectedTransportAutomaticIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One coordinate of the full selected-minus-old classical advection pairing
density is integrable because both factors have genuine physical `L²`
representatives. -/
theorem h3PreterminalSelectedOldWeakStrongAdvectionDifferenceProduct_integrable
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
    (i : Fin 3) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity u t
    Integrable
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
      (volume : Measure Point3) := by
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
    h3PreterminalOldElapsedWeakStrongVelocity u t

  let D :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  let AS :=
    h3WeakStrongAdvectionPhysicalL2Hilbert USel

  let AO :=
    h3WeakStrongAdvectionPhysicalL2Hilbert UOld

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
          exact hxSub
      _ =
        realAdvectionComponent
            selected (q : ℝ) x (h3AxisOfFin3 i)
          -
        realAdvectionComponent
            old (q : ℝ) x (h3AxisOfFin3 i) := by
          rw [hxSel', hxOld']

  have hL2Product :
      Integrable
        (fun x : Point3 =>
          (D i : H3ScalarL2) x *
            ((AS - AO) i : H3ScalarL2) x)
        (volume : Measure Point3) := by
    exact
      (MeasureTheory.Lp.memLp (D i)).integrable_mul
        (MeasureTheory.Lp.memLp ((AS - AO) i))

  exact
    hL2Product.congr
      (hDRep.mul hARep)

/-- The selected pure-transport energy density is automatically integrable:
subtract the already-integrable old-gradient interaction from the integrable
full classical advection-difference pairing density. -/
theorem h3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
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
    H3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
      hNS ht hEnd hE hTail q := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  intro j

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

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

  have hFullFin :=
    h3PreterminalSelectedOldWeakStrongAdvectionDifferenceProduct_integrable
      hNS ht hEnd hE hTail htauR q i

  have hOldGradientFin :=
    h3PreterminalSelectedOldWeakStrongOldGradient_integrable
      hNS ht hEnd hE hTail q i

  have hAxis :
      h3AxisOfFin3 i = j := by
    dsimp only [i]
    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hFull :
      Integrable
        (fun x : Point3 =>
          ((selected (q : ℝ) x).component j
              -
            (old (q : ℝ) x).component j)
            *
          (realAdvectionComponent
              selected (q : ℝ) x j
            -
           realAdvectionComponent
              old (q : ℝ) x j))
        (volume : Measure Point3) := by
    dsimp only [selected, old] at hFullFin
    simpa only [hAxis] using hFullFin

  have hOldGradient :
      Integrable
        (selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) · j)
        (volume : Measure Point3) := by
    dsimp only [selected, old] at hOldGradientFin
    simpa only [hAxis] using hOldGradientFin

  have hDifference :
      Integrable
        (fun x : Point3 =>
          (((selected (q : ℝ) x).component j
                -
              (old (q : ℝ) x).component j)
              *
            (realAdvectionComponent
                selected (q : ℝ) x j
              -
             realAdvectionComponent
                old (q : ℝ) x j))
            -
          selectedOldWeakStrongOldGradientProduct
            selected old (q : ℝ) x j)
        (volume : Measure Point3) :=
    hFull.sub hOldGradient

  have hPointwise :
      (fun x : Point3 =>
        (((selected (q : ℝ) x).component j
            -
          (old (q : ℝ) x).component j)
          *
        (realAdvectionComponent
            selected (q : ℝ) x j
          -
         realAdvectionComponent
            old (q : ℝ) x j))
          -
        selectedOldWeakStrongOldGradientProduct
          selected old (q : ℝ) x j)
        =
      (fun x : Point3 =>
        ((selected (q : ℝ) x).component j
            -
          (old (q : ℝ) x).component j)
          *
        realAdvectionSelectedTransportDifferenceComponent
          selected old (q : ℝ) x j) := by
    funext x

    rw [
      realAdvectionComponent_sub_eq_selectedTransport_add_oldGradient
        selected old (q : ℝ) x j
        hSelected hOld
    ]

    unfold
      selectedOldWeakStrongOldGradientProduct

    ring

  rw [hPointwise] at hDifference

  exact hDifference

/-- The selected scalar-flux divergence is automatically integrable.  Thus the
only nonautomatic part of honest whole-space selected transport IBP is the
zero-integral boundary statement. -/
theorem h3PreterminalSelectedOldWeakStrongSelectedTransportFluxDivergence_integrable
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
    (j : PrimeTensor.Axis Depth.three) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity u t
    Integrable
      (fun x : Point3 =>
        transportScalarFluxDivergenceXYZ
          selected
          (q : ℝ)
          (selectedOldVelocityDifferenceComponent
            selected old (q : ℝ) j)
          x)
      (volume : Measure Point3) := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  let f :=
    selectedOldVelocityDifferenceComponent
      selected old (q : ℝ) j

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
      SpatialC1 f := by
    dsimp only [f]

    exact
      selectedOldVelocityDifferenceComponent_spatialC1
        selected old (q : ℝ) j
        hSelected hOld

  have hDiv :
      ∀ x : Point3,
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3 (selected (q : ℝ)) x
          =
        0 := by
    intro x
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_divergence_eq_zero
        hNS ht hEnd hE hTail htauR q x

  have hPairingAll :=
    h3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
      hNS ht hEnd hE hTail htauR q

  have hPairing :
      Integrable
        (fun x : Point3 =>
          f x *
            h3ScalarTransport
              selected
              (q : ℝ)
              f
              x)
        (volume : Measure Point3) := by
    have hConcrete :=
      hPairingAll j

    have hTransportEq :=
      realAdvectionSelectedTransportDifferenceComponent_eq_scalarTransport
        selected old (q : ℝ) j

    change
      Integrable
        (fun x : Point3 =>
          f x *
            realAdvectionSelectedTransportDifferenceComponent
              selected old (q : ℝ) x j)
        (volume : Measure Point3)
      at hConcrete

    refine
      hConcrete.congr
        (Filter.Eventually.of_forall ?_)

    intro x

    dsimp only [f]

    rw [congrFun hTransportEq x]

  have hPointwise :
      (fun x : Point3 =>
        transportScalarFluxDivergenceXYZ
          selected (q : ℝ) f x)
        =
      (fun x : Point3 =>
        2 *
          (f x *
            h3ScalarTransport
              selected
              (q : ℝ)
              f
              x)) := by
    funext x

    simpa [mul_assoc] using
      transportScalarFluxDivergenceXYZ_eq_two_mul_transport_of_divergenceFree
        selected
        (q : ℝ)
        hSelected
        hDiv
        hf
        x

  rw [hPointwise]

  exact
    hPairing.const_mul 2

/-- For the concrete selected restart, flux vanishing alone upgrades
automatically to the honest selected-transport IBP package. -/
theorem h3PreterminalSelectedOldWeakStrongSelectedTransportIntegrationByPartsAt_of_fluxVanishes
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
        hNS ht hEnd hE hTail q) :
    H3PreterminalSelectedOldWeakStrongSelectedTransportIntegrationByPartsAt
      hNS ht hEnd hE hTail q := by
  intro j

  constructor

  · exact
      h3PreterminalSelectedOldWeakStrongSelectedTransportFluxDivergence_integrable
        hNS ht hEnd hE hTail htauR q j

  · exact hFlux j

/-- The alternate nonlinear forcing estimate now needs only the genuine
boundary-at-infinity statement for selected transport.  Every integrability
field is automatic. -/
theorem neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate_of_fluxVanishes
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
  have hIBP :=
    h3PreterminalSelectedOldWeakStrongSelectedTransportIntegrationByPartsAt_of_fluxVanishes
      hNS ht hEnd hE hTail htauR q hFlux

  exact
    neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate_of_selectedTransportIBP
      hNS ht hEnd hE hTail htauR q hIBP

end

end Euclidean
end Bridge
end PrimeTensor
