import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongDifferenceDerivativeL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAlternateSelectedTransportAutomaticIntegrability

/-!
# Automatic selected scalar-flux cancellation

The alternate weak--strong route had one final spatial hypothesis:

    ∫ div (S D_j²) = 0.

All ingredients needed to prove it are now internal to the repository.

For every selected velocity coordinate `S_i`:

* `S_i` is spatially `C¹`;
* `S_i` is uniformly bounded;
* `∂ᵢ S_i` is uniformly bounded.

For every difference coordinate `D_j`:

* `D_j` is spatially `C¹`;
* `D_j ∈ L²`;
* `∂ᵢ D_j ∈ L²`.

The generic flux-coordinate theorem therefore gives, for each spatial axis `i`,

    ∂ᵢ (S_i D_j²) ∈ L¹,
    ∫ ∂ᵢ (S_i D_j²) = 0.

Summing the three coordinate identities proves the exact
`TransportScalarFluxVanishesAt` predicate.  Feeding that into the alternate
forcing-pairing theorem removes the last selected-transport hypothesis:

    -2 ⟪D, NΔ⟫ ≤ 6 B ‖D‖²

is now automatic from the endpoint H³ tail data and restart-radius condition.
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

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedFluxAutomatic
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected pure-transport scalar flux vanishes automatically for every
selected-minus-old difference coordinate. -/
theorem h3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt_auto
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
      hNS ht hEnd hE hTail q := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  intro j

  let f : ScalarField3 :=
    selectedOldVelocityDifferenceComponent
      selected old (q : ℝ) j

  let M : ℝ :=
    h3PreterminalSelectedWeakStrongVelocityEnvelope E

  let B : ℝ :=
    h3PreterminalSelectedWeakStrongGradientEnvelope E

  have hSelectedC1 :
      ∀ i : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component i) := by
    intro i
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) i

  have hOldC1 :
      ∀ i : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component i) := by
    intro i
    dsimp only [old]

    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q i

  have hfC1 :
      SpatialC1 f := by
    dsimp only [f]

    exact
      selectedOldVelocityDifferenceComponent_spatialC1
        selected old (q : ℝ) j
        hSelectedC1 hOldC1

  have hf2 :
      MemLp f 2
        (volume : Measure Point3) := by
    dsimp only [f, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongVelocityDifferenceComponent_memLp_two
        hNS ht hEnd hE hTail q j

  have hdf2 :
      ∀ i : PrimeTensor.Axis Depth.three,
        MemLp
          (spatial3.d i f)
          2
          (volume : Measure Point3) := by
    intro i
    dsimp only [f, selected, old]

    exact
      h3PreterminalSelectedOldWeakStrongVelocityDifference_spatial_d_memLp_two
        hNS ht hEnd hE hTail q j i

  have hVelocityBound :
      ∀
        (i : PrimeTensor.Axis Depth.three)
        (x : Point3),
        ‖(selected (q : ℝ) x).component i‖ ≤ M := by
    intro i x
    dsimp only [selected, M]

    exact
      norm_h3PreterminalSelectedWeakStrongVelocity_component_le_envelope
        hNS ht hE hTail (q : ℝ) x i

  have hDerivativeBound :
      ∀
        (i : PrimeTensor.Axis Depth.three)
        (x : Point3),
        ‖spatial3.d
            i
            (fun y : Point3 =>
              (selected (q : ℝ) y).component i)
            x‖
          ≤
        B := by
    intro i x
    dsimp only [selected, B]

    have h :=
      h3PreterminalSelectedWeakStrongVelocity_spatial_d_le_gradientEnvelope
        hNS ht hE hTail (q : ℝ) x i i

    simpa only [Real.norm_eq_abs] using h

  let vx : ScalarField3 :=
    fun x : Point3 =>
      (selected (q : ℝ) x).component xAxis

  let vy : ScalarField3 :=
    fun x : Point3 =>
      (selected (q : ℝ) x).component yAxis

  let vz : ScalarField3 :=
    fun x : Point3 =>
      (selected (q : ℝ) x).component zAxis

  have hvxC1 : SpatialC1 vx := by
    dsimp only [vx]
    exact hSelectedC1 xAxis

  have hvyC1 : SpatialC1 vy := by
    dsimp only [vy]
    exact hSelectedC1 yAxis

  have hvzC1 : SpatialC1 vz := by
    dsimp only [vz]
    exact hSelectedC1 zAxis

  have hvxBound :
      ∀ x : Point3, ‖vx x‖ ≤ M := by
    intro x
    dsimp only [vx]
    exact hVelocityBound xAxis x

  have hvyBound :
      ∀ x : Point3, ‖vy x‖ ≤ M := by
    intro x
    dsimp only [vy]
    exact hVelocityBound yAxis x

  have hvzBound :
      ∀ x : Point3, ‖vz x‖ ≤ M := by
    intro x
    dsimp only [vz]
    exact hVelocityBound zAxis x

  have hdvxBound :
      ∀ x : Point3,
        ‖spatial3.d xAxis vx x‖ ≤ B := by
    intro x
    dsimp only [vx]
    exact hDerivativeBound xAxis x

  have hdvyBound :
      ∀ x : Point3,
        ‖spatial3.d yAxis vy x‖ ≤ B := by
    intro x
    dsimp only [vy]
    exact hDerivativeBound yAxis x

  have hdvzBound :
      ∀ x : Point3,
        ‖spatial3.d zAxis vz x‖ ≤ B := by
    intro x
    dsimp only [vz]
    exact hDerivativeBound zAxis x

  have hIntX :
      Integrable
        (spatial3.d
          xAxis
          (fun x : Point3 =>
            vx x * (f x * f x)))
        (volume : Measure Point3) :=
    scalarFluxCoordinate_spatial_d_integrable_of_bounded_memLp_two
      hvxC1
      hfC1
      xAxis
      M B
      hvxBound
      hdvxBound
      hf2
      (hdf2 xAxis)

  have hIntY :
      Integrable
        (spatial3.d
          yAxis
          (fun x : Point3 =>
            vy x * (f x * f x)))
        (volume : Measure Point3) :=
    scalarFluxCoordinate_spatial_d_integrable_of_bounded_memLp_two
      hvyC1
      hfC1
      yAxis
      M B
      hvyBound
      hdvyBound
      hf2
      (hdf2 yAxis)

  have hIntZ :
      Integrable
        (spatial3.d
          zAxis
          (fun x : Point3 =>
            vz x * (f x * f x)))
        (volume : Measure Point3) :=
    scalarFluxCoordinate_spatial_d_integrable_of_bounded_memLp_two
      hvzC1
      hfC1
      zAxis
      M B
      hvzBound
      hdvzBound
      hf2
      (hdf2 zAxis)

  have hZeroX :
      (∫ x : Point3,
        spatial3.d
          xAxis
          (fun y : Point3 =>
            vx y * (f y * f y))
          x
        ∂volume)
        =
      0 :=
    integral_scalarFluxCoordinate_spatial_d_eq_zero_of_bounded_memLp_two
      hvxC1
      hfC1
      xAxis
      M B
      hvxBound
      hdvxBound
      hf2
      (hdf2 xAxis)

  have hZeroY :
      (∫ x : Point3,
        spatial3.d
          yAxis
          (fun y : Point3 =>
            vy y * (f y * f y))
          x
        ∂volume)
        =
      0 :=
    integral_scalarFluxCoordinate_spatial_d_eq_zero_of_bounded_memLp_two
      hvyC1
      hfC1
      yAxis
      M B
      hvyBound
      hdvyBound
      hf2
      (hdf2 yAxis)

  have hZeroZ :
      (∫ x : Point3,
        spatial3.d
          zAxis
          (fun y : Point3 =>
            vz y * (f y * f y))
          x
        ∂volume)
        =
      0 :=
    integral_scalarFluxCoordinate_spatial_d_eq_zero_of_bounded_memLp_two
      hvzC1
      hfC1
      zAxis
      M B
      hvzBound
      hdvzBound
      hf2
      (hdf2 zAxis)

  unfold TransportScalarFluxVanishesAt
  unfold transportScalarFluxDivergenceXYZ

  change
    (∫ x : Point3,
      spatial3.d
          xAxis
          (fun y : Point3 =>
            vx y * (f y * f y))
          x
        +
      (spatial3.d
          yAxis
          (fun y : Point3 =>
            vy y * (f y * f y))
          x
        +
       spatial3.d
          zAxis
          (fun y : Point3 =>
            vz y * (f y * f y))
          x)
      ∂volume)
      =
    0

  have hYZ :
      (∫ x : Point3,
        spatial3.d
            yAxis
            (fun y : Point3 =>
              vy y * (f y * f y))
            x
          +
        spatial3.d
            zAxis
            (fun y : Point3 =>
              vz y * (f y * f y))
            x
        ∂volume)
        =
      (∫ x : Point3,
        spatial3.d
          yAxis
          (fun y : Point3 =>
            vy y * (f y * f y))
          x
        ∂volume)
        +
      (∫ x : Point3,
        spatial3.d
          zAxis
          (fun y : Point3 =>
            vz y * (f y * f y))
          x
        ∂volume) := by
    exact
      MeasureTheory.integral_add
        hIntY hIntZ

  have hXYZ :
      (∫ x : Point3,
        spatial3.d
            xAxis
            (fun y : Point3 =>
              vx y * (f y * f y))
            x
          +
        (spatial3.d
            yAxis
            (fun y : Point3 =>
              vy y * (f y * f y))
            x
          +
         spatial3.d
            zAxis
            (fun y : Point3 =>
              vz y * (f y * f y))
            x)
        ∂volume)
        =
      (∫ x : Point3,
        spatial3.d
          xAxis
          (fun y : Point3 =>
            vx y * (f y * f y))
          x
        ∂volume)
        +
      (∫ x : Point3,
        spatial3.d
            yAxis
            (fun y : Point3 =>
              vy y * (f y * f y))
            x
          +
        spatial3.d
            zAxis
            (fun y : Point3 =>
              vz y * (f y * f y))
            x
        ∂volume) := by
    exact
      MeasureTheory.integral_add
        hIntX
        (hIntY.add hIntZ)

  calc
    (∫ x : Point3,
      spatial3.d
          xAxis
          (fun y : Point3 =>
            vx y * (f y * f y))
          x
        +
      (spatial3.d
          yAxis
          (fun y : Point3 =>
            vy y * (f y * f y))
          x
        +
       spatial3.d
          zAxis
          (fun y : Point3 =>
            vz y * (f y * f y))
          x)
      ∂volume)
        =
      (∫ x : Point3,
        spatial3.d
          xAxis
          (fun y : Point3 =>
            vx y * (f y * f y))
          x
        ∂volume)
        +
      (∫ x : Point3,
        spatial3.d
            yAxis
            (fun y : Point3 =>
              vy y * (f y * f y))
            x
          +
        spatial3.d
            zAxis
            (fun y : Point3 =>
              vz y * (f y * f y))
            x
        ∂volume) := hXYZ
    _ =
      (∫ x : Point3,
        spatial3.d
          xAxis
          (fun y : Point3 =>
            vx y * (f y * f y))
          x
        ∂volume)
        +
      ((∫ x : Point3,
          spatial3.d
            yAxis
            (fun y : Point3 =>
              vy y * (f y * f y))
            x
          ∂volume)
        +
       (∫ x : Point3,
          spatial3.d
            zAxis
            (fun y : Point3 =>
              vz y * (f y * f y))
            x
          ∂volume)) := by
            rw [hYZ]
    _ = 0 := by
      rw [hZeroX, hZeroY, hZeroZ]
      ring

/-- The alternate nonlinear forcing estimate is now completely automatic:
the selected flux condition is derived from the H³ restart data rather than
supplied as an external whole-space hypothesis. -/
theorem neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate_auto
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
  have hFlux :
      H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
        hNS ht hEnd hE hTail q :=
    h3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt_auto
      hNS ht hEnd hE hTail q

  exact
    neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate_of_fluxVanishes
      hNS ht hEnd hE hTail htauR q hFlux

end

end Euclidean
end Bridge
end PrimeTensor
