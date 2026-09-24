import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Transport.L2.Norm.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Difference.Gronwall

/-!
# Selected--old weak--strong transport: concrete square density

The preceding quotient-native bridge proves

    ∫ |D_L²(x)|² dx = ‖D_L²‖²

for every three-component physical `L²` state.  This file identifies the
specific selected-minus-old classical velocity difference with the coordinates
of the concrete `L²` difference state almost everywhere.

For each coordinate `j`,

    S_j(q,x) - O_j(t+q,x)
      = D_j(q,x)    a.e.,

where `S` is the smooth selected restart representative and `O` is the old
logged preterminal velocity.  Squaring and summing the three coordinate
relations gives an a.e. identity between the classical square density and the
native `PiLp 2` square density.

Consequently the classical square-density integral is exactly the squared
physical `L²` norm of the concrete selected-minus-old state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportConcreteSquareDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongTransportConcreteSquareDensity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3SelectedOldWeakStrongTransportConcreteSquareDensity Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One coordinate of the actual selected-minus-old classical velocity
difference agrees almost everywhere with the corresponding coordinate of the
concrete physical `L²` difference state. -/
theorem h3PreterminalSelectedOldVelocityDifference_coordinate_ae
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    (fun x : Point3 =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν
          (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht hE hTail)
          (q : ℝ) x).component
            (h3AxisOfFin3 j)
        -
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j)
        x)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      ((h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail q) j : H3ScalarL2) x) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let VSelected : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      hν hNS ht hE hTail (q : ℝ)

  let VOld : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      hν hNS ht hEnd hE hTail q

  have hSelected :
      (fun x : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            hν U₀ hEpos hU₀ (q : ℝ) x).component
              (h3AxisOfFin3 j))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (VSelected j : H3ScalarL2) x) := by
    have hRep :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
        (s := (q : ℝ))
        hν U₀ hEpos hU₀ j

    simpa only [
      VSelected,
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt,
      PiLp.toLp_apply,
      U₀,
      hEpos,
      hU₀,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
    ] using hRep

  have hOld :
      (fun x : Point3 =>
        (VOld j : H3ScalarL2) x)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j) := by
    simpa only [
      VOld,
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed,
      PiLp.toLp_apply
    ] using
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
        hNS ht hEnd hTail q j

  have hDcoord :
      D j = VSelected j - VOld j := by
    simp only [
      D,
      VSelected,
      VOld,
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed,
      PiLp.sub_apply
    ]

  have hDifference :
      (fun x : Point3 =>
        (D j : H3ScalarL2) x)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (VSelected j : H3ScalarL2) x
          -
        (VOld j : H3ScalarL2) x) := by
    have hSub :=
      MeasureTheory.Lp.coeFn_sub
        (VSelected j)
        (VOld j)

    filter_upwards [hSub] with x hx
    rw [hDcoord]
    exact hx

  filter_upwards [hSelected, hOld, hDifference] with x hS hO hD

  have hTarget :
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (q : ℝ) x).component
            (h3AxisOfFin3 j)
        -
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 j)
        x
        =
      (D j : H3ScalarL2) x := by
    rw [hS, ← hO, hD]

  simpa only [
    U₀,
    hEpos,
    hU₀,
    D
  ] using hTarget

/-- Classical pointwise square density of the actual selected-minus-old
velocity difference. -/
noncomputable def h3PreterminalSelectedOldVelocitySquareDensity
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3) : ℝ :=
  ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht hE hTail)
        (q : ℝ) x).component xAxis
      - loggedVelocityComponent u (t + (q : ℝ)) xAxis x) ^ 2
    +
  (
    ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν
          (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht hE hTail)
          (q : ℝ) x).component yAxis
      - loggedVelocityComponent u (t + (q : ℝ)) yAxis x) ^ 2
      +
    ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν
          (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht hE hTail)
          (q : ℝ) x).component zAxis
      - loggedVelocityComponent u (t + (q : ℝ)) zAxis x) ^ 2
  )

/-- The classical selected-minus-old square density is exactly the native
`PiLp 2` square density almost everywhere. -/
theorem h3PreterminalSelectedOldVelocitySquareDensity_ae_eq_physicalL2
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocitySquareDensity
        hν hNS ht hEnd hE hTail q
      =ᵐ[(volume : Measure Point3)]
    h3PhysicalRealFinVectorL2SquareDensity
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail q) := by
  have h0 :=
    h3PreterminalSelectedOldVelocityDifference_coordinate_ae
      hν hNS ht hEnd hE hTail q (0 : Fin 3)

  have h1 :=
    h3PreterminalSelectedOldVelocityDifference_coordinate_ae
      hν hNS ht hEnd hE hTail q (1 : Fin 3)

  have h2 :=
    h3PreterminalSelectedOldVelocityDifference_coordinate_ae
      hν hNS ht hEnd hE hTail q (2 : Fin 3)

  filter_upwards [h0, h1, h2] with x hx hy hz

  unfold
    h3PreterminalSelectedOldVelocitySquareDensity
    h3PhysicalRealFinVectorL2SquareDensity

  simp only [
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ] at hx hy hz

  rw [hx, hy, hz]

/-- The classical square-density integral is exactly the squared norm of the
concrete selected-minus-old physical `L²` difference state. -/
theorem integral_h3PreterminalSelectedOldVelocitySquareDensity_eq_norm_sq
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ x : Point3,
      h3PreterminalSelectedOldVelocitySquareDensity
        hν hNS ht hEnd hE hTail q x)
      =
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail q‖ ^ 2 := by
  calc
    (∫ x : Point3,
      h3PreterminalSelectedOldVelocitySquareDensity
        hν hNS ht hEnd hE hTail q x)
        =
      ∫ x : Point3,
        h3PhysicalRealFinVectorL2SquareDensity
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            hν hNS ht hEnd hE hTail q)
          x := by
            exact
              integral_congr_ae
                (h3PreterminalSelectedOldVelocitySquareDensity_ae_eq_physicalL2
                  hν hNS ht hEnd hE hTail q)
    _ =
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail q‖ ^ 2 := by
        exact
          integral_h3PhysicalRealFinVectorL2SquareDensity_eq_norm_sq
            (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              hν hNS ht hEnd hE hTail q)

end

end Euclidean
end Bridge
end PrimeTensor
