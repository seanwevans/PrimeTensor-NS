import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Temporal.L2.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Fourth.Coordinate.Physical.L2.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Forcing.Second.Coordinate.Open.L2.Continuity

/-!
# Close selected order-two temporal coefficient continuity

The order-two temporal coefficient is

    ∂ₐ∂ᵦ ∂ₜ Sⱼ
      =
    ∑ₖ ∂ₐ∂ᵦ∂ₖ∂ₖ Sⱼ
      -
    ∂ₐ∂ᵦ Nⱼ(S,S)

at unit viscosity.

Both coefficient paths are now strongly continuous in physical `L²`:

* `H3PathOrderTwoSelectedVelocityFourthCoordinatePhysicalL2Identification`
  gives strong continuity of every literal ordered fourth selected velocity jet;
* `H3PathOrderTwoSelectedForcingSecondCoordinateOpenL2Continuity`
  gives strong continuity of every literal selected forcing Hessian.

This file assembles those paths into the selected order-two PDE right-hand side,
identifies that `H3ScalarL2` state with the already-packaged mixed temporal
coefficient, and closes

`H3CanonicalSelectedOrder2RelativeTemporalScalarL2ContinuousOnRestartRadius`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedTemporalL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderTwoSelectedTemporalL2Continuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Assemble the order-two PDE right-hand side -/

/-- Canonical physical `L²` package of the selected twice-differentiated PDE
right-hand side. -/
noncomputable def h3PreterminalSelectedOrderTwoRHSScalarL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail
  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail
  (∑ k : Fin 3,
    h3PreterminalSelectedRealVelocityFourthCoordinateL2
      hNS ht₀ hE hTail q
      j a b
      (h3AxisOfFin3 k)
      (h3AxisOfFin3 k))
  -
  h3SelectedRestartRealLerayForcingSecondCoordinateL2
    (one_pos : (0 : ℝ) < 1)
    U₀ hA hU₀ q
    (h3ClassicalizationFinOfAxis j)
    a b

/-- The assembled order-two PDE right-hand side is strongly continuous on the
full strict restart interval. -/
theorem continuous_h3PreterminalSelectedOrderTwoRHSScalarL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j a b : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedOrderTwoRHSScalarL2
          hNS ht₀ hE hTail q j a b) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  have hDiffusion :
      Continuous
        (fun q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          ∑ k : Fin 3,
            h3PreterminalSelectedRealVelocityFourthCoordinateL2
              hNS ht₀ hE hTail q
              j a b
              (h3AxisOfFin3 k)
              (h3AxisOfFin3 k)) := by
    apply continuous_finsetSum
    intro k hk
    exact
      continuous_h3PreterminalSelectedRealVelocityRepeatedFourthCoordinateL2OnRestartRadius
        hNS ht₀ hE hTail
        j a b
        (h3AxisOfFin3 k)

  have hForcing :
      Continuous
        (fun q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3SelectedRestartRealLerayForcingSecondCoordinateL2
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀ q
            (h3ClassicalizationFinOfAxis j)
            a b) :=
    continuous_h3SelectedRestartRealLerayForcingSecondCoordinateL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (h3ClassicalizationFinOfAxis j)
      a b

  have hRHS := hDiffusion.sub hForcing

  change
    Continuous
      ((fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        ∑ k : Fin 3,
          h3PreterminalSelectedRealVelocityFourthCoordinateL2
            hNS ht₀ hE hTail q
            j a b
            (h3AxisOfFin3 k)
            (h3AxisOfFin3 k))
      -
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3SelectedRestartRealLerayForcingSecondCoordinateL2
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ q
          (h3ClassicalizationFinOfAxis j)
          a b))

  exact hRHS

/-- A.e. representative of the assembled selected order-two PDE right-hand
side. -/
theorem h3PreterminalSelectedOrderTwoRHSScalarL2_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b : PrimeTensor.Axis Depth.three) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
    let selected :
        SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
    (((h3PreterminalSelectedOrderTwoRHSScalarL2
          hNS ht₀ hE hTail q j a b :
          H3ScalarL2) :
          Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (∑ k : Fin 3,
        spatial3.d a
          (spatial3.d b
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (selected (q : ℝ) y).component j))))
          x)
      -
      spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ))
              (W (q : ℝ))
              (h3ClassicalizationFinOfAxis j)
              y).re))
        x)) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let selected :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let D : H3ScalarL2 :=
    ∑ k : Fin 3,
      h3PreterminalSelectedRealVelocityFourthCoordinateL2
        hNS ht₀ hE hTail q
        j a b
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 k)

  let F : H3ScalarL2 :=
    h3SelectedRestartRealLerayForcingSecondCoordinateL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ q
      (h3ClassicalizationFinOfAxis j)
      a b

  have hSub :=
    MeasureTheory.Lp.coeFn_sub D F

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k : Fin 3 =>
        h3PreterminalSelectedRealVelocityFourthCoordinateL2
          hNS ht₀ hE hTail q
          j a b
          (h3AxisOfFin3 k)
          (h3AxisOfFin3 k))

  have hTerms :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ k : Fin 3,
          (((h3PreterminalSelectedRealVelocityFourthCoordinateL2
              hNS ht₀ hE hTail q
              j a b
              (h3AxisOfFin3 k)
              (h3AxisOfFin3 k) :
              H3ScalarL2) :
              Point3 → ℝ) x)
            =
          spatial3.d a
            (spatial3.d b
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (selected (q : ℝ) y).component j))))
            x := by

    exact ae_all_iff.2 (fun k => by
      dsimp only [selected, U₀, hA, hU₀]
      unfold h3PreterminalSelectedRealVelocityFourthCoordinateL2
      exact
        MeasureTheory.MemLp.coeFn_toLp
          (h3CanonicalSelectedArbitraryFourthVelocityJetMemLp2OnRestartRadius_closed
            E u T t₀ hNS ht₀ hE hTail
            (q : ℝ) q.property
            a b
            (h3AxisOfFin3 k)
            (h3AxisOfFin3 k)
            j))

  have hForce :=
    h3SelectedRestartRealLerayForcingSecondCoordinateL2_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ q
      (h3ClassicalizationFinOfAxis j)
      a b

  filter_upwards [
    hSub, hSum, hTerms, hForce
  ] with x hSubx hSumx hTermsx hForcex

  change (((D - F : H3ScalarL2) : Point3 → ℝ) x) = _

  rw [hSubx]
  simp only [Pi.sub_apply]
  rw [hSumx]
  simp only [Finset.sum_apply]
  rw [hForcex]

  apply congrArg
    (fun z : ℝ =>
      z -
      spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ))
              (W (q : ℝ))
              (h3ClassicalizationFinOfAxis j)
              y).re))
        x)

  apply Finset.sum_congr rfl
  intro k hk
  exact hTermsx k

/-! ## Identify the temporal coefficient with the assembled RHS -/

/-- The already-packaged selected mixed temporal coefficient is exactly the
assembled physical `L²` right-hand side. -/
theorem h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At_eq_orderTwoRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b : PrimeTensor.Axis Depth.three) :
    h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At
        hNS ht₀ hE hTail q.property
        j a b
      =
    h3PreterminalSelectedOrderTwoRHSScalarL2
      hNS ht₀ hE hTail q
      j a b := by

  apply MeasureTheory.Lp.ext

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let selected :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  have hField :
      spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (selected r y).component j)
                (q : ℝ)))
        =
      (fun x : Point3 =>
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d b
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (selected (q : ℝ) y).component j))))
            x)
        -
        spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W (q : ℝ))
                (W (q : ℝ))
                (h3ClassicalizationFinOfAxis j)
                y).re))
          x) := by

    funext x

    dsimp only [selected, W, U₀]

    simpa only [one_mul] using
      spatial_d2_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_secondMixedDerivativeCandidate
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        hA hU₀
        q.property.1
        q.property.2
        x a b j

  have hTemporal :=
    h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At_ae
      hNS ht₀ hE hTail q.property
      j a b

  have hRHS :=
    h3PreterminalSelectedOrderTwoRHSScalarL2_ae
      hNS ht₀ hE hTail q
      j a b

  filter_upwards [
    hTemporal, hRHS
  ] with x hTemporalx hRHSx

  rw [hTemporalx, hRHSx]

  exact congrFun hField x

/-! ## Closure of the order-two temporal continuity frontier -/

/-- Strong physical `L²` continuity of every selected order-two temporal
coefficient is closed on the entire strict restart interval. -/
theorem h3CanonicalSelectedOrder2RelativeTemporalScalarL2ContinuousOnRestartRadius_closed :
    H3CanonicalSelectedOrder2RelativeTemporalScalarL2ContinuousOnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail j a b

  have hRHS :
      Continuous
        (fun q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedOrderTwoRHSScalarL2
            hNS ht₀ hE hTail q
            j a b) :=
    continuous_h3PreterminalSelectedOrderTwoRHSScalarL2
      hNS ht₀ hE hTail
      j a b

  have hEq :
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At
          hNS ht₀ hE hTail q.property
          j a b)
        =
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedOrderTwoRHSScalarL2
          hNS ht₀ hE hTail q
          j a b) := by
    funext q
    exact
      h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At_eq_orderTwoRHS
        hNS ht₀ hE hTail q
        j a b

  rw [hEq]
  exact hRHS

end

end Euclidean
end Bridge
end PrimeTensor
