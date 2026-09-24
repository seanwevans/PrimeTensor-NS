import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.L2.Jet.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Velocity.Jet.Four.Arbitrary.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Physical.L2.Jet
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Second.Temporal.Derivative.PDE.Form

/-!
# Package the selected order-two temporal coefficient in physical L²

For one selected restart and one ordered second spatial jet, the literal mixed
temporal coefficient is

    ∂ₐ∂ᵦ ∂ₜ Sⱼ.

The twice-spatially differentiated selected PDE gives, at unit viscosity,

    ∂ₐ∂ᵦ ∂ₜ Sⱼ
      =
    ∑ₖ ∂ₐ∂ᵦ∂ₖ∂ₖ Sⱼ
      -
    ∂ₐ∂ᵦ Nⱼ(S,S).

Both terms are already in physical `L²`:

* every ordered fourth selected velocity jet is closed;
* every ordered second selected Leray-forcing jet is closed.

Hence the order-two temporal coefficient has a canonical `H3ScalarL2` package.
This file proves that package has the literal mixed temporal field as its a.e.
representative and isolates strong `L²` continuity of the coefficient path as
the next analytic frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedTemporalL2Reduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderTwoSelectedTemporalL2Reduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The selected second-jet mixed temporal field belongs to physical `L²` at
every strict elapsed restart time. -/
theorem h3PreterminalSelectedSecondJetRelativeTemporalField_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq :
      q ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b : PrimeTensor.Axis Depth.three) :
    MemLp
      (spatial3.d a
        (spatial3.d b
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  r y).component j)
              q)))
      2
      (volume : Measure Point3) := by

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

  have hFourth :
      ∀ k : Fin 3,
        MemLp
          (spatial3.d a
            (spatial3.d b
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (selected q y).component j)))))
          2
          (volume : Measure Point3) := by
    intro k

    dsimp only [selected, U₀, hA, hU₀]

    exact
      h3CanonicalSelectedArbitraryFourthVelocityJetMemLp2OnRestartRadius_closed
        E u T t₀ hNS ht₀ hE hTail
        q hq
        a b
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 k)
        j

  have hDiffusion :
      MemLp
        (fun y : Point3 =>
          ∑ k : Fin 3,
            spatial3.d a
              (spatial3.d b
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun z : Point3 =>
                      (selected q z).component j))))
              y)
        2
        (volume : Measure Point3) := by
    exact
      MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _hk => hFourth k)

  have hForcing :
      MemLp
        (spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W q) (W q)
                (h3ClassicalizationFinOfAxis j)
                y).re)))
        2
        (volume : Measure Point3) := by
    dsimp only [W, U₀, hA, hU₀]

    exact
      h3SelectedRestartRealLerayForcing_spatial_d_two_memLp2
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        hq.1
        hq.2
        (h3ClassicalizationFinOfAxis j)
        a b

  have hRHS :
      MemLp
        ((fun y : Point3 =>
          ∑ k : Fin 3,
            spatial3.d a
              (spatial3.d b
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun z : Point3 =>
                      (selected q z).component j))))
              y)
          -
        spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W q) (W q)
                (h3ClassicalizationFinOfAxis j)
                y).re)))
        2
        (volume : Measure Point3) :=
    hDiffusion.sub hForcing

  have hField :
      spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (selected r y).component j)
                q))
        =
      (fun y : Point3 =>
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d b
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun z : Point3 =>
                    (selected q z).component j))))
            y)
        -
        spatial3.d a
          (spatial3.d b
            (fun z : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W q) (W q)
                (h3ClassicalizationFinOfAxis j)
                z).re))
          y) := by
    funext y

    dsimp only [selected, W, U₀]

    simpa only [one_mul] using
      spatial_d2_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_secondMixedDerivativeCandidate
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        hA
        hU₀
        hq.1
        hq.2
        y a b j

  rw [hField]
  exact hRHS

/-- Canonical physical `L²` package of one selected second-jet relative temporal
derivative. -/
noncomputable def h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq :
      q ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  (h3PreterminalSelectedSecondJetRelativeTemporalField_memLp_two
      hNS ht₀ hE hTail hq j a b).toLp
    (spatial3.d a
      (spatial3.d b
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState
                  hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                r y).component j)
            q)))

/-- The packaged selected order-two temporal coefficient has the literal mixed
temporal field as its a.e. representative. -/
theorem h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq :
      q ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a b : PrimeTensor.Axis Depth.three) :
    (((h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At
          hNS ht₀ hE hTail hq j a b : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState
                  hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                r y).component j)
            q))) := by
  unfold h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3PreterminalSelectedSecondJetRelativeTemporalField_memLp_two
        hNS ht₀ hE hTail hq j a b)

/-- The remaining coefficient-topology frontier for the direct order-two
Hilbert-space argument: strong physical `L²` continuity of every selected
second-jet temporal coefficient on the open restart interval. -/
def H3CanonicalSelectedOrder2RelativeTemporalScalarL2ContinuousOnRestartRadius :
    Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j a b : PrimeTensor.Axis Depth.three),
      Continuous
        (fun q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedSecondJetRelativeTemporalScalarL2At
            hNS ht₀ hE hTail q.property j a b)

end

end Euclidean
end Bridge
end PrimeTensor
