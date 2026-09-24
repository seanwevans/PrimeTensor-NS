import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.L2.Jet.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Velocity.Jet.High.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Physical.L2.Jet
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Third.Temporal.Derivative.PDE.Form

/-!
# Reduce the selected order-three strong L² derivative to temporal coefficient continuity

The selected order-three energy has already been reduced to strong physical
`L²` differentiation of each ordered third spatial velocity jet.

At one strict positive restart time the corresponding temporal coefficient is

    ∂ₐ∂ᵦ∂𝑐 ∂ₜ Sⱼ
      =
    ∑ₖ ∂ₐ∂ᵦ∂𝑐∂ₖ∂ₖ Sⱼ
      -
    ∂ₐ∂ᵦ∂𝑐 Nⱼ(S,S)

at unit viscosity.

Both terms already belong to physical `L²`:

* the repeated fifth selected velocity jet comes from the closed selected
  fourth/fifth high-jet chain;
* every ordered third selected Leray-forcing derivative is already in
  physical `L²`.

This file packages that mixed temporal field canonically as `H3ScalarL2` and
isolates the remaining topology problem: strong `L²` continuity of that
coefficient on the open restart interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedTemporalL2Reduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderThreeSelectedTemporalL2Reduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The already-closed selected fourth/fifth high-jet package, exposed for
reuse in the order-three temporal coefficient. -/
theorem h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_closed_for_order3 :
    H3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius := by

  have hTail :
      H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius

  have hDuhamel :
      H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_tail
      hTail

  have hRadial :
      H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_duhamel
      hDuhamel

  have hMultiplier :
      H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius_of_radial
      hRadial

  have hComplex :
      H3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius_of_rawCoordinateMultiplier
      hMultiplier

  have hReal :
      H3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius_of_complex
      hComplex

  exact
    h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_of_frechetRealPart
      hReal

/-- Every selected order-three relative temporal coefficient belongs to
physical `L²` at every strict positive restart time. -/
theorem h3PreterminalSelectedThirdJetRelativeTemporalField_memLp_two
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
    (j a b c : PrimeTensor.Axis Depth.three) :
    MemLp
      (spatial3.d a
        (spatial3.d b
          (spatial3.d c
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
                q))))
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

  have hSelectedJets :=
    h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_closed_for_order3
      E u T t₀ hNS ht₀ hE hTail
      q hq

  have hFifth :
      ∀ k : Fin 3,
        MemLp
          (spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun y : Point3 =>
                      (selected q y).component j))))))
          2
          (volume : Measure Point3) := by
    intro k

    dsimp only [selected, U₀, hA, hU₀]

    exact
      hSelectedJets.2
        a b c
        (h3AxisOfFin3 k)
        j

  have hDiffusion :
      MemLp
        (fun y : Point3 =>
          ∑ k : Fin 3,
            spatial3.d a
              (spatial3.d b
                (spatial3.d c
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (spatial3.d
                      (h3AxisOfFin3 k)
                      (fun z : Point3 =>
                        (selected q z).component j)))))
              y)
        2
        (volume : Measure Point3) := by
    exact
      MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _hk => hFifth k)

  have hForcing :
      MemLp
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (fun y : Point3 =>
                (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                  (W q) (W q)
                  (h3ClassicalizationFinOfAxis j)
                  y).re))))
        2
        (volume : Measure Point3) := by

    dsimp only [W, U₀, hA, hU₀]

    exact
      h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        hq.1
        hq.2
        (h3ClassicalizationFinOfAxis j)
        a b c

  have hRHS :
      MemLp
        ((fun y : Point3 =>
          ∑ k : Fin 3,
            spatial3.d a
              (spatial3.d b
                (spatial3.d c
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (spatial3.d
                      (h3AxisOfFin3 k)
                      (fun z : Point3 =>
                        (selected q z).component j)))))
              y)
          -
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (fun y : Point3 =>
                (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                  (W q) (W q)
                  (h3ClassicalizationFinOfAxis j)
                  y).re))))
        2
        (volume : Measure Point3) :=
    hDiffusion.sub hForcing

  have hField :
      spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    (selected r y).component j)
                  q)))
        =
      (fun y : Point3 =>
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun z : Point3 =>
                      (selected q z).component j)))))
            y)
        -
        spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (fun z : Point3 =>
                (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                  (W q) (W q)
                  (h3ClassicalizationFinOfAxis j)
                  z).re)))
          y) := by

    funext y

    dsimp only [selected, W, U₀]

    simpa only [one_mul] using
      spatial_d3_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_thirdMixedDerivativeCandidate
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        hA
        hU₀
        hq.1
        hq.2
        y a b c j

  rw [hField]
  exact hRHS

/-- Canonical physical `L²` package of one selected third-jet relative temporal
derivative. -/
noncomputable def h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
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
    (j a b c : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  (h3PreterminalSelectedThirdJetRelativeTemporalField_memLp_two
      hNS ht₀ hE hTail hq j a b c).toLp
    (spatial3.d a
      (spatial3.d b
        (spatial3.d c
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
              q))))

/-- The packaged selected order-three temporal coefficient has the literal
third-spatial mixed temporal field as its a.e. representative. -/
theorem h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At_ae
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
    (j a b c : PrimeTensor.Axis Depth.three) :
    (((h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
          hNS ht₀ hE hTail hq j a b c : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
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
              q)))) := by

  unfold h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3PreterminalSelectedThirdJetRelativeTemporalField_memLp_two
        hNS ht₀ hE hTail hq j a b c)

/-- The final coefficient-topology frontier for the direct order-three
Hilbert-space argument: strong physical `L²` continuity of every selected
third-jet temporal coefficient on the open restart interval. -/
def H3CanonicalSelectedOrder3RelativeTemporalScalarL2ContinuousOnRestartRadius :
    Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j a b c : PrimeTensor.Axis Depth.three),
      Continuous
        (fun q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
            hNS ht₀ hE hTail q.property j a b c)

end

end Euclidean
end Bridge
end PrimeTensor
