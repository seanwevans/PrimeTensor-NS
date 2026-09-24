import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.L2.Jet.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Physical.L2.Jet
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Temporal.Derivative.PDE.Form

/-!
# Selected order-one derivative coefficient in physical L²

`H3PathOrderOneSelectedL2JetReduction` reduced the first H³ energy derivative
to strong `H3ScalarL2` differentiation of the nine selected first spatial jets.

Before proving that Banach-valued derivative, isolate its coefficient as an
actual physical `L²` state.

For one selected coordinate and one spatial derivative,

    ∂ₐ ∂ₜ Sⱼ
      =
    Σₖ ∂ₐ ∂ₖ ∂ₖ Sⱼ
      - ∂ₐ Nⱼ

at unit viscosity.

The first differentiated selected Leray forcing is already in physical `L²`.
Hence the only spatial mass needed for the coefficient is the repeated-index
cubic selected velocity jet.  This file packages precisely that frontier,
proves the mixed temporal field belongs to `L²`, and constructs its canonical
`H3ScalarL2` representative.

After this reduction, the remaining order-one issue is no longer existence of
the derivative coefficient in the Hilbert space.  It is only proving that the
already-packaged first-jet `L²` path has this coefficient as its strong time
derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedTemporalL2Reduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedTemporalL2Reduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The exact selected-side cubic velocity mass needed by the first differentiated
temporal PDE.

Only the repeated-index third derivatives occurring in the Laplacian are
requested.
-/
def H3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        ∀ a k j : PrimeTensor.Axis Depth.three,
          MemLp
            (spatial3.d a
              (spatial3.d k
                (spatial3.d k
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      (h3PreterminalSelectedDecoderAnchorState
                        hNS ht₀ hTail)
                      (lt_of_lt_of_le zero_lt_one hE)
                      (norm_h3PreterminalSelectedDecoderAnchorState_le
                        hNS ht₀ hE hTail)
                      q
                      y).component j))))
            2
            (volume : Measure Point3)

/--
Assuming only the repeated-index cubic selected velocity jets, the first
spatial derivative of the selected temporal derivative belongs to physical
`L²` at every strict positive restart time.
-/
theorem h3PreterminalSelectedFirstJetRelativeTemporalField_memLp_two_of_repeatedThirdVelocityJet
    (hThird :
      H3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius)
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
    (j a : PrimeTensor.Axis Depth.three) :
    MemLp
      (spatial3.d
        a
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
                r
                y).component j)
            q))
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

  have hCubic :
      ∀ k : Fin 3,
        MemLp
          (spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (selected q y).component j))))
          2
          (volume : Measure Point3) := by
    intro k

    dsimp only [selected, U₀, hA, hU₀]

    exact
      hThird
        E u T t₀ hNS ht₀ hE hTail
        q hq
        a
        (h3AxisOfFin3 k)
        j

  have hDiffusion :
      MemLp
        (fun y : Point3 =>
          ∑ k : Fin 3,
            spatial3.d a
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun z : Point3 =>
                    (selected q z).component j)))
              y)
        2
        (volume : Measure Point3) := by
    exact
      MeasureTheory.memLp_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _hk => hCubic k)

  have hForcing :
      MemLp
        (spatial3.d
          a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W q) (W q)
              (h3ClassicalizationFinOfAxis j)
              y).re))
        2
        (volume : Measure Point3) := by
    dsimp only [W, U₀, hA, hU₀]

    exact
      h3SelectedRestartRealLerayForcing_spatial_d_memLp2
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        hq.1
        hq.2
        (h3ClassicalizationFinOfAxis j)
        a

  have hRHS :
      MemLp
        ((fun y : Point3 =>
          ∑ k : Fin 3,
            spatial3.d a
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun z : Point3 =>
                    (selected q z).component j)))
              y)
          -
        spatial3.d
          a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W q) (W q)
              (h3ClassicalizationFinOfAxis j)
              y).re))
        2
        (volume : Measure Point3) :=
    hDiffusion.sub hForcing

  have hField :
      spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (selected r y).component j)
              q)
        =
      (fun y : Point3 =>
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun z : Point3 =>
                  (selected q z).component j)))
            y)
        -
        spatial3.d
          a
          (fun z : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W q) (W q)
              (h3ClassicalizationFinOfAxis j)
              z).re)
          y) := by
    funext y

    dsimp only [selected, W, U₀]

    simpa only [one_mul] using
      spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_mixedDerivativeCandidate
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        hA
        hU₀
        hq.1
        hq.2
        y a j

  rw [hField]
  exact hRHS

/--
Canonical physical `L²` package of one selected first-jet relative temporal
derivative.
-/
noncomputable def h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
    (hThird :
      H3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius)
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
    (j a : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  (h3PreterminalSelectedFirstJetRelativeTemporalField_memLp_two_of_repeatedThirdVelocityJet
      hThird hNS ht₀ hE hTail hq j a).toLp
    (spatial3.d
      a
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
              r
              y).component j)
          q))

/-- The packaged selected first-jet temporal coefficient has the literal mixed
temporal field as its a.e. representative. -/
theorem h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At_ae
    (hThird :
      H3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius)
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
    (j a : PrimeTensor.Axis Depth.three) :
    (((h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
          hThird hNS ht₀ hE hTail hq j a : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d
      a
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
              r
              y).component j)
          q)) := by
  unfold h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3PreterminalSelectedFirstJetRelativeTemporalField_memLp_two_of_repeatedThirdVelocityJet
        hThird hNS ht₀ hE hTail hq j a)

end

end Euclidean
end Bridge
end PrimeTensor
