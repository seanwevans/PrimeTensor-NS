import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedForcingFirstCoordinateOpenL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedCubicVelocityPhysicalL2Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedStrongL2FromCoefficientContinuity

/-!
# Close selected order-one temporal coefficient continuity

The two pieces of the differentiated selected velocity equation are now
strongly continuous in physical `L²` on the complete open restart interval:

* every repeated-index cubic velocity jet
  `∂ₐ ∂ₖ ∂ₖ Sⱼ`;
* every first selected Leray-forcing jet `∂ₐ Nⱼ`.

This file packages their finite sum/difference as one canonical physical
`H3ScalarL2` path, identifies it with the already-defined mixed temporal
coefficient using the pointwise selected PDE, and closes
`H3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedTemporalL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedTemporalL2Continuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Physical `L²` package of the order-one selected PDE right-hand side at one
strict positive restart time. -/
noncomputable def h3SelectedRestartOrderOneRHSScalarL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  (∑ k : Fin 3,
    h3SelectedRestartRealVelocityThirdCoordinateL2
      hν U₀ hA hU₀ q j a
      (h3AxisOfFin3 k) (h3AxisOfFin3 k))
  -
  h3SelectedRestartRealLerayForcingFirstCoordinateL2
    hν U₀ hA hU₀ q j a

/-- The assembled selected order-one PDE right-hand side is strongly continuous
in physical `L²` on the open restart interval. -/
theorem continuous_h3SelectedRestartOrderOneRHSScalarL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartOrderOneRHSScalarL2
          hν U₀ hA hU₀ q j a) := by
  have hDiffusion :
      Continuous
        (fun q : Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius ν A) =>
          ∑ k : Fin 3,
            h3SelectedRestartRealVelocityThirdCoordinateL2
              hν U₀ hA hU₀ q j a
              (h3AxisOfFin3 k) (h3AxisOfFin3 k)) := by
    apply continuous_finsetSum
    intro k hk
    exact
      continuous_h3SelectedRestartRealVelocityRepeatedThirdCoordinateL2
        hν U₀ hA hU₀ j a (h3AxisOfFin3 k)

  have hForcing :
      Continuous
        (fun q : Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius ν A) =>
          h3SelectedRestartRealLerayForcingFirstCoordinateL2
            hν U₀ hA hU₀ q j a) :=
    continuous_h3SelectedRestartRealLerayForcingFirstCoordinateL2
      hν U₀ hA hU₀ j a

  have hRHS := hDiffusion.sub hForcing

  change
    Continuous
      ((fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        ∑ k : Fin 3,
          h3SelectedRestartRealVelocityThirdCoordinateL2
            hν U₀ hA hU₀ q j a
            (h3AxisOfFin3 k) (h3AxisOfFin3 k))
      -
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartRealLerayForcingFirstCoordinateL2
          hν U₀ hA hU₀ q j a))
  exact hRHS

/-- A.e. representative of the assembled order-one selected PDE right-hand
side. -/
theorem h3SelectedRestartOrderOneRHSScalarL2_ae
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (((h3SelectedRestartOrderOneRHSScalarL2
          hν U₀ hA hU₀ q j a : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (∑ k : Fin 3,
        spatial3.d a
          (spatial3.d (h3AxisOfFin3 k)
            (spatial3.d (h3AxisOfFin3 k)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W (q : ℝ) j))))
          x)
      -
      spatial3.d a
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ)) (W (q : ℝ)) j y).re)
        x)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3ScalarL2 :=
    ∑ k : Fin 3,
      h3SelectedRestartRealVelocityThirdCoordinateL2
        hν U₀ hA hU₀ q j a
        (h3AxisOfFin3 k) (h3AxisOfFin3 k)

  let F : H3ScalarL2 :=
    h3SelectedRestartRealLerayForcingFirstCoordinateL2
      hν U₀ hA hU₀ q j a

  have hSub :=
    MeasureTheory.Lp.coeFn_sub D F

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k : Fin 3 =>
        h3SelectedRestartRealVelocityThirdCoordinateL2
          hν U₀ hA hU₀ q j a
          (h3AxisOfFin3 k) (h3AxisOfFin3 k))

  have hTerms :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ k : Fin 3,
          (((h3SelectedRestartRealVelocityThirdCoordinateL2
              hν U₀ hA hU₀ q j a
              (h3AxisOfFin3 k) (h3AxisOfFin3 k) : H3ScalarL2) :
              Point3 → ℝ) x)
            =
          spatial3.d a
            (spatial3.d (h3AxisOfFin3 k)
              (spatial3.d (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) j))))
            x := by
    exact ae_all_iff.2 (fun k => by
      dsimp only [W]
      unfold h3SelectedRestartRealVelocityThirdCoordinateL2
      exact
        MeasureTheory.MemLp.coeFn_toLp
          (h3SelectedRestartRealVelocity_spatial_d_three_memLp2
            hν U₀ hA hU₀ q.property.1 q.property.2 j a
            (h3AxisOfFin3 k) (h3AxisOfFin3 k)))

  have hForce :=
    h3SelectedRestartRealLerayForcingFirstCoordinateL2_ae
      hν U₀ hA hU₀ q j a

  filter_upwards [hSub, hSum, hTerms, hForce] with
      x hSubx hSumx hTermsx hForcex

  change (((D - F : H3ScalarL2) : Point3 → ℝ) x) = _
  rw [hSubx]
  simp only [Pi.sub_apply]
  rw [hSumx]
  simp only [Finset.sum_apply]
  rw [hForcex]

  apply congrArg (fun z : ℝ => z -
    spatial3.d a
      (fun y : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W (q : ℝ)) (W (q : ℝ)) j y).re)
      x)

  apply Finset.sum_congr rfl
  intro k hk
  exact hTermsx k

/-- The already-packaged mixed temporal coefficient is exactly the assembled
physical `L²` PDE right-hand side. -/
theorem h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At_eq_orderOneRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j a : PrimeTensor.Axis Depth.three) :
    h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
        h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
        hNS ht₀ hE hTail q.property j a
      =
    h3SelectedRestartOrderOneRHSScalarL2
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      q
      (h3ClassicalizationFinOfAxis j)
      a := by
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

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxisJ :
      h3AxisOfFin3 jf = j := by
    dsimp only [jf]
    exact h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hComponent :
      (fun y : Point3 =>
        (selected (q : ℝ) y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W (q : ℝ) jf) := by
    funext y
    rw [← hAxisJ]
    simp only [
      selected,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      W
    ]

  have hField :
      spatial3.d a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (selected r y).component j)
              (q : ℝ))
        =
      (fun x : Point3 =>
        (∑ k : Fin 3,
          spatial3.d a
            (spatial3.d (h3AxisOfFin3 k)
              (spatial3.d (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) jf))))
            x)
        -
        spatial3.d a
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) jf y).re)
          x) := by
    funext x

    have hPDE :=
      spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_mixedDerivativeCandidate
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        q.property.1 q.property.2
        x a j

    rw [hComponent] at hPDE

    simpa only [one_mul, selected, W, jf] using hPDE

  have hTemporal :=
    h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At_ae
      h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
      hNS ht₀ hE hTail q.property j a

  have hRHS :=
    h3SelectedRestartOrderOneRHSScalarL2_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ q jf a

  filter_upwards [hTemporal, hRHS] with x hTemporalx hRHSx

  rw [hTemporalx, hRHSx]

  exact congrFun hField x

/-- The selected order-one mixed temporal coefficient is strongly continuous
on the complete open restart interval. -/
theorem h3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius_closed :
    H3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail j a

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hRHS :
      Continuous
        (fun q : Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3SelectedRestartOrderOneRHSScalarL2
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀ q jf a) :=
    continuous_h3SelectedRestartOrderOneRHSScalarL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ jf a

  have hEq :
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
          h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
          hNS ht₀ hE hTail q.property j a)
        =
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3SelectedRestartOrderOneRHSScalarL2
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ q jf a) := by
    funext q
    dsimp only [U₀, hA, hU₀, jf]
    exact
      h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At_eq_orderOneRHS
        hNS ht₀ hE hTail q j a

  rw [hEq]
  exact hRHS

end

end Euclidean
end Bridge
end PrimeTensor
