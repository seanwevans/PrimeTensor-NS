import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Flux.Coordinate.Integrability

/-!
# Basic concrete data for automatic selected transport flux cancellation

The generic flux-coordinate theorem now asks the concrete weak--strong pair for
only four ingredients:

* a uniform bound on the selected velocity component;
* a uniform bound on its first spatial derivative;
* `D_j ∈ L²`;
* `∂ᵢ D_j ∈ L²`.

The selected first-derivative envelope is already available.  This checkpoint
closes the zeroth-order selected envelope and the `L²` membership of every
selected-minus-old difference component.

After this file the only missing input for fully automatic selected flux
cancellation is

    ∂ᵢ D_j ∈ L².

That last fact is spectral: the concrete difference is an H³ state difference,
and the existing bounded raw-derivative multiplier spends one H³ derivative.
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

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedFluxBasicData
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit uniform pointwise envelope for a selected restart velocity
component. -/
noncomputable def h3PreterminalSelectedWeakStrongVelocityEnvelope
    (E : ℝ) : ℝ :=
  h3RawFourierL1DeweightingCoefficient * (2 * E)

/-- Every selected unit-viscosity restart velocity component is uniformly
bounded by the H³ zeroth-order evaluation envelope. -/
theorem norm_h3PreterminalSelectedWeakStrongVelocity_component_le_envelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    ‖((h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
        s x).component j‖
      ≤
    h3PreterminalSelectedWeakStrongVelocityEnvelope E := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hEpos hU₀

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hEvaluation :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s k) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖W s k‖ :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_apply_le
      (W s k) x

  have hCoordinate :
      ‖W s k‖ ≤ ‖W s‖ := by
    exact
      h3SpectralVelocity_coordinate_norm_le
        (W s) k

  have hWBound :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      (one_pos : (0 : ℝ) < 1)
      (h3FinHeatLerayRestartRadius_pos
        (1 : ℝ)
        hEpos).le
      U₀
      hEpos
      hU₀
      (h3FinHeatLerayRestartRadius_smallness
        (1 : ℝ)
        hEpos.le)

  have hPath :
      ‖W s‖ ≤ 2 * E := by
    dsimp only [W]

    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWBound.2 s

  have hScalar :
      ‖W s k‖ ≤ 2 * E :=
    hCoordinate.trans hPath

  have hBound :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s k) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient * (2 * E) :=
    hEvaluation.trans
      (mul_le_mul_of_nonneg_left
        hScalar
        h3RawFourierL1DeweightingCoefficient_nonneg)

  have hSelectedComponent :
      (fun y : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
          s y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W s k) := by
    funext y

    unfold h3PreterminalSelectedWeakStrongVelocity
    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

    rw [h3SpectralRealVelocityOfPath_component]

    rfl

  have hSelectedPoint :
      ((h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
        s x).component j
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W s k) x := by
    exact congrFun hSelectedComponent x

  unfold h3PreterminalSelectedWeakStrongVelocityEnvelope

  calc
    ‖((h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
        s x).component j‖
        =
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s k) x‖ := by
            exact congrArg norm hSelectedPoint
    _ ≤
      h3RawFourierL1DeweightingCoefficient * (2 * E) :=
        hBound

/-- Every concrete selected-minus-old scalar velocity difference component is
an actual `L²` function.  This is transferred directly from the corresponding
coordinate of the already-constructed physical `PiLp 2` difference state. -/
theorem h3PreterminalSelectedOldWeakStrongVelocityDifferenceComponent_memLp_two
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
      h3PreterminalOldElapsedWeakStrongVelocity u t
    MemLp
      (selectedOldVelocityDifferenceComponent
        selected old (q : ℝ) j)
      2
      (volume : Measure Point3) := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let D :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q

  have hAxis :
      h3AxisOfFin3 k = j := by
    dsimp only [k]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hRep :
      selectedOldVelocityDifferenceComponent
          selected old (q : ℝ) j
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (D k : H3ScalarL2) x) := by
    have h :=
      h3PreterminalSelectedOldVelocityDifference_coordinate_ae
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q k

    change
      (fun x : Point3 =>
        (selected (q : ℝ) x).component (h3AxisOfFin3 k)
          -
        (old (q : ℝ) x).component (h3AxisOfFin3 k))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (D k : H3ScalarL2) x)
      at h

    rw [hAxis] at h

    unfold selectedOldVelocityDifferenceComponent

    exact h

  have hD :
      MemLp
        (fun x : Point3 =>
          (D k : H3ScalarL2) x)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp (D k)

  exact
    (memLp_congr_ae hRep).2 hD

end

end Euclidean
end Bridge
end PrimeTensor
