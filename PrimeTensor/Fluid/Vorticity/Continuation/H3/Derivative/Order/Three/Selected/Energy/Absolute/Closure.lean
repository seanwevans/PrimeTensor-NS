import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Strong.L2.From.Coefficient.Continuity

/-!
# Transport selected order-three energy differentiation to absolute time

The relative selected order-three scalar energy derivative is now closed.
This file composes elapsed time with `τ ↦ τ - t₀` and transports the
coefficient through the chain rule.

No new estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedEnergyAbsoluteClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Absolute-time form of the selected order-three scalar energy derivative. -/
def H3CanonicalSelectedOrder3EnergyDerivativeOnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ s : ℝ,
        s ∈
          Set.Ioo
            t₀
            (t₀ + h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        HasDerivAt
          (fun τ : ℝ =>
            ∑ j : PrimeTensor.Axis Depth.three,
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  ∑ l : PrimeTensor.Axis Depth.three,
                    spatialSquareEnergy
                      (spatial3.d i
                        (spatial3.d k
                          (spatial3.d l
                            (fun y : Point3 =>
                              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                                (one_pos : (0 : ℝ) < 1)
                                (h3PreterminalSelectedDecoderAnchorState
                                  hNS ht₀ hTail)
                                (lt_of_lt_of_le zero_lt_one hE)
                                (norm_h3PreterminalSelectedDecoderAnchorState_le
                                  hNS ht₀ hE hTail)
                                (τ - t₀)
                                y).component j)))))
          (∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  spatialEnergyPairing
                    (spatial3.d i
                      (spatial3.d k
                        (spatial3.d l
                          (fun y : Point3 =>
                            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                              (one_pos : (0 : ℝ) < 1)
                              (h3PreterminalSelectedDecoderAnchorState
                                hNS ht₀ hTail)
                              (lt_of_lt_of_le zero_lt_one hE)
                              (norm_h3PreterminalSelectedDecoderAnchorState_le
                                hNS ht₀ hE hTail)
                              (s - t₀)
                              y).component j))))
                    (spatial3.d i
                      (spatial3.d k
                        (spatial3.d l
                          (fun y : Point3 =>
                            temporal.d
                              (fun τ : ℝ =>
                                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                                  (one_pos : (0 : ℝ) < 1)
                                  (h3PreterminalSelectedDecoderAnchorState
                                    hNS ht₀ hTail)
                                  (lt_of_lt_of_le zero_lt_one hE)
                                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                                    hNS ht₀ hE hTail)
                                  (τ - t₀)
                                  y).component j)
                              s)))))
          s

/-- The elapsed-time selected order-three energy derivative transports through
`τ ↦ τ - t₀` to the absolute-time selected statement. -/
theorem h3CanonicalSelectedOrder3EnergyDerivativeOnRestartRadius_of_relative
    (hRelative :
      H3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius) :
    H3CanonicalSelectedOrder3EnergyDerivativeOnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail
  intro s hs

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let q : ℝ :=
    s - t₀

  have hq0 : 0 < q := by
    dsimp only [q]
    exact sub_pos.mpr hs.1

  have hqR :
      q < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    dsimp only [q]
    linarith [hs.2]

  have hq :
      q ∈
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨hq0, hqR⟩

  have hRelativeAt :=
    hRelative
      E u T t₀ hNS ht₀ hE hTail
      q hq

  have hShift :
      HasDerivAt
        (fun τ : ℝ => τ - t₀)
        1
        s := by
    simpa using
      (hasDerivAt_id s).sub_const t₀

  have hAbsoluteRaw :
      HasDerivAt
        (fun τ : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  spatialSquareEnergy
                    (spatial3.d i
                      (spatial3.d k
                        (spatial3.d l
                          (fun y : Point3 =>
                            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                              (one_pos : (0 : ℝ) < 1)
                              U₀ hA hU₀
                              (τ - t₀)
                              y).component j)))))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (fun y : Point3 =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            U₀ hA hU₀
                            q y).component j))))
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (fun y : Point3 =>
                          temporal.d
                            (fun r : ℝ =>
                              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                                (one_pos : (0 : ℝ) < 1)
                                U₀ hA hU₀
                                r y).component j)
                            q)))))
        s := by

    have hComp :=
      hRelativeAt.scomp s hShift

    simpa only [
      Function.comp_def,
      one_smul,
      q,
      U₀, hA, hU₀
    ] using hComp

  have hTemporalFieldEq
      (j : PrimeTensor.Axis Depth.three) :
      (fun y : Point3 =>
        temporal.d
          (fun τ : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (τ - t₀)
              y).component j)
          s)
        =
      (fun y : Point3 =>
        temporal.d
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          q) := by

    funext y

    have hRegularity :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_temporalDerivativeRegularity
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        y j

    dsimp only at hRegularity

    have hfDiff :
        DifferentiableAt ℝ
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          q := by
      exact
        (hRegularity.1 q hq).differentiableAt
          (isOpen_Ioo.mem_nhds hq)

    have hf :
        HasDerivAt
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          (deriv
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀
                r
                y).component j)
            q)
          q :=
      hfDiff.hasDerivAt

    have hComp :=
      hf.comp s hShift

    change
      deriv
          (fun τ : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (τ - t₀)
              y).component j)
          s
        =
      deriv
          (fun r : ℝ =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              r
              y).component j)
          q

    simpa only [
      Function.comp_def,
      mul_one,
      q
    ] using hComp.deriv

  have hCoefficientEq :
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          U₀ hA hU₀
                          q y).component j))))
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (fun y : Point3 =>
                        temporal.d
                          (fun r : ℝ =>
                            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                              (one_pos : (0 : ℝ) < 1)
                              U₀ hA hU₀
                              r y).component j)
                          q)))))
        =
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          U₀ hA hU₀
                          (s - t₀) y).component j))))
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (fun y : Point3 =>
                        temporal.d
                          (fun τ : ℝ =>
                            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                              (one_pos : (0 : ℝ) < 1)
                              U₀ hA hU₀
                              (τ - t₀) y).component j)
                          s))))) := by

    apply Finset.sum_congr rfl
    intro j hj

    apply Finset.sum_congr rfl
    intro i hi

    apply Finset.sum_congr rfl
    intro k hk

    apply Finset.sum_congr rfl
    intro l hl

    have hTime :
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (fun y : Point3 =>
                  temporal.d
                    (fun r : ℝ =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        U₀ hA hU₀
                        r y).component j)
                    q)))
          =
        spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (fun y : Point3 =>
                temporal.d
                  (fun τ : ℝ =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      U₀ hA hU₀
                      (τ - t₀) y).component j)
                  s))) :=
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i
            (spatial3.d k
              (spatial3.d l f)))
        (hTemporalFieldEq j).symm

    rw [hTime]

  exact
    hAbsoluteRaw.congr_deriv
      hCoefficientEq

/-- The closed relative order-three theorem closes the absolute-time selected
order-three scalar energy derivative. -/
theorem h3CanonicalSelectedOrder3EnergyDerivativeOnRestartRadius_closed :
    H3CanonicalSelectedOrder3EnergyDerivativeOnRestartRadius := by

  exact
    h3CanonicalSelectedOrder3EnergyDerivativeOnRestartRadius_of_relative
      h3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius_closed

end

end Euclidean
end Bridge
end PrimeTensor
