import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Scalar.Weak.Test.Density
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.L2.Jet.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Mixed.Derivative.Absolute.Time

/-!
# Reduce the selected order-one strong L² frontier to elapsed time

The selected restart is natively parameterized by elapsed time.  The existing
order-one strong `L²` frontier is written in absolute time only because the
continuation/gluing layer uses

    τ ↦ S(τ - t₀).

This file removes that bookkeeping from the remaining Hilbert-space analysis.

We introduce the restart-relative frontier

    d/dq [∂ᵢ Sⱼ(q)]_{L²}
      =
    [∂ᵢ ∂q Sⱼ(q)]_{L²},

prove that it implies the already-defined absolute-time frontier by composing
with `τ ↦ τ - t₀`, and transport the derivative coefficient through the same
relative/absolute temporal-field identity used by the pointwise mixed
derivative theorem.

The scalar density result from the preceding checkpoint is also recorded in
its useful Hilbert form: compact smooth weak-test pairings determine arbitrary
`H3ScalarL2` states exactly.

Thus every subsequent weak-to-strong argument can be carried out entirely in
elapsed time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedRelativeStrongL2Reduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedRelativeStrongL2Reduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Dense compact smooth scalar weak tests determine physical scalar `L²`
states exactly by Hilbert pairing. -/
theorem h3ScalarL2_eq_of_weakTest_inner_eq_orderOne
    {F G : H3ScalarL2}
    (h :
      ∀ φ : H3WeakTestFunction,
        inner ℝ
            (h3WeakTestFunctionPhysicalL2 φ)
            F
          =
        inner ℝ
            (h3WeakTestFunctionPhysicalL2 φ)
            G) :
    F = G := by
  exact
    DenseRange.eq_of_inner_right
      ℝ
      denseRange_h3WeakTestFunctionPhysicalL2_orderOne
      h

/--
Restart-relative form of the remaining selected order-one Banach-valued
frontier.

At every strict elapsed restart time, every selected first spatial jet has a
genuine `H3ScalarL2` derivative whose a.e. representative is the literal
restart-relative mixed derivative.
-/
def H3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius : Prop :=
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
        ∀ j i : PrimeTensor.Axis Depth.three,
          ∃ D : H3ScalarL2,
            HasDerivAt
              (fun r : ℝ =>
                h3PreterminalSelectedFirstJetScalarL2At
                  hNS ht₀ hE hTail r j i)
              D
              q
            ∧
            (((D : H3ScalarL2) : Point3 → ℝ)
              =ᵐ[(volume : Measure Point3)]
            spatial3.d
              i
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

/-- Restart-relative strong first-jet `L²` differentiation implies the
absolute-time frontier used by the order-one energy reduction. -/
theorem h3CanonicalSelectedOrder1PhysicalL2StrongDerivativeOnRestartRadius_of_relative
    (hRelative :
      H3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius) :
    H3CanonicalSelectedOrder1PhysicalL2StrongDerivativeOnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail
  intro s hs
  intro j i

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

  rcases
    hRelative
      E u T t₀ hNS ht₀ hE hTail
      q hq j i
    with
    ⟨D, hD, hDae⟩

  have hShift :
      HasDerivAt
        (fun τ : ℝ => τ - t₀)
        1
        s := by
    simpa using
      (hasDerivAt_id s).sub_const t₀

  have hDAtShift :
      HasDerivAt
        (fun r : ℝ =>
          h3PreterminalSelectedFirstJetScalarL2At
            hNS ht₀ hE hTail r j i)
        D
        (s - t₀) := by
    simpa only [q] using hD

  have hAbsolute :
      HasDerivAt
        (fun τ : ℝ =>
          h3PreterminalSelectedFirstJetScalarL2At
            hNS ht₀ hE hTail (τ - t₀) j i)
        D
        s := by
    have hComp :=
      hDAtShift.scomp s hShift

    simpa only [
      Function.comp_def,
      one_smul
    ] using hComp

  have hTemporalFieldEq :
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

  have hCoefficientFieldEq :
      spatial3.d
          i
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
      spatial3.d
          i
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  (one_pos : (0 : ℝ) < 1)
                  U₀ hA hU₀
                  r
                  y).component j)
              q) :=
    congrArg
      (fun f : ScalarField3 => spatial3.d i f)
      hTemporalFieldEq

  refine
    ⟨D, hAbsolute, ?_⟩

  have hDaeRelative :
      (((D : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d
        i
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀
                r
                y).component j)
            q)) := by
    simpa only [U₀, hA, hU₀] using hDae

  rw [hCoefficientFieldEq]

  exact hDaeRelative

/-- The elapsed-time strong first-jet frontier is sufficient for the selected
order-one scalar energy derivative. -/
theorem h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_relativePhysicalL2StrongDerivative
    (hRelative :
      H3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius) :
    H3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius := by
  exact
    h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_physicalL2StrongDerivative
      (h3CanonicalSelectedOrder1PhysicalL2StrongDerivativeOnRestartRadius_of_relative
        hRelative)

/-- The elapsed-time strong first-jet frontier is sufficient for the actual
old H³ path order-one energy derivative identity. -/
theorem h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selectedRelativePhysicalL2StrongDerivative
    (hRelative :
      H3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
      (velocityH3Energy1At u)
      (velocityH3FormalDerivative1At u s)
      s := by
  exact
    h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selected
      (h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_relativePhysicalL2StrongDerivative
        hRelative)
      hH3 hClass hs

end

end Euclidean
end Bridge
end PrimeTensor
