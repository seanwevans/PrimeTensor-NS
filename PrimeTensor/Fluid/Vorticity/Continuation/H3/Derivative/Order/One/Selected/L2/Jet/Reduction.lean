import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Energy.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Difference.Derivative.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSMass
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Reduce selected order-one H³ energy differentiation to nine strong L² jet derivatives

The preceding reduction isolated the only remaining order-one scalar task on
the selected restart:

    d/dt Σⱼ Σᵢ ∫ |∂ᵢ Sⱼ|².

This file removes the spatial integral from that frontier.

Every first selected spatial derivative is already known to lie in physical
`L²(Point3)`.  Package it canonically as an `H3ScalarL2`.  Its squared Hilbert
norm is exactly the corresponding `spatialSquareEnergy`.

Therefore, if each of the nine selected first-jet `L²` paths has its genuine
strong derivative, Hilbert-space norm-square calculus gives the selected
order-one scalar energy derivative immediately.  The only coefficient
identification is the standard real `L²` inner product against the a.e.
representatives.

Thus the remaining order-one analytic frontier is reduced to one generic
Banach-valued statement:

    d/dt [∂ᵢ Sⱼ]_{L²}
      = [∂ᵢ ∂ₜSⱼ]_{L²}.

No differentiation under a whole-space integral remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedL2JetReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One selected first spatial derivative, canonically packaged in physical
`L²(Point3)`. -/
noncomputable def h3PreterminalSelectedFirstJetScalarL2At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (j i : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  (h3PreterminalSelectedWeakStrongVelocity_spatial_d_memLp_two
      hNS ht hE hTail s j i).toLp
    (spatial3.d
      i
      (fun x : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
          s x).component j))

/-- The canonical `L²` package represents the literal selected first spatial
derivative almost everywhere. -/
theorem h3PreterminalSelectedFirstJetScalarL2At_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (j i : PrimeTensor.Axis Depth.three) :
    (((h3PreterminalSelectedFirstJetScalarL2At
          hNS ht hE hTail s j i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d
      i
      (fun x : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
          s x).component j)) := by
  unfold h3PreterminalSelectedFirstJetScalarL2At

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3PreterminalSelectedWeakStrongVelocity_spatial_d_memLp_two
        hNS ht hE hTail s j i)

/-- The squared norm of one selected first-jet `L²` slot is exactly its
PrimeTensor spatial square energy. -/
theorem norm_sq_h3PreterminalSelectedFirstJetScalarL2At_eq_spatialSquareEnergy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (j i : PrimeTensor.Axis Depth.three) :
    ‖h3PreterminalSelectedFirstJetScalarL2At
        hNS ht hE hTail s j i‖ ^ 2
      =
    spatialSquareEnergy
      (spatial3.d
        i
        (fun x : Point3 =>
          ((h3PreterminalSelectedWeakStrongVelocity
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail)
            s x).component j)) := by
  rw [h3ScalarL2_norm_sq_eq_spatialSquareEnergy_coe]

  unfold spatialSquareEnergy

  apply integral_congr_ae

  filter_upwards [
    h3PreterminalSelectedFirstJetScalarL2At_ae
      hNS ht hE hTail s j i
  ] with x hx

  rw [hx]

/--
The remaining selected order-one Banach-valued frontier.

At every strict absolute restart time and for every first spatial jet slot,
there is an `H3ScalarL2` derivative whose a.e. representative is the literal
first spatial derivative of the selected absolute-time temporal derivative.
-/
def H3CanonicalSelectedOrder1PhysicalL2StrongDerivativeOnRestartRadius : Prop :=
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
        ∀ j i : PrimeTensor.Axis Depth.three,
          ∃ D : H3ScalarL2,
            HasDerivAt
              (fun τ : ℝ =>
                h3PreterminalSelectedFirstJetScalarL2At
                  hNS ht₀ hE hTail (τ - t₀) j i)
              D
              s
            ∧
            (((D : H3ScalarL2) : Point3 → ℝ)
              =ᵐ[(volume : Measure Point3)]
            spatial3.d
              i
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
                  s))

/-- Nine strong selected first-jet `L²` derivatives imply the selected scalar
order-one energy derivative frontier. -/
theorem h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_physicalL2StrongDerivative
    (hStrong :
      H3CanonicalSelectedOrder1PhysicalL2StrongDerivativeOnRestartRadius) :
    H3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail
  intro s hs

  let selected :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht₀ hE hTail

  have hEach :
      ∀ j i : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun τ : ℝ =>
            spatialSquareEnergy
              (spatial3.d
                i
                (fun y : Point3 =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalSelectedDecoderAnchorState
                      hNS ht₀ hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalSelectedDecoderAnchorState_le
                      hNS ht₀ hE hTail)
                    (τ - t₀)
                    y).component j)))
          (spatialEnergyPairing
            (spatial3.d
              i
              (fun y : Point3 =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  (s - t₀)
                  y).component j))
            (spatial3.d
              i
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
                  s)))
          s := by
    intro j i

    rcases hStrong
      E u T t₀ hNS ht₀ hE hTail
      s hs j i with
      ⟨D, hD, hDae⟩

    let X : H3ScalarL2 :=
      h3PreterminalSelectedFirstJetScalarL2At
        hNS ht₀ hE hTail (s - t₀) j i

    have hXae :
        (((X : H3ScalarL2) : Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d
          i
          (fun y : Point3 =>
            (selected (s - t₀) y).component j)) := by
      dsimp only [X]
      simpa only [selected] using
        h3PreterminalSelectedFirstJetScalarL2At_ae
          hNS ht₀ hE hTail (s - t₀) j i

    have hDaeSelected :
        (((D : H3ScalarL2) : Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d
          i
          (fun y : Point3 =>
            temporal.d
              (fun τ : ℝ =>
                (selected (τ - t₀) y).component j)
              s)) := by
      simpa only [
        selected,
        h3PreterminalSelectedWeakStrongVelocity
      ] using hDae

    have hCoefficient :
        2 * inner ℝ X D
          =
        spatialEnergyPairing
          (spatial3.d
            i
            (fun y : Point3 =>
              (selected (s - t₀) y).component j))
          (spatial3.d
            i
            (fun y : Point3 =>
              temporal.d
                (fun τ : ℝ =>
                  (selected (τ - t₀) y).component j)
                s)) := by
      unfold spatialEnergyPairing
      congr 1

      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae

      filter_upwards [hXae, hDaeSelected] with y hX hDy

      rw [hX, hDy]
      simp [RCLike.inner_apply, mul_comm]

    have hNorm :
        HasDerivAt
          (fun τ : ℝ =>
            ‖h3PreterminalSelectedFirstJetScalarL2At
                hNS ht₀ hE hTail (τ - t₀) j i‖ ^ 2)
          (2 * inner ℝ X D)
          s := by
      have h := hD.norm_sq
      dsimp only [X] at h ⊢
      exact h

    have hNormCoefficient :
        HasDerivAt
          (fun τ : ℝ =>
            ‖h3PreterminalSelectedFirstJetScalarL2At
                hNS ht₀ hE hTail (τ - t₀) j i‖ ^ 2)
          (spatialEnergyPairing
            (spatial3.d
              i
              (fun y : Point3 =>
                (selected (s - t₀) y).component j))
            (spatial3.d
              i
              (fun y : Point3 =>
                temporal.d
                  (fun τ : ℝ =>
                    (selected (τ - t₀) y).component j)
                  s)))
          s :=
      hNorm.congr_deriv hCoefficient

    have hEnergyEq :
        (fun τ : ℝ =>
          ‖h3PreterminalSelectedFirstJetScalarL2At
              hNS ht₀ hE hTail (τ - t₀) j i‖ ^ 2)
          =ᶠ[𝓝 s]
        (fun τ : ℝ =>
          spatialSquareEnergy
            (spatial3.d
              i
              (fun y : Point3 =>
                (selected (τ - t₀) y).component j))) := by
      filter_upwards with τ

      simpa only [selected] using
        norm_sq_h3PreterminalSelectedFirstJetScalarL2At_eq_spatialSquareEnergy
          hNS ht₀ hE hTail (τ - t₀) j i

    have hSelected :
        HasDerivAt
          (fun τ : ℝ =>
            spatialSquareEnergy
              (spatial3.d
                i
                (fun y : Point3 =>
                  (selected (τ - t₀) y).component j)))
          (spatialEnergyPairing
            (spatial3.d
              i
              (fun y : Point3 =>
                (selected (s - t₀) y).component j))
            (spatial3.d
              i
              (fun y : Point3 =>
                temporal.d
                  (fun τ : ℝ =>
                    (selected (τ - t₀) y).component j)
                  s)))
          s :=
      hNormCoefficient.congr_of_eventuallyEq
        hEnergyEq.symm

    simpa only [
      selected,
      h3PreterminalSelectedWeakStrongVelocity
    ] using hSelected

  have hInner :
      ∀ j : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun τ : ℝ =>
            ∑ i : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d
                  i
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      (h3PreterminalSelectedDecoderAnchorState
                        hNS ht₀ hTail)
                      (lt_of_lt_of_le zero_lt_one hE)
                      (norm_h3PreterminalSelectedDecoderAnchorState_le
                        hNS ht₀ hE hTail)
                      (τ - t₀)
                      y).component j)))
          (∑ i : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d
                i
                (fun y : Point3 =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalSelectedDecoderAnchorState
                      hNS ht₀ hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalSelectedDecoderAnchorState_le
                      hNS ht₀ hE hTail)
                    (s - t₀)
                    y).component j))
              (spatial3.d
                i
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
                    s)))
          s := by
    intro j
    apply HasDerivAt.fun_sum
    intro i hi
    exact hEach j i

  have hSum :
      HasDerivAt
        (fun τ : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d
                  i
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      (h3PreterminalSelectedDecoderAnchorState
                        hNS ht₀ hTail)
                      (lt_of_lt_of_le zero_lt_one hE)
                      (norm_h3PreterminalSelectedDecoderAnchorState_le
                        hNS ht₀ hE hTail)
                      (τ - t₀)
                      y).component j)))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d
                i
                (fun y : Point3 =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalSelectedDecoderAnchorState
                      hNS ht₀ hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalSelectedDecoderAnchorState_le
                      hNS ht₀ hE hTail)
                    (s - t₀)
                    y).component j))
              (spatial3.d
                i
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
                    s)))
        s := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact hInner j

  exact hSum

/-- It is enough to close the nine selected first-jet strong `L²` derivatives;
the old canonical order-one derivative identity then follows automatically. -/
theorem h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selectedPhysicalL2StrongDerivative
    (hStrong :
      H3CanonicalSelectedOrder1PhysicalL2StrongDerivativeOnRestartRadius)
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
      (h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_physicalL2StrongDerivative
        hStrong)
      hH3 hClass hs

end

end Euclidean
end Bridge
end PrimeTensor
