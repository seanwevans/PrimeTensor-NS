import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Weak.First.Jet.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Time.Derivative.Spatial.C2

/-!
# Weak derivative of one selected second spatial jet

The order-two strong `L²` FTC argument needs the scalar weak evolution of every
ordered second selected velocity jet.

For a compact scalar test `φ`,

    ∫ φ ∂ₐ∂ᵦ Sⱼ
      = - ∫ (∂ₐφ) ∂ᵦ Sⱼ.

The right-hand side is exactly the already-closed selected first-jet weak
pairing.  We therefore define the globally total second-jet weak pairing by
that integration-by-parts expression.  This avoids imposing global `C²`
regularity on the total real-time spectral extension.

At every strict positive selected restart time, the selected velocity is
spatially `C²`; likewise its actual temporal derivative is spatially `C²`.
Separate integration-by-parts lemmas therefore identify these total weak
pairings with the literal second spatial jet and literal mixed temporal second
jet.

The derivative theorem itself is then immediate from the already-closed
first-jet weak derivative theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedWeakSecondJetDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderTwoSelectedWeakSecondJetDerivative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Globally total compact-test pairing with an ordered selected second spatial
jet, represented by one integration by parts against the already-total
first-jet pairing. -/
noncomputable def h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (r : ℝ) :
    ℝ :=
  -
  h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
    hNS ht hE hTail
    (h3WeakTestFunctionSpatialDerivative a φ)
    j b r

/-- Globally total compact-test pairing with the corresponding
second-spatial / first-temporal selected coefficient. -/
noncomputable def h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (r : ℝ) :
    ℝ :=
  -
  h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
    hNS ht hE hTail
    (h3WeakTestFunctionSpatialDerivative a φ)
    j b r

/-! ## Literal positive-time identifications -/

/-- At a strict positive selected time, the total second-jet weak pairing is
the literal compact-test pairing with `∂ₐ∂ᵦ Sⱼ`. -/
theorem h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal_eq_literal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal
        hNS ht hE hTail φ j a b s
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d a
          (spatial3.d b
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s j)))
          x)
      ∂volume := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hsR :
      s < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    lt_of_lt_of_le hs.2 htauR

  have hBaseC2 :
      SpatialC2
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s j)) := by
    unfold SpatialC2
    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart,
      U₀, hA, hU₀
    ]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        2
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        hs.1 hsR.le j

  have hFirstC1 :
      SpatialC1
        (spatial3.d b
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s j))) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hBaseC2 b

  have hIBP :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hFirstC1 a φ

  dsimp only [
    h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal,
    h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal,
    W
  ]

  exact hIBP.symm

/-- At a strict positive selected time, the total temporal second-jet weak
pairing is the literal compact-test pairing with `∂ₐ∂ᵦ∂ₜ Sⱼ`. -/
theorem h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal_eq_literal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal
        hNS ht hE hTail φ j a b s
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d a
          (spatial3.d b
            (fun y : Point3 =>
              temporal.d
                (fun q : ℝ =>
                  h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W q j) y)
                s))
          x)
      ∂volume := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hsR :
      s < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    lt_of_lt_of_le hs.2 htauR

  have hTemporalC2 :
      SpatialC2
        (fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q j) y)
            s) := by
    unfold SpatialC2

    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart,
      temporal_d,
      U₀, hA, hU₀
    ]

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_spatial_contDiff_two
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        hs.1 hsR j

  have hTemporalFirstC1 :
      SpatialC1
        (spatial3.d b
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W q j) y)
              s)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hTemporalC2 b

  have hIBP :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hTemporalFirstC1 a φ

  dsimp only [
    h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal,
    h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal,
    W
  ]

  exact hIBP.symm

/-! ## Weak derivative -/

/-- Every compact scalar test sees the correct time derivative of every ordered
selected second spatial jet. -/
theorem h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal_hasDerivAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal
        hNS ht hE hTail φ j a b)
      (h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal
        hNS ht hE hTail φ j a b s)
      s := by

  let dφ : H3WeakTestFunction :=
    h3WeakTestFunctionSpatialDerivative a φ

  have hFirst :
      HasDerivAt
        (h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
          hNS ht hE hTail dφ j b)
        (h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
          hNS ht hE hTail dφ j b s)
        s := by
    exact
      h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal_hasDerivAt
        hNS ht htau hE hTail htauR hs
        dφ j b

  have hNeg :=
    hFirst.neg

  change
    HasDerivAt
      (-
        h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
          hNS ht hE hTail dφ j b)
      (-
        h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
          hNS ht hE hTail dφ j b s)
      s

  exact hNeg

end

end Euclidean
end Bridge
end PrimeTensor
