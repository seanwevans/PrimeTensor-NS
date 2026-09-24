import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Weak.Second.Jet.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Time.Derivative.Spatial.C3

/-!
# Weak derivative of one selected third spatial jet

The order-three strong `L²` FTC argument needs the scalar weak evolution of every
ordered third selected velocity jet.

For a compact scalar test `φ`,

    ∫ φ ∂ₐ∂ᵦ∂𝑐 Sⱼ
      = - ∫ (∂ₐφ) ∂ᵦ∂𝑐 Sⱼ.

The right-hand side is exactly the already-closed selected second-jet weak
pairing.  We therefore define the globally total third-jet weak pairing by one
more integration by parts.

At every strict positive selected restart time, the selected velocity is
spatially `C³`; the actual selected temporal derivative is now also spatially
`C³`.  These regularity statements identify the total weak pairings with the
literal third spatial jet and literal mixed temporal third jet.

The derivative theorem then follows immediately from the closed second-jet
weak derivative theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedWeakThirdJetDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderThreeSelectedWeakThirdJetDerivative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Globally total compact-test pairing with an ordered selected third spatial
jet, represented by one integration by parts against the already-total
second-jet pairing. -/
noncomputable def h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (r : ℝ) :
    ℝ :=
  -
  h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal
    hNS ht hE hTail
    (h3WeakTestFunctionSpatialDerivative a φ)
    j b c r

/-- Globally total compact-test pairing with the corresponding
third-spatial / first-temporal selected coefficient. -/
noncomputable def h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (r : ℝ) :
    ℝ :=
  -
  h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal
    hNS ht hE hTail
    (h3WeakTestFunctionSpatialDerivative a φ)
    j b c r

/-! ## Literal positive-time identifications -/

/-- At a strict positive selected time, the total third-jet weak pairing is
the literal compact-test pairing with `∂ₐ∂ᵦ∂𝑐 Sⱼ`. -/
theorem h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal_eq_literal
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
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
        hNS ht hE hTail φ j a b c s
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W s j))))
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

  have hBaseC3 :
      SpatialC3
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s j)) := by
    unfold SpatialC3
    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart,
      U₀, hA, hU₀
    ]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        3
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        hs.1 hsR.le j

  have hFirstC2 :
      SpatialC2
        (spatial3.d c
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s j))) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hBaseC3 c

  have hSecondC1 :
      SpatialC1
        (spatial3.d b
          (spatial3.d c
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W s j)))) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hFirstC2 b

  have hSecondLiteral :=
    h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal_eq_literal
      hNS ht htau hE hTail htauR hs
      (h3WeakTestFunctionSpatialDerivative a φ)
      j b c

  have hIBP :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hSecondC1 a φ

  unfold h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
  rw [hSecondLiteral]
  simpa only [W] using hIBP.symm

/-- At a strict positive selected time, the total temporal third-jet weak
pairing is the literal compact-test pairing with `∂ₐ∂ᵦ∂𝑐∂ₜ Sⱼ`. -/
theorem h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal_eq_literal
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
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
        hNS ht hE hTail φ j a b c s
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (fun y : Point3 =>
                temporal.d
                  (fun q : ℝ =>
                    h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W q j) y)
                  s)))
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

  have hTemporalC3 :
      SpatialC3
        (fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q j) y)
            s) := by
    unfold SpatialC3

    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart,
      temporal_d,
      U₀, hA, hU₀
    ]

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_spatial_contDiff_three
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        hs.1 hsR j

  have hTemporalFirstC2 :
      SpatialC2
        (spatial3.d c
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W q j) y)
              s)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hTemporalC3 c

  have hTemporalSecondC1 :
      SpatialC1
        (spatial3.d b
          (spatial3.d c
            (fun y : Point3 =>
              temporal.d
                (fun q : ℝ =>
                  h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W q j) y)
                s))) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hTemporalFirstC2 b

  have hSecondLiteral :=
    h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal_eq_literal
      hNS ht htau hE hTail htauR hs
      (h3WeakTestFunctionSpatialDerivative a φ)
      j b c

  have hIBP :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hTemporalSecondC1 a φ

  unfold h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
  rw [hSecondLiteral]
  simpa only [W] using hIBP.symm

/-! ## Weak derivative -/

/-- Every compact scalar test sees the correct time derivative of every ordered
selected third spatial jet. -/
theorem h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal_hasDerivAt
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
    (a b c : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
        hNS ht hE hTail φ j a b c)
      (h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
        hNS ht hE hTail φ j a b c s)
      s := by

  let dφ : H3WeakTestFunction :=
    h3WeakTestFunctionSpatialDerivative a φ

  have hSecond :
      HasDerivAt
        (h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal
          hNS ht hE hTail dφ j b c)
        (h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal
          hNS ht hE hTail dφ j b c s)
        s := by
    exact
      h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal_hasDerivAt
        hNS ht htau hE hTail htauR hs
        dφ j b c

  have hNeg :=
    hSecond.neg

  change
    HasDerivAt
      (-
        h3PreterminalSelectedUnitWeakSecondJetCoordinatePairingReal
          hNS ht hE hTail dφ j b c)
      (-
        h3PreterminalSelectedUnitWeakSecondJetTemporalCoordinatePairingReal
          hNS ht hE hTail dφ j b c s)
      s

  exact hNeg

end

end Euclidean
end Bridge
end PrimeTensor
