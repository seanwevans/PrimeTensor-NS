import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Third.Velocity.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Diffusion.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Coordinate.Pairing.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Time.Derivative.Spatial.C1

/-!
# Weak derivative of one selected first spatial jet

The remaining order-one strong-`L²` problem should not be attacked by
differentiating an `Lp` representative pointwise.

For a compact scalar test `φ` and one selected first spatial jet,

    P(r) = ∫ φ ∂ₐSⱼ(r),

one spatial integration by parts gives

    P(r) = - ∫ (∂ₐφ) Sⱼ(r).

The right-hand side is exactly the already-closed order-zero selected weak
coordinate pairing, with the differentiated compact test.  We can therefore
differentiate it using the existing selected weak-coordinate theorem, without
any domination estimate for the mixed derivative.

At the target time the actual selected temporal derivative is spatially `C¹`.
A second integration by parts then identifies the derivative coefficient with

    ∫ φ ∂ₐ∂ₜSⱼ.

Thus every compact scalar test sees the correct derivative of every selected
first spatial jet.  This is the weak first-jet evolution identity needed for
the final scalar `L²` density/Bochner upgrade.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedWeakFirstJetDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedWeakFirstJetDerivative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Compact-test pairing with one selected first spatial velocity jet. -/
noncomputable def h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (r : ℝ) :
    ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      (spatial3.d
        a
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W r j))
        x)
    ∂volume

/-- Compact-test pairing with the corresponding mixed
`first-spatial / first-temporal` selected derivative. -/
noncomputable def h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (r : ℝ) :
    ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q j)
                y)
            r)
        x)
    ∂volume

/-- A selected first-jet compact-test pairing is the negative zeroth-order
selected pairing against the differentiated compact test. -/
theorem h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal_eq_neg_derivativeTest
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (r : ℝ) :
    h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
        hNS ht hE hTail φ j a r
      =
    -
    h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
      hNS ht hE hTail
      (h3WeakTestFunctionSpatialDerivative a φ)
      j r := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hC1 :
      SpatialC1
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W r j)) := by
    unfold SpatialC1
    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        (W r j)

  dsimp only [
    h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal,
    h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal,
    W
  ]

  exact
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hC1 a φ

/-- At a strict positive selected time, the mixed first-jet temporal pairing is
the negative zeroth-order temporal pairing against the differentiated test. -/
theorem h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal_eq_neg_derivativeTest
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
    (a : PrimeTensor.Axis Depth.three) :
    h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
        hNS ht hE hTail φ j a s
      =
    -
    h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
      hNS ht hE hTail
      (h3WeakTestFunctionSpatialDerivative a φ)
      j s := by
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

  have hTemporalC1 :
      SpatialC1
        (fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q j)
                y)
            s) := by
    unfold SpatialC1

    dsimp only [W, h3PreterminalTailCanonicalSelectedRestart]

    simpa only [U₀, hA, hU₀, temporal_d] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_timeDerivative_spatial_contDiff_one
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        hs.1
        hsR
        j

  dsimp only [
    h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal,
    h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal,
    W
  ]

  exact
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hTemporalC1 a φ

/--
Every compact scalar test sees the correct time derivative of every selected
first spatial jet.

The proof contains no new parametric-integral argument: spatial integration by
parts reduces the path to the already-closed order-zero selected weak pairing,
and a second integration by parts identifies its derivative coefficient.
-/
theorem h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal_hasDerivAt
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
    (a : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
        hNS ht hE hTail φ j a)
      (h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
        hNS ht hE hTail φ j a s)
      s := by
  let dφ : H3WeakTestFunction :=
    h3WeakTestFunctionSpatialDerivative a φ

  let Φ : H3WeakTestVector :=
    fun _ : Fin 3 => dφ

  have hBase :
      HasDerivAt
        (h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
          hNS ht hE hTail dφ j)
        (h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
          hNS ht hE hTail dφ j s)
        s := by
    have h :=
      h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal_hasDerivAt
        hNS ht htau hE hTail htauR hs Φ j

    simpa only [Φ, dφ] using h

  have hNeg :
      HasDerivAt
        (fun r : ℝ =>
          -
          h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
            hNS ht hE hTail dφ j r)
        (-
          h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
            hNS ht hE hTail dφ j s)
        s :=
    hBase.neg

  have hPath :
      h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
          hNS ht hE hTail φ j a
        =
      (fun r : ℝ =>
        -
        h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
          hNS ht hE hTail dφ j r) := by
    funext r

    simpa only [dφ] using
      h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal_eq_neg_derivativeTest
        hNS ht hE hTail φ j a r

  have hCoefficient :
      -
        h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
          hNS ht hE hTail dφ j s
        =
      h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
        hNS ht hE hTail φ j a s := by
    simpa only [dφ] using
      (h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal_eq_neg_derivativeTest
        hNS ht htau hE hTail htauR hs φ j a).symm

  rw [hPath]

  exact
    hNeg.congr_deriv hCoefficient

end

end Euclidean
end Bridge
end PrimeTensor
