import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldVelocityWeakPairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Diffusion.Pairing

/-!
# Pressure-free continuity of old third-order weak pairings

`OldVelocityWeakPairing` proved continuity of

    q ↦ ∫ ψ(x) u_j(t+q,x) dx

directly from pointwise temporal continuity and the retained H³ envelope.

For the ordered third H³ jet we do not need temporal continuity of spatial
derivatives.  Three spatial integrations by parts move

    ∂ᵢ ∂ₖ ∂ₗ uⱼ

entirely onto the fixed compact smooth test:

    ∫ ψ ∂ᵢ∂ₖ∂ₗ uⱼ
      = - ∫ (∂ₗ∂ₖ∂ᵢ ψ) uⱼ.

The right-hand side is exactly one of the already-continuous zeroth-order weak
velocity pairings.  This closes compact-test continuity for every ordered
third derivative without pressure, temporal derivative integrability, endpoint
continuity, or a mild equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldThirdWeakPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldThirdWeakPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Ordered third coordinate derivative of a compact smooth scalar test.

The order is the one produced by successively integrating
`∂ₐ ∂ᵦ ∂𝚌 q` by parts: first `a`, then `b`, then `c`. -/
noncomputable def h3WeakTestFunctionThirdSpatialDerivative
    (a b c : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    H3WeakTestFunction :=
  h3WeakTestFunctionSpatialDerivative
    c
    (h3WeakTestFunctionSpatialDerivative
      b
      (h3WeakTestFunctionSpatialDerivative a φ))

/-- Three spatial integrations by parts for an arbitrary ordered third
coordinate derivative. -/
theorem h3SpatialC3_test_pairing_thirdSpatialDerivative_eq_neg_testThirdDerivative_pairing
    {q : ScalarField3}
    (hq : SpatialC3 q)
    (a b c : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d c q))
          x)
      ∂volume)
      =
    -
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3WeakTestFunctionThirdSpatialDerivative a b c φ) x)
        (q x)
      ∂volume := by
  have hdc2 :
      SpatialC2 (spatial3.d c q) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hq c

  have hdbc1 :
      SpatialC1
        (spatial3.d b (spatial3.d c q)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hdc2 b

  have hdc1 :
      SpatialC1 (spatial3.d c q) :=
    hdc2.of_le (by norm_num)

  have hq1 :
      SpatialC1 q :=
    hq.of_le (by norm_num)

  have hFirst :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hdbc1
      a
      φ

  have hSecond :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hdc1
      b
      (h3WeakTestFunctionSpatialDerivative a φ)

  have hThird :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hq1
      c
      (h3WeakTestFunctionSpatialDerivative
        b
        (h3WeakTestFunctionSpatialDerivative a φ))

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d c q))
          x)
      ∂volume)
        =
      -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3WeakTestFunctionSpatialDerivative a φ) x)
          (spatial3.d
            b
            (spatial3.d c q)
            x)
        ∂volume := by
          exact hFirst
    _ =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3WeakTestFunctionSpatialDerivative
            b
            (h3WeakTestFunctionSpatialDerivative a φ)) x)
          (spatial3.d c q x)
        ∂volume := by
          rw [hSecond]
          ring
    _ =
      -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3WeakTestFunctionThirdSpatialDerivative
            a b c φ) x)
          (q x)
        ∂volume := by
          simpa only [
            h3WeakTestFunctionThirdSpatialDerivative
          ] using hThird

/-- One ordered third derivative of the old preterminal velocity paired against
one compact smooth scalar test. -/
noncomputable def h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (j i k l : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (spatial3.d
        (h3AxisOfFin3 i)
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 l)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j))))
        x)
    ∂volume

/-- Every old ordered-third compact-test pairing is exactly a zeroth-order
velocity pairing with the three derivatives transferred to the test. -/
theorem h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed_eq_neg_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (j i k l : Fin 3)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
        hNS ht hEnd hTail ψ j i k l q
      =
    -
    h3PreterminalOldVelocityWeakScalarPairingOnElapsed
      hNS ht hEnd hTail
      (h3WeakTestFunctionThirdSpatialDerivative
        (h3AxisOfFin3 i)
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 l)
        ψ)
      j q := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hC3 :
      SpatialC3
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 j)) := by
    unfold loggedVelocityComponent
    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hAbs
        (h3AxisOfFin3 j)

  unfold
    h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
    h3PreterminalOldVelocityWeakScalarPairingOnElapsed

  exact
    h3SpatialC3_test_pairing_thirdSpatialDerivative_eq_neg_testThirdDerivative_pairing
      hC3
      (h3AxisOfFin3 i)
      (h3AxisOfFin3 k)
      (h3AxisOfFin3 l)
      ψ

/-- Pressure-free continuity of every ordered-third old velocity weak pairing
on the closed elapsed interval. -/
theorem continuous_h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (j i k l : Fin 3) :
    Continuous
      (h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
        hNS ht hEnd hTail ψ j i k l) := by
  let d3ψ : H3WeakTestFunction :=
    h3WeakTestFunctionThirdSpatialDerivative
      (h3AxisOfFin3 i)
      (h3AxisOfFin3 k)
      (h3AxisOfFin3 l)
      ψ

  have hZero :
      Continuous
        (h3PreterminalOldVelocityWeakScalarPairingOnElapsed
          hNS ht hEnd hTail d3ψ j) :=
    continuous_h3PreterminalOldVelocityWeakScalarPairingOnElapsed
      hNS ht hEnd hE hTail d3ψ j

  have hEq :
      h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed
          hNS ht hEnd hTail ψ j i k l
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        -
        h3PreterminalOldVelocityWeakScalarPairingOnElapsed
          hNS ht hEnd hTail d3ψ j q) := by
    funext q
    dsimp only [d3ψ]
    exact
      h3PreterminalOldVelocityThirdWeakScalarPairingOnElapsed_eq_neg_zero
        hNS ht hEnd hTail ψ j i k l q

  rw [hEq]

  exact hZero.neg

end

end Euclidean
end Bridge
end PrimeTensor
