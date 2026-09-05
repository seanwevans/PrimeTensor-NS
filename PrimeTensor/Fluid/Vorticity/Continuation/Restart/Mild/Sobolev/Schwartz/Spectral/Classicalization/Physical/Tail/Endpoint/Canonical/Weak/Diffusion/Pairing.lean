import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Velocity.Pairing.Continuity
import PrimeTensor.Bridge.Euclidean.Curl.Laplacian.X

/-!
# Classicalization: move endpoint diffusion onto the weak test function

The endpoint projected `L²` right-hand side contains the physical Laplacian.
The reduced endpoint continuity hypothesis, however, assumes strong `L²`
continuity only for the zeroth and ordered third H³ jet slots, not for the
second-order slots appearing directly in the Laplacian package.

For weak evolution this is unnecessary.  Against a compactly supported smooth
test function, two spatial integrations by parts give

    ∫ φ ∂ₖ∂ₖ f = ∫ (∂ₖ∂ₖ φ) f.

The right-hand side depends only on the zeroth-order `L²` velocity coordinate.

This file packages that observation in three layers:

* bundled first and second coordinate derivatives of `H3WeakTestFunction`;
* a generic `SpatialC2` double integration-by-parts theorem;
* an endpoint weak diffusion pairing represented entirely by zeroth-order
  physical `L²` velocity slots, hence continuous in elapsed time from the
  existing endpoint hypothesis.

No second-jet time continuity, time derivative, pressure transform, or
fixed-frequency evaluation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakDiffusionPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakDiffusionPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Bundled coordinate derivative of a compactly supported smooth scalar test
function. -/
noncomputable def h3WeakTestFunctionSpatialDerivative
    (a : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    H3WeakTestFunction :=
  (TestFunction.lineDerivCLM
    ℝ
    (axisDirection a) :
      H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
    φ

/-- Bundled pure second coordinate derivative of a compactly supported smooth
scalar test function. -/
noncomputable def h3WeakTestFunctionSecondSpatialDerivative
    (a : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    H3WeakTestFunction :=
  h3WeakTestFunctionSpatialDerivative
    a
    (h3WeakTestFunctionSpatialDerivative a φ)

/-- One spatial integration by parts, extracted from the ordinary-distribution
bridge proved for the pressure defect.

Compact support of the test function means only local integrability of `q` is
needed. -/
theorem h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
    {q : ScalarField3}
    (hq : SpatialC1 q)
    (a : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d a q x)
      ∂volume)
      =
    -
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3WeakTestFunctionSpatialDerivative a φ) x)
        (q x)
      ∂volume := by
  let dφ : H3WeakTestFunction :=
    h3WeakTestFunctionSpatialDerivative a φ

  have hDist :=
    h3WeakDistributionOfFun_lineDeriv_apply_eq_integral_spatial3_d
      hq a φ

  have hqLocalOn :
      LocallyIntegrableOn
        q
        Set.univ
        (volume : Measure Point3) :=
    hq.continuous.locallyIntegrable.locallyIntegrableOn Set.univ

  have hEval :
      h3WeakDistributionOfFun q dφ
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (dφ x)
          (q x)
        ∂volume := by
    unfold h3WeakDistributionOfFun
    exact
      TestFunction.integralAgainstBilinCLM_eq_integral
        hqLocalOn

  rw [Distribution.lineDerivCLM_apply] at hDist

  have hDist' :
      -
        h3WeakDistributionOfFun q dφ
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (spatial3.d a q x)
        ∂volume := by
    simpa only [
      dφ,
      h3WeakTestFunctionSpatialDerivative
    ] using hDist

  rw [hEval] at hDist'

  exact hDist'.symm

/-- Two spatial integrations by parts move a pure second derivative completely
from a `C²` scalar field onto a compactly supported smooth test function. -/
theorem h3SpatialC2_test_pairing_secondSpatialDerivative_eq_testSecondDerivative_pairing
    {q : ScalarField3}
    (hq : SpatialC2 q)
    (a : PrimeTensor.Axis Depth.three)
    (φ : H3WeakTestFunction) :
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d
          a
          (spatial3.d a q)
          x)
      ∂volume)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3WeakTestFunctionSecondSpatialDerivative a φ) x)
        (q x)
      ∂volume := by
  have hq1 :
      SpatialC1 q :=
    hq.of_le (by norm_num)

  have hdq1 :
      SpatialC1 (spatial3.d a q) := by
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hq a

  have hFirst :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hdq1 a φ

  have hSecond :=
    h3SpatialC1_test_pairing_spatial3_d_eq_neg_testDerivative_pairing
      hq1
      a
      (h3WeakTestFunctionSpatialDerivative a φ)

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d
          a
          (spatial3.d a q)
          x)
      ∂volume)
        =
      -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3WeakTestFunctionSpatialDerivative a φ) x)
          (spatial3.d a q x)
        ∂volume := by
          exact hFirst
    _ =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          ((h3WeakTestFunctionSecondSpatialDerivative a φ) x)
          (q x)
        ∂volume := by
          rw [hSecond]
          simp [h3WeakTestFunctionSecondSpatialDerivative]

/-- Coordinatewise Hilbert-space realization of a compact test pairing with one
zeroth-order endpoint velocity component. -/
theorem h3WeakTestFunctionPhysicalL2_inner_preterminalSlot0_eq_integral_normalizedRealPath
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 ψ)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 i) q)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        ((h3SpectralRealVelocityOfPath W (q : ℝ) x).component
          (h3AxisOfFin3 i))
      ∂volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let Φ : H3ScalarL2 :=
    h3WeakTestFunctionPhysicalL2 ψ

  let V : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot0 i) q

  have hΦ :
      (Φ : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (ψ : Point3 → ℝ) := by
    dsimp only [Φ]
    exact h3WeakTestFunctionPhysicalL2_ae ψ

  have hV :
      (V : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    dsimp only [V]
    exact
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_loggedVelocityComponent
        hNS ht hEnd hTail q i

  have hW :
      (fun x : Point3 =>
        (h3SpectralRealVelocityOfPath W (q : ℝ) x).component
          (h3AxisOfFin3 i))
        =
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    dsimp only [W]
    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        (q : ℝ) q.property i

  change
    inner ℝ Φ V
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        ((h3SpectralRealVelocityOfPath W (q : ℝ) x).component
          (h3AxisOfFin3 i))
      ∂volume

  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [hΦ, hV] with x hxΦ hxV

  have hxW :
      (h3SpectralRealVelocityOfPath W (q : ℝ) x).component
          (h3AxisOfFin3 i)
        =
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i)
        x :=
    congrFun hW x

  rw [hxΦ, hxV, ← hxW]

  simpa [mul_comm]

/-- On a genuine physical endpoint slice, each pure second derivative can be
moved onto the compact test function. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_secondSpatialDerivative_weakTransfer
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i k : Fin 3)
    (φ : H3WeakTestFunction) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W s y).component
                (h3AxisOfFin3 i)))
          x)
      ∂volume)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 k) φ) x)
        ((h3SpectralRealVelocityOfPath W s x).component
          (h3AxisOfFin3 i))
      ∂volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let f : ScalarField3 :=
    fun y : Point3 =>
      (h3SpectralRealVelocityOfPath W s y).component
        (h3AxisOfFin3 i)

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hs⟩

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hOldC3 :
      SpatialC3
        (loggedVelocityComponent
          u
          (t + s)
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent
    exact
      hPDE.regularity.velocity_spatial_three
        (t + s)
        hAbs
        (h3AxisOfFin3 i)

  have hOldEq :
      f
        =
      loggedVelocityComponent
        u
        (t + s)
        (h3AxisOfFin3 i) := by
    dsimp only [f, W]
    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        s hs i

  have hfC2 :
      SpatialC2 f := by
    rw [hOldEq]
    exact hOldC3.of_le (by norm_num)

  simpa only [f] using
    h3SpatialC2_test_pairing_secondSpatialDerivative_eq_testSecondDerivative_pairing
      hfC2
      (h3AxisOfFin3 k)
      φ

/-- Weak diffusion pairing on the closed elapsed interval, written entirely
with twice-differentiated compact test functions and zeroth-order physical
`L²` velocity slots. -/
noncomputable def h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  ∑ i : Fin 3,
    ∑ k : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSecondSpatialDerivative
            (h3AxisOfFin3 k)
            (φ i)))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 i) q)

/-- The weak diffusion pairing is continuous in elapsed time using only the
zeroth-order endpoint `L²` continuity hypothesis. -/
theorem continuous_h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector) :
    Continuous
      (h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
        hNS ht hEnd hTail φ) := by
  unfold h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed

  apply continuous_finsetSum
  intro i hi

  apply continuous_finsetSum
  intro k hk

  exact
    continuous_const.inner
      (hEndpoint i).1

/-- The continuous Hilbert-space weak diffusion pairing is exactly the literal
pairing with the endpoint reconstructed Laplacian, written as the finite sum of
pure second-derivative integrals. -/
theorem h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed_eq_endpointSecondDerivativeIntegrals
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
        hNS ht hEnd hTail φ q
      =
    ∑ i : Fin 3,
      ∑ k : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (fun y : Point3 =>
                  (h3SpectralRealVelocityOfPath W (q : ℝ) y).component
                    (h3AxisOfFin3 i)))
              x)
          ∂volume := by
  dsimp only

  unfold h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed

  apply Finset.sum_congr rfl
  intro i hi

  apply Finset.sum_congr rfl
  intro k hk

  have hInner :=
    h3WeakTestFunctionPhysicalL2_inner_preterminalSlot0_eq_integral_normalizedRealPath
      hNS ht htau hEnd hE hTail hEndpoint
      (h3WeakTestFunctionSecondSpatialDerivative
        (h3AxisOfFin3 k)
        (φ i))
      q
      i

  have hTransfer :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_secondSpatialDerivative_weakTransfer
      hNS ht htau hEnd hE hTail hEndpoint
      (q : ℝ)
      q.property
      i k
      (φ i)

  exact hInner.trans hTransfer.symm

end

end Euclidean
end Bridge
end PrimeTensor
