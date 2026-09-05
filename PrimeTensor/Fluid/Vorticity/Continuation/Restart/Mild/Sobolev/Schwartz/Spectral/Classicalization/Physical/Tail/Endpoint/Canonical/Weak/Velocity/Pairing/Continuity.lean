import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Temporal.Pairing
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Classicalization: continuity of compactly tested endpoint velocity pairings

The previous checkpoint gives the explicit weak derivative pairing

    Σᵢ ∫ φᵢ ∂ₛWᵢ = Σᵢ ∫ φᵢ Rᵢ

at every strict physical elapsed time.

Before differentiating the spatial pairing in time, we isolate its topology.
Each compactly supported smooth scalar test function is itself an `L²(Point3)`
vector.  Pairing it against the zeroth-order physical `L²` velocity coordinate
therefore gives an ordinary Hilbert-space inner product.

The endpoint continuity hypothesis already states strong continuity of exactly
those zeroth-order `L²` coordinates.  Hence the finite vector test pairing is
continuous on the closed elapsed interval.

Finally, the concrete `L²` jet representative theorem together with the
pointwise endpoint/old-velocity identification shows that this Hilbert pairing
is literally

    Σᵢ ∫ φᵢ(x) Wᵢ(s,x) dx.

Thus the next file can differentiate a genuine continuous scalar function,
without mixing the topology argument into the derivative proof.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakVelocityPairingContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakVelocityPairingContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Canonical real `L²(Point3)` class carried by a compactly supported smooth
scalar test function. -/
noncomputable def h3WeakTestFunctionPhysicalL2
    (φ : H3WeakTestFunction) :
    H3ScalarL2 :=
  let hφ :
      MemLp
        (φ : Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  hφ.toLp φ

/-- The `L²` test-function package represents the original test function almost
everywhere. -/
theorem h3WeakTestFunctionPhysicalL2_ae
    (φ : H3WeakTestFunction) :
    ((h3WeakTestFunctionPhysicalL2 φ : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (φ : Point3 → ℝ) := by
  unfold h3WeakTestFunctionPhysicalL2
  dsimp only
  exact
    MemLp.coeFn_toLp
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

/-- Hilbert-space pairing of a compactly supported smooth test vector with the
old physical zeroth-order `L²` velocity coordinates on elapsed time. -/
noncomputable def h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
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
    inner ℝ
      (h3WeakTestFunctionPhysicalL2 (φ i))
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 i) q)

/-- The compactly tested velocity pairing is continuous on the complete closed
elapsed interval.  This uses only the zeroth-order part of the reduced endpoint
`L²` continuity hypothesis. -/
theorem continuous_h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
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
      (h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ) := by
  unfold h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed

  apply continuous_finset_sum
  intro i hi

  exact
    continuous_const.inner
      (hEndpoint i).1

/-- One zeroth-order elapsed `L²` coordinate represents the matching old logged
velocity component almost everywhere. -/
theorem h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_loggedVelocityComponent
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    ((h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail
        (h3JetSlot0 i) q : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    loggedVelocityComponent
      u
      (t + (q : ℝ))
      (h3AxisOfFin3 i) := by
  have h :=
    velocityH3L2JetAt_ae_eq_jetField
      (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)
      (h3JetSlot0 i)

  simpa only [
    h3PreterminalCanonicalL2JetOnElapsed,
    h3JetSlot0,
    velocityH3JetFieldAt
  ] using h

/-- The Hilbert-space elapsed pairing is literally the spatial integral of the
normalized real endpoint velocity against the compact test vector. -/
theorem h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_eq_integral_normalizedRealPath
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
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ q
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3SpectralRealVelocityOfPath W (q : ℝ) x).component
            (h3AxisOfFin3 i))
        ∂volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  unfold h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed

  apply Finset.sum_congr rfl
  intro i hi

  let Φ : H3ScalarL2 :=
    h3WeakTestFunctionPhysicalL2 (φ i)

  let V : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot0 i) q

  have hΦ :
      (Φ : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (φ i : Point3 → ℝ) := by
    dsimp only [Φ]
    exact h3WeakTestFunctionPhysicalL2_ae (φ i)

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
        (φ i x)
        ((h3SpectralRealVelocityOfPath W (q : ℝ) x).component
          (h3AxisOfFin3 i))
      ∂volume

  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [hΦ, hV] with x hxΦ hxV

  change
    inner ℝ (Φ x) (V x)
      =
    (φ i x) *
      (h3SpectralRealVelocityOfPath W (q : ℝ) x).component
        (h3AxisOfFin3 i)

  rw [hxΦ, hxV]

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

  rw [← hxW]
  simpa [mul_comm]

end

end Euclidean
end Bridge
end PrimeTensor
