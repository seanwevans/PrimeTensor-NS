import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Vector.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.RHS.Hilbert
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family

/-!
# Reduce selected--old weak FTC to the selected branch

The endpoint-independent old branch already has the exact weak FTC

    <Φ, O(q) - O(0)>
      =
    ∫₀^q <Φ, R_old(r)> dr

for divergence-free compact tests, under the existing product-integrability
input.  The selected branch is smooth, but its matching Hilbert weak FTC has not
yet been packaged in the weak--strong chain.

This file performs the bookkeeping needed to isolate that one remaining
temporal task.

First, the literal old compact-test increment used by the zeroth-order weak FTC
is identified exactly with the Hilbert pairing against the genuine old physical
`L²` velocity increment.

Second, the selected physical velocity increment and selected projected-RHS
ambient-real extension are packaged.

Finally, using the already-proved zero initial selected--old difference,

    D(0) = 0,

we prove

    D(q)
      =
    [S(q) - S(0)] - [O(q) - O(0)].

Therefore:

    selected weak FTC
      + old endpoint-independent weak FTC
      =>
    <Φ, D(q)>
      =
    ∫₀^q <Φ, R_sel(r)> dr
      -
    ∫₀^q <Φ, R_old(r)> dr.

No strong old `L²` derivative and no endpoint continuity is used.  The next
increment can focus solely on proving the selected weak FTC and then combining
the two scalar integrals into the selected-minus-old RHS integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakFTCReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Selected physical `L²` velocity increment from elapsed zero to `q`. -/
noncomputable def h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail (q : ℝ)
    -
  h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail 0

/-- Ambient-real selected projected RHS on one elapsed interval. -/
noncomputable def h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (r : ℝ) :
    H3PhysicalRealFinVectorL2Hilbert :=
  if hr : r ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR ⟨r, hr⟩)
  else
    0

@[simp]
theorem h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR r
      =
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR ⟨r, hr⟩) := by
  simp only [
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed,
    dite_eq_left hr
  ]

/-- Exact selected weak-FTC frontier in the native physical Hilbert language.

This is branch-local and places no requirement on the old path. -/
def H3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ q : Set.Icc (0 : ℝ) tau,
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
            hNS ht htau hE hTail q)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR r)

/-- The Hilbert pairing with the genuine old physical velocity increment is
exactly the literal compact-test increment occurring in the endpoint-independent
old weak FTC. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_loggedPairingDifference
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + (q : ℝ)) (h3AxisOfFin3 i) x
            -
           loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume := by
  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, le_rfl, htau.le⟩

  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo
      hNS ht htau hEnd hTail φ q
  ]

  unfold h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
  rw [← Finset.sum_sub_distrib]

  apply Finset.sum_congr rfl
  intro i hi

  let Φ : H3ScalarL2 :=
    h3WeakTestFunctionPhysicalL2 (φ i)

  let Vq : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot0 i) q

  let V0 : H3ScalarL2 :=
    h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail (h3JetSlot0 i) q0

  have hΦ :
      (Φ : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (φ i : Point3 → ℝ) := by
    dsimp only [Φ]
    exact h3WeakTestFunctionPhysicalL2_ae (φ i)

  have hVq :
      (Vq : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    dsimp only [Vq]
    exact
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_loggedVelocityComponent
        hNS ht hEnd hTail q i

  have hV0 :
      (V0 : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        t
        (h3AxisOfFin3 i) := by
    have h :=
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_loggedVelocityComponent
        hNS ht hEnd hTail q0 i

    simpa only [q0, add_zero] using h

  have hIntQ :
      Integrable
        (fun x : Point3 =>
          inner ℝ (Φ x) (Vq x))
        (volume : Measure Point3) :=
    MeasureTheory.L2.integrable_inner Φ Vq

  have hInt0 :
      Integrable
        (fun x : Point3 =>
          inner ℝ (Φ x) (V0 x))
        (volume : Measure Point3) :=
    MeasureTheory.L2.integrable_inner Φ V0

  change
    inner ℝ Φ Vq - inner ℝ Φ V0
      =
    ∫ x : Point3,
      (φ i x) *
        (loggedVelocityComponent
            u (t + (q : ℝ)) (h3AxisOfFin3 i) x
          -
         loggedVelocityComponent
            u t (h3AxisOfFin3 i) x)
      ∂volume

  rw [MeasureTheory.L2.inner_def]
  rw [MeasureTheory.L2.inner_def]
  rw [← integral_sub hIntQ hInt0]

  apply integral_congr_ae
  filter_upwards [hΦ, hVq, hV0] with x hxΦ hxQ hx0

  rw [hxΦ, hxQ, hx0]

  simp [RCLike.inner_apply]
  ring

/-- Endpoint-independent old weak FTC, rewritten entirely in the native
physical Hilbert language. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_projectedRHSHilbert_intervalIntegral_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t (q : ℝ) φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
      =
    ∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r) := by
  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_loggedPairingDifference
      hNS ht htau hEnd hTail φ q
  ]

  exact
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHSHilbert_intervalIntegral_of_productIntegrable
      hNS ht hEnd hTail φ hφ q.property hProd

/-- The actual selected-minus-old difference is the selected increment minus the
old increment, because the canonical restart starts with zero physical
difference. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_selectedIncrement_sub_oldIncrement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q
      =
    h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
        hNS ht htau hE hTail q
      -
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q := by
  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, le_rfl, htau.le⟩

  let S0 : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail 0

  let O0 : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q0

  have hZero :
      S0 - O0 = 0 := by
    simpa only [
      S0,
      O0,
      q0,
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
    ] using
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_zero
        (one_pos : (0 : ℝ) < 1)
        hNS ht htau hEnd hE hTail

  have hInitial :
      S0 = O0 :=
    sub_eq_zero.mp hZero

  unfold
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
    h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo

  change
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)
        -
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q
      =
    (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)
        -
      S0)
      -
    (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q
        -
      O0)

  rw [hInitial]
  abel

/-- Once the selected branch weak FTC is supplied, the already-existing
endpoint-independent old weak FTC gives the complete selected-minus-old weak
evolution identity, with the two branch RHS integrals kept separated.

This theorem exposes no strong old derivative. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_selectedIntegral_sub_oldIntegral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hSelectedFTC :
      H3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
        hNS ht htau hE hTail htauR)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau)
    (hOldProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t (q : ℝ) φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
      =
    (∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR r))
      -
    (∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r)) := by
  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_selectedIncrement_sub_oldIncrement
      hNS ht htau hEnd hE hTail q,
    inner_sub_right,
    hSelectedFTC φ hφ q,
    inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_projectedRHSHilbert_intervalIntegral_of_productIntegrable
      hNS ht htau hEnd hTail φ hφ q hOldProd
  ]

end

end Euclidean
end Bridge
end PrimeTensor
