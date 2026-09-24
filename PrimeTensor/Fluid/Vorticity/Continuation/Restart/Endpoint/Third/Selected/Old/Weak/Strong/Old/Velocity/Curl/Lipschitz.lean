import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Curl.Test.Density
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure

/-!
# Endpoint-independent old physical L² velocity increment bound from curl tests

The pressure-free vorticity route now supplies two complementary facts:

* every elementary curl test satisfies the exact old weak evolution identity
  against the endpoint-independent projected RHS;
* the closed Hilbert span of those three curl-test families is exactly the
  physical Leray-fixed subspace.

This file turns those facts into a strong physical `L²` estimate.

For one target `q`, first package the vectors `Φ` satisfying

    <Φ, U(q)-U(0)> = ∫₀^q <Φ, R_old(r)> dr

together with the scalar interval-integrability needed for linearity.  This is
a real submodule.  The integrated curl theorem puts every elementary curl
generator in it, hence the entire algebraic curl span.

The old projected RHS has the already-proved uniform Hilbert bound

    ‖R_old(r)‖ ≤ 3 C(E).

Therefore every `Φ` in the curl span obeys

    |<Φ, U(q)-U(0)>|
      ≤ 3 ‖Φ‖ C(E) q.

The estimate defines a closed set, so it extends to the closed curl span.
The curl-density theorem identifies that closure with the physical Leray-fixed
submodule.  Since the old velocity increment itself is Leray-fixed, testing it
against itself yields

    ‖U(q)-U(0)‖ ≤ 3 C(E) q.

No endpoint continuity, pressure estimate, old strong time derivative, or
Hilbert-valued Bochner integrability of the old RHS is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVelocityCurlLipschitz
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact scalar old evolution property for one arbitrary physical Hilbert
test vector at target `q`.  Interval integrability is included so the property
is stable under real linear combinations. -/
def H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (Φ : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  IntervalIntegrable
      (fun r : ℝ =>
        inner ℝ
          Φ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
      volume
      (0 : ℝ)
      (q : ℝ)
    ∧
  inner ℝ
      Φ
      (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q)
    =
  ∫ r in (0 : ℝ)..(q : ℝ),
    inner ℝ
      Φ
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
        hNS ht hEnd hTail r)

/-- The exact integrated old pairing property at fixed target `q` is a real
linear submodule of the physical Hilbert space. -/
noncomputable def h3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingSubmoduleTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    Submodule ℝ H3PhysicalRealFinVectorL2Hilbert where
  carrier :=
    { Φ |
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
        hNS ht htau hEnd hTail q Φ }
  zero_mem' := by
    unfold
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
    constructor <;> simp
  add_mem' := by
    intro Φ Ψ hΦ hΨ
    unfold
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
      at hΦ hΨ ⊢

    rcases hΦ with ⟨hΦInt, hΦEq⟩
    rcases hΨ with ⟨hΨInt, hΨEq⟩

    constructor
    · simpa only [inner_add_left] using hΦInt.add hΨInt
    · calc
        inner ℝ
            (Φ + Ψ)
            (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q)
            =
          inner ℝ
              Φ
              (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
                hNS ht htau hEnd hTail q)
            +
          inner ℝ
              Ψ
              (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
                hNS ht htau hEnd hTail q) := by
            rw [inner_add_left]
        _ =
          (∫ r in (0 : ℝ)..(q : ℝ),
            inner ℝ
              Φ
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r))
            +
          (∫ r in (0 : ℝ)..(q : ℝ),
            inner ℝ
              Ψ
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r)) := by
            rw [hΦEq, hΨEq]
        _ =
          ∫ r in (0 : ℝ)..(q : ℝ),
            (
              inner ℝ
                Φ
                (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                  hNS ht hEnd hTail r)
                +
              inner ℝ
                Ψ
                (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                  hNS ht hEnd hTail r)
            ) := by
              exact
                (intervalIntegral.integral_add
                  hΦInt hΨInt).symm
        _ =
          ∫ r in (0 : ℝ)..(q : ℝ),
            inner ℝ
              (Φ + Ψ)
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r) := by
              apply intervalIntegral.integral_congr
              intro r _hr
              change
                inner ℝ
                    Φ
                    (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                      hNS ht hEnd hTail r)
                  +
                inner ℝ
                    Ψ
                    (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                      hNS ht hEnd hTail r)
                  =
                inner ℝ
                    (Φ + Ψ)
                    (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                      hNS ht hEnd hTail r)
              rw [inner_add_left]
  smul_mem' := by
    intro c Φ hΦ
    unfold
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
      at hΦ ⊢

    rcases hΦ with ⟨hΦInt, hΦEq⟩

    constructor
    · let f : ℝ → ℝ :=
        fun r : ℝ =>
          inner ℝ
            Φ
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r)

      have hEq :
          (fun r : ℝ =>
            inner ℝ
              (c • Φ)
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r))
            =
          c • f := by
        funext r
        dsimp only [f]
        simp only [
          Pi.smul_apply,
          smul_eq_mul,
          real_inner_smul_left
        ]

      rw [hEq]

      exact hΦInt.smul c
    · calc
        inner ℝ
            (c • Φ)
            (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q)
            =
          c *
          inner ℝ
            Φ
            (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q) := by
            rw [real_inner_smul_left]
        _ =
          c *
          (∫ r in (0 : ℝ)..(q : ℝ),
            inner ℝ
              Φ
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r)) := by
            rw [hΦEq]
        _ =
          ∫ r in (0 : ℝ)..(q : ℝ),
            c *
            inner ℝ
              Φ
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r) := by
              simpa only [smul_eq_mul] using
                (intervalIntegral.integral_smul
                  c
                  (fun r : ℝ =>
                    inner ℝ
                      Φ
                      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                        hNS ht hEnd hTail r))).symm
        _ =
          ∫ r in (0 : ℝ)..(q : ℝ),
            inner ℝ
              (c • Φ)
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r) := by
              apply intervalIntegral.integral_congr
              intro r _hr
              change
                c *
                    inner ℝ
                      Φ
                      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                        hNS ht hEnd hTail r)
                  =
                inner ℝ
                    (c • Φ)
                    (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                      hNS ht hEnd hTail r)
              rw [real_inner_smul_left]

/-- Every elementary curl-test generator satisfies the exact integrated old
projected-RHS pairing property. -/
theorem h3CurlWeakTestPhysicalL2Set_subset_oldProjectedRHSIntegratedPairingSubmoduleTo
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
    h3CurlWeakTestPhysicalL2Set
      ⊆
    (h3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingSubmoduleTo
      hNS ht htau hEnd hTail q :
      Set H3PhysicalRealFinVectorL2Hilbert) := by
  intro Φ hΦ

  have hCurl :=
    h3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedZeroProjectedRHSOnElapsed_tailH3_weakStrong
      hNS ht htau hEnd hE hTail

  rcases hΦ with ⟨ψ, h01 | h02 | h12⟩

  · subst Φ
    change
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
        hNS ht htau hEnd hTail q
        (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ))

    unfold
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo

    constructor
    · exact
        intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
          hNS ht hEnd hE hTail
          (h3WeakTestCurl01 ψ)
          (h3WeakTestCurl01_divergenceFree ψ)
          q
    · rw [
        inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo
          hNS ht htau hEnd hTail
          (h3WeakTestCurl01 ψ) q
      ]
      simpa only using (hCurl ψ q).1

  · subst Φ
    change
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
        hNS ht htau hEnd hTail q
        (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))

    unfold
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo

    constructor
    · exact
        intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
          hNS ht hEnd hE hTail
          (h3WeakTestCurl02 ψ)
          (h3WeakTestCurl02_divergenceFree ψ)
          q
    · rw [
        inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo
          hNS ht htau hEnd hTail
          (h3WeakTestCurl02 ψ) q
      ]
      simpa only using (hCurl ψ q).2.1

  · subst Φ
    change
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
        hNS ht htau hEnd hTail q
        (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ))

    unfold
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo

    constructor
    · exact
        intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
          hNS ht hEnd hE hTail
          (h3WeakTestCurl12 ψ)
          (h3WeakTestCurl12_divergenceFree ψ)
          q
    · rw [
        inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo
          hNS ht htau hEnd hTail
          (h3WeakTestCurl12 ψ) q
      ]
      simpa only using (hCurl ψ q).2.2

/-- Hence every vector in the algebraic curl-test span satisfies the exact
integrated old pairing identity. -/
theorem h3CurlWeakTestPhysicalL2Span_le_oldProjectedRHSIntegratedPairingSubmoduleTo
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
    h3CurlWeakTestPhysicalL2Span
      ≤
    h3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingSubmoduleTo
      hNS ht htau hEnd hTail q := by
  unfold h3CurlWeakTestPhysicalL2Span

  apply Submodule.span_le.mpr

  exact
    h3CurlWeakTestPhysicalL2Set_subset_oldProjectedRHSIntegratedPairingSubmoduleTo
      hNS ht htau hEnd hE hTail q

/-- Quantitative old velocity-increment pairing bound on the algebraic
curl-test span. -/
theorem norm_inner_velocityIncrementTo_le_of_mem_curlWeakTestSpan_tailH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ : Φ ∈ h3CurlWeakTestPhysicalL2Span) :
    ‖inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)‖
      ≤
    ((3 * ‖Φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    (q : ℝ) := by
  have hIntegrated :
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
        hNS ht htau hEnd hTail q Φ := by
    exact
      (h3CurlWeakTestPhysicalL2Span_le_oldProjectedRHSIntegratedPairingSubmoduleTo
        hNS ht htau hEnd hE hTail q)
        hΦ

  rcases hIntegrated with ⟨_hInt, hEq⟩

  have hPointwise :
      ∀ᵐ r : ℝ ∂volume,
        r ∈ Set.uIoc (0 : ℝ) (q : ℝ) →
          ‖inner ℝ
              Φ
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail r)‖
            ≤
          ‖Φ‖
            *
          (3 * h3UnitViscosityZeroRHSBound E) := by
    filter_upwards with r
    intro hr

    rw [Set.uIoc_of_le q.property.1] at hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨
        hr.1.le,
        hr.2.trans q.property.2
      ⟩

    rw [
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
        hNS ht hEnd hTail hrTau
    ]

    calc
      ‖inner ℝ
          Φ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail ⟨r, hrTau⟩)‖
          ≤
        ‖Φ‖ *
        ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail ⟨r, hrTau⟩‖ :=
        norm_inner_le_norm _ _
      _ ≤
        ‖Φ‖ *
        (3 * h3UnitViscosityZeroRHSBound E) := by
          exact
            mul_le_mul_of_nonneg_left
              (norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_le_three_mul
                hNS ht hEnd hE hTail ⟨r, hrTau⟩)
              (norm_nonneg Φ)

  have hBound0 :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae
      hPointwise

  have hBound :
      ‖∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          Φ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r)‖
        ≤
      (‖Φ‖ * (3 * h3UnitViscosityZeroRHSBound E))
        *
      (q : ℝ) := by
    simpa only [
      sub_zero,
      abs_of_nonneg q.property.1
    ] using hBound0

  calc
    ‖inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)‖
        =
      ‖∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          Φ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r)‖ := by
          rw [hEq]
    _ ≤
      (‖Φ‖ * (3 * h3UnitViscosityZeroRHSBound E))
        *
      (q : ℝ) :=
      hBound
    _ =
      ((3 * ‖Φ‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ) := by
      ring

/-- The same quantitative pairing bound extends to the complete closed
curl-test span. -/
theorem norm_inner_velocityIncrementTo_le_of_mem_curlWeakTestClosedSpan_tailH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ : Φ ∈ h3CurlWeakTestPhysicalL2ClosedSpan) :
    ‖inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)‖
      ≤
    ((3 * ‖Φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    (q : ℝ) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
      hNS ht htau hEnd hTail q

  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    { Ψ |
      ‖inner ℝ Ψ V‖
        ≤
      ((3 * ‖Ψ‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ) }

  have hClosed : IsClosed S := by
    dsimp only [S]

    exact
      isClosed_le
        ((continuous_id.inner continuous_const).norm)
        (((continuous_const.mul continuous_norm).mul continuous_const).mul
          continuous_const)

  have hSpanSubset :
      (h3CurlWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S := by
    intro Ψ hΨ

    dsimp only [S, V]

    exact
      norm_inner_velocityIncrementTo_le_of_mem_curlWeakTestSpan_tailH3
        hNS ht htau hEnd hE hTail q Ψ hΨ

  have hClosureSubset :
      closure
          (h3CurlWeakTestPhysicalL2Span :
            Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S :=
    closure_minimal hSpanSubset hClosed

  have hΦClosure :
      Φ ∈
      closure
        (h3CurlWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert) := by
    unfold h3CurlWeakTestPhysicalL2ClosedSpan at hΦ
    change
      Φ ∈
      closure
        (h3CurlWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
      at hΦ
    exact hΦ

  have hResult :=
    hClosureSubset hΦClosure

  dsimp only [S, V] at hResult
  exact hResult

/-- The old physical velocity increment is Lipschitz from elapsed zero, directly
from the canonical H³ tail and the pressure-free curl identities. -/
theorem norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_le_tailH3_curl
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
    ‖h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q‖
      ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    (q : ℝ) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
      hNS ht htau hEnd hTail q

  have hLeray :
      V ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
    dsimp only [V]

    exact
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
        hNS ht htau hEnd hTail q

  have hClosed :
      V ∈ h3CurlWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3CurlWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]
    exact hLeray

  have hPair :=
    norm_inner_velocityIncrementTo_le_of_mem_curlWeakTestClosedSpan_tailH3
      hNS ht htau hEnd hE hTail
      q V hClosed

  have hPairSelf :
      ‖inner ℝ V V‖
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ) := by
    change
      ‖inner ℝ
          V
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q)‖
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ)

    exact hPair

  have hSq :
      ‖V‖ ^ 2
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ) := by
    simpa only [
      real_inner_self_eq_norm_sq,
      Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖V‖)
    ] using hPairSelf

  have hRHSNonneg :
      0 ≤ h3UnitViscosityZeroRHSBound E :=
    h3UnitViscosityZeroRHSBound_nonneg hE

  have hqNonneg :
      0 ≤ (q : ℝ) :=
    q.property.1

  have hFinal :
      ‖V‖
        ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ) := by
    by_cases hV : ‖V‖ = 0

    · rw [hV]
      exact
        mul_nonneg
          (mul_nonneg (by norm_num) hRHSNonneg)
          hqNonneg

    · have hVPos : 0 < ‖V‖ := by
        exact
          lt_of_le_of_ne
            (norm_nonneg V)
            (Ne.symm hV)

      nlinarith [hSq]

  simpa only [V] using hFinal

end

end Euclidean
end Bridge
end PrimeTensor
