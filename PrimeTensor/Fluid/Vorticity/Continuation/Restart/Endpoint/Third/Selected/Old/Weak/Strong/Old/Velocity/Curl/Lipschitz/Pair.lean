import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Velocity.Curl.Lipschitz

/-!
# Endpoint-independent arbitrary-pair old physical L² velocity bound

The preceding curl-density argument gives the sharp old physical `L²`
increment estimate only from elapsed zero:

    ‖U(q) - U(0)‖ ≤ 3 C(E) q.

For continuity we need the correct modulus between two arbitrary ordered
elapsed times `r ≤ q`.

No re-anchoring is necessary.  For every vector in the algebraic curl-test
span, the previous integrated-pairing submodule gives both exact identities

    <Φ, U(q)-U(0)> = ∫₀^q <Φ,R_old(s)> ds,
    <Φ, U(r)-U(0)> = ∫₀^r <Φ,R_old(s)> ds.

Subtracting them and using interval-integral additivity gives

    <Φ, U(q)-U(r)> = ∫ᵣ^q <Φ,R_old(s)> ds.

The uniform old projected-RHS Hilbert bound

    ‖R_old(s)‖ ≤ 3 C(E)

therefore yields the correct `(q-r)` pairing modulus.  Closedness extends the
estimate from the algebraic curl span to its closure, which is the whole
physical Leray-fixed subspace.  The velocity difference itself is Leray-fixed,
so self-pairing closes the strong bound

    ‖U(q)-U(r)‖ ≤ 3 C(E) (q-r).

No endpoint continuity, pressure estimate, product-integrability frontier, or
Hilbert-valued old-RHS Bochner integral is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVelocityCurlLipschitzPair
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On the algebraic curl-test span, subtracting the two exact zero-based old
weak evolution identities gives the exact projected-RHS integral over an
arbitrary ordered elapsed interval. -/
theorem inner_velocityIncrementDifference_eq_oldProjectedRHS_intervalIntegral_of_mem_curlWeakTestSpan_tailH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ))
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ : Φ ∈ h3CurlWeakTestPhysicalL2Span) :
    inner ℝ
        Φ
        (
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q
            -
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail r
        )
      =
    ∫ s in (r : ℝ)..(q : ℝ),
      inner ℝ
        Φ
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail s) := by
  let f : ℝ → ℝ :=
    fun s : ℝ =>
      inner ℝ
        Φ
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail s)

  have hQ :
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
        hNS ht htau hEnd hTail q Φ := by
    exact
      (h3CurlWeakTestPhysicalL2Span_le_oldProjectedRHSIntegratedPairingSubmoduleTo
        hNS ht htau hEnd hE hTail q)
        hΦ

  have hR :
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
        hNS ht htau hEnd hTail r Φ := by
    exact
      (h3CurlWeakTestPhysicalL2Span_le_oldProjectedRHSIntegratedPairingSubmoduleTo
        hNS ht htau hEnd hE hTail r)
        hΦ

  unfold
    H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
    at hQ hR

  rcases hQ with ⟨hQInt, hQEq⟩
  rcases hR with ⟨hRInt, hREq⟩

  have hQInt' :
      IntervalIntegrable f volume (0 : ℝ) (q : ℝ) := by
    simpa only [f] using hQInt

  have hRInt' :
      IntervalIntegrable f volume (0 : ℝ) (r : ℝ) := by
    simpa only [f] using hRInt

  have hRQInt :
      IntervalIntegrable f volume (r : ℝ) (q : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hrq]

    have hIntOnQ :
        IntegrableOn f (Set.Ioo (0 : ℝ) (q : ℝ)) volume := by
      exact
        (intervalIntegrable_iff_integrableOn_Ioo_of_le q.property.1).1
          hQInt'

    exact
      hIntOnQ.mono_set
        (by
          intro s hs
          exact
            ⟨
              lt_of_le_of_lt r.property.1 hs.1,
              hs.2
            ⟩)

  have hAdd :
      (∫ s in (0 : ℝ)..(r : ℝ), f s)
        +
      (∫ s in (r : ℝ)..(q : ℝ), f s)
        =
      ∫ s in (0 : ℝ)..(q : ℝ), f s :=
    intervalIntegral.integral_add_adjacent_intervals
      hRInt' hRQInt

  rw [inner_sub_right]

  change
    inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
      -
    inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail r)
      =
    ∫ s in (r : ℝ)..(q : ℝ), f s

  rw [hQEq, hREq]

  change
    (∫ s in (0 : ℝ)..(q : ℝ), f s)
      -
    (∫ s in (0 : ℝ)..(r : ℝ), f s)
      =
    ∫ s in (r : ℝ)..(q : ℝ), f s

  linarith

/-- The arbitrary-interval projected-RHS integral over the algebraic curl span
inherits the uniform old Hilbert RHS bound with the exact interval length. -/
theorem norm_inner_velocityIncrementDifference_le_of_mem_curlWeakTestSpan_tailH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ))
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ : Φ ∈ h3CurlWeakTestPhysicalL2Span) :
    ‖inner ℝ
        Φ
        (
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q
            -
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail r
        )‖
      ≤
    ((3 * ‖Φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  have hEq :=
    inner_velocityIncrementDifference_eq_oldProjectedRHS_intervalIntegral_of_mem_curlWeakTestSpan_tailH3
      hNS ht htau hEnd hE hTail
      r q hrq Φ hΦ

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.uIoc (r : ℝ) (q : ℝ) →
          ‖inner ℝ
              Φ
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail s)‖
            ≤
          ‖Φ‖
            *
          (3 * h3UnitViscosityZeroRHSBound E) := by
    filter_upwards with s
    intro hs

    rw [Set.uIoc_of_le hrq] at hs

    have hsTau :
        s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨
        r.property.1.trans hs.1.le,
        hs.2.trans q.property.2
      ⟩

    rw [
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
        hNS ht hEnd hTail hsTau
    ]

    calc
      ‖inner ℝ
          Φ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail ⟨s, hsTau⟩)‖
          ≤
        ‖Φ‖ *
        ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail ⟨s, hsTau⟩‖ :=
        norm_inner_le_norm _ _
      _ ≤
        ‖Φ‖ *
        (3 * h3UnitViscosityZeroRHSBound E) := by
          exact
            mul_le_mul_of_nonneg_left
              (norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_le_three_mul
                hNS ht hEnd hE hTail ⟨s, hsTau⟩)
              (norm_nonneg Φ)

  have hBound0 :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae
      hPointwise

  have hBound :
      ‖∫ s in (r : ℝ)..(q : ℝ),
        inner ℝ
          Φ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail s)‖
        ≤
      (‖Φ‖ * (3 * h3UnitViscosityZeroRHSBound E))
        *
      ((q : ℝ) - (r : ℝ)) := by
    simpa only [
      abs_of_nonneg (sub_nonneg.mpr hrq)
    ] using hBound0

  calc
    ‖inner ℝ
        Φ
        (
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q
            -
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail r
        )‖
        =
      ‖∫ s in (r : ℝ)..(q : ℝ),
        inner ℝ
          Φ
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail s)‖ := by
          rw [hEq]
    _ ≤
      (‖Φ‖ * (3 * h3UnitViscosityZeroRHSBound E))
        *
      ((q : ℝ) - (r : ℝ)) :=
      hBound
    _ =
      ((3 * ‖Φ‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
      ring

/-- The arbitrary-pair weak estimate extends from the algebraic curl span to
its complete closed Hilbert span. -/
theorem norm_inner_velocityIncrementDifference_le_of_mem_curlWeakTestClosedSpan_tailH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ))
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ : Φ ∈ h3CurlWeakTestPhysicalL2ClosedSpan) :
    ‖inner ℝ
        Φ
        (
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q
            -
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail r
        )‖
      ≤
    ((3 * ‖Φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      -
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail r

  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    { Ψ |
      ‖inner ℝ Ψ V‖
        ≤
      ((3 * ‖Ψ‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) }

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
      norm_inner_velocityIncrementDifference_le_of_mem_curlWeakTestSpan_tailH3
        hNS ht htau hEnd hE hTail
        r q hrq Ψ hΨ

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

/-- Strong endpoint-independent arbitrary-pair physical `L²` estimate for the
old velocity increment path. -/
theorem norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖(
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q
        -
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail r
    )‖ ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      -
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail r

  have hQLeray :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q
        ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
      hNS ht htau hEnd hTail q

  have hRLeray :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail r
        ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
      hNS ht htau hEnd hTail r

  have hLeray :
      V ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
    dsimp only [V]
    exact
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule.sub_mem
        hQLeray hRLeray

  have hClosed :
      V ∈ h3CurlWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3CurlWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]
    exact hLeray

  have hPair :=
    norm_inner_velocityIncrementDifference_le_of_mem_curlWeakTestClosedSpan_tailH3
      hNS ht htau hEnd hE hTail
      r q hrq V hClosed

  have hPairSelf :
      ‖inner ℝ V V‖
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    change
      ‖inner ℝ
          V
          (
            h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
                hNS ht htau hEnd hTail q
              -
            h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
                hNS ht htau hEnd hTail r
          )‖
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ))

    exact hPair

  have hSq :
      ‖V‖ ^ 2
        ≤
      ((3 * ‖V‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    simpa only [
      real_inner_self_eq_norm_sq,
      Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖V‖)
    ] using hPairSelf

  have hRHSNonneg :
      0 ≤ h3UnitViscosityZeroRHSBound E :=
    h3UnitViscosityZeroRHSBound_nonneg hE

  have hLenNonneg :
      0 ≤ (q : ℝ) - (r : ℝ) :=
    sub_nonneg.mpr hrq

  have hFinal :
      ‖V‖
        ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    by_cases hV : ‖V‖ = 0

    · rw [hV]
      exact
        mul_nonneg
          (mul_nonneg (by norm_num) hRHSNonneg)
          hLenNonneg

    · have hVPos : 0 < ‖V‖ := by
        exact
          lt_of_le_of_ne
            (norm_nonneg V)
            (Ne.symm hV)

      nlinarith [hSq]

  simpa only [V] using hFinal

/-- Equivalent direct form for the actual old physical velocity path. -/
theorem norm_h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_sub_le_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖(
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q
        -
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail r
    )‖ ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  have h :=
    norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_tailH3_curl
      hNS ht htau hEnd hE hTail
      r q hrq

  have hEq :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q
        -
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail r
        =
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q
        -
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail r := by
    unfold
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
    abel

  rw [hEq] at h

  exact h

end

end Euclidean
end Bridge
end PrimeTensor
