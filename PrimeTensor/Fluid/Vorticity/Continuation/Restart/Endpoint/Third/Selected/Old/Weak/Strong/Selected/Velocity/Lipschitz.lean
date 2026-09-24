import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.FTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.RHS.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Difference.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalVelocityDifferenceBound

/-!
# Strong selected and selected--old temporal L² moduli

The selected branch already has exactly the ingredients needed to reproduce the
endpoint-independent old strong two-time estimate:

* exact weak projected-RHS FTC on every initial elapsed interval;
* the uniform physical Hilbert bound
      ‖R_selected(r)‖ ≤ 3 C(E);
* Leray-fixedness of every selected physical velocity state.

Subtracting the weak FTC identities at two ordered elapsed times gives the
selected weak evolution on `[r,q]`.  The RHS bound gives the correct linear
time modulus against every compact smooth divergence-free test.  Closure then
extends that estimate to the whole divergence-free physical Hilbert subspace,
where the selected velocity difference itself may be used as a test.

Thus

    ‖S(q) - S(r)‖ ≤ 3 C(E) (q-r).

Combining this with the already-proved old bound gives

    ‖D(q) - D(r)‖ ≤ 6 C(E) (q-r),

for the concrete selected-minus-old path.  This is the temporal modulus needed
by the uniform-partition mesh argument.

No strong old time derivative and no selected time-derivative hypothesis is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedVelocityLipschitz
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Subtract the two initial-time selected weak FTC identities to obtain the
exact selected weak evolution on an arbitrary ordered elapsed interval. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocity_sub_eq_projectedRHS_intervalIntegral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)
          -
        h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (r : ℝ))
      =
    ∫ s in (r : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR s) := by
  let Φ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ

  let S : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let f : ℝ → ℝ :=
    fun s : ℝ =>
      inner ℝ
        Φ
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR s)

  have hFTC :=
    h3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
      hNS ht htau hE hTail htauR

  have hQ :
      inner ℝ Φ (S (q : ℝ) - S 0)
        =
      ∫ s in (0 : ℝ)..(q : ℝ), f s := by
    simpa only [Φ, S, f,
      h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed] using
      hFTC φ hφ q

  have hR :
      inner ℝ Φ (S (r : ℝ) - S 0)
        =
      ∫ s in (0 : ℝ)..(r : ℝ), f s := by
    simpa only [Φ, S, f,
      h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed] using
      hFTC φ hφ r

  have hIntR :
      IntervalIntegrable f volume (0 : ℝ) (r : ℝ) := by
    dsimp only [f, Φ]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
        hNS ht htau hE hTail htauR φ r.property

  have hIntRQ :
      IntervalIntegrable f volume (r : ℝ) (q : ℝ) := by
    have hContTau :=
      continuousOn_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
        hNS ht htau hE hTail htauR φ

    have hSub :
        Set.uIcc (r : ℝ) (q : ℝ)
          ⊆
        Set.Icc (0 : ℝ) tau := by
      rw [uIcc_of_le hrq]
      intro s hs
      exact
        ⟨
          r.property.1.trans hs.1,
          hs.2.trans q.property.2
        ⟩

    exact
      (hContTau.mono hSub).intervalIntegrable

  have hAdd :
      (∫ s in (0 : ℝ)..(r : ℝ), f s)
        +
      (∫ s in (r : ℝ)..(q : ℝ), f s)
        =
      ∫ s in (0 : ℝ)..(q : ℝ), f s :=
    intervalIntegral.integral_add_adjacent_intervals
      hIntR hIntRQ

  have hPair :
      inner ℝ Φ (S (q : ℝ) - S (r : ℝ))
        =
      inner ℝ Φ (S (q : ℝ) - S 0)
        -
      inner ℝ Φ (S (r : ℝ) - S 0) := by
    simp only [inner_sub_right]
    ring

  rw [hPair, hQ, hR]

  linarith

/-- The selected weak two-time evolution inherits the uniform RHS ceiling with
the correct linear elapsed-time modulus. -/
theorem norm_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocity_sub_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)
          -
        h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (r : ℝ))‖
      ≤
    ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocity_sub_eq_projectedRHS_intervalIntegral
      hNS ht htau hE hTail htauR φ hφ r q hrq
  ]

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.uIoc (r : ℝ) (q : ℝ) →
          ‖inner ℝ
              (h3WeakTestVectorPhysicalL2Hilbert φ)
              (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
                hNS ht hE hTail htauR s)‖
            ≤
          (3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
            *
          h3UnitViscosityZeroRHSBound E := by
    filter_upwards with s
    intro hs

    rw [Set.uIoc_of_le hrq] at hs

    have hsTau :
        s ∈ Set.Icc (0 : ℝ) tau := by
      exact
        ⟨
          r.property.1.trans hs.1.le,
          hs.2.trans q.property.2
        ⟩

    have hRHS :
        ‖h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s‖
          ≤
        3 * h3UnitViscosityZeroRHSBound E := by
      rw [
        h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
          hNS ht hE hTail htauR hsTau
      ]

      exact
        norm_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_le_three_mul
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR ⟨s, hsTau⟩)

    calc
      ‖inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s)‖
          ≤
        ‖h3WeakTestVectorPhysicalL2Hilbert φ‖
          *
        ‖h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
            hNS ht hE hTail htauR s‖ :=
        abs_real_inner_le_norm _ _
      _ ≤
        ‖h3WeakTestVectorPhysicalL2Hilbert φ‖
          *
        (3 * h3UnitViscosityZeroRHSBound E) := by
          exact
            mul_le_mul_of_nonneg_left
              hRHS
              (norm_nonneg _)
      _ =
        (3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
          *
        h3UnitViscosityZeroRHSBound E := by
          ring

  have hBound :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae
      hPointwise

  simpa only [
    abs_of_nonneg (sub_nonneg.mpr hrq)
  ] using hBound

/-- Extend the selected arbitrary-pair weak estimate from compact smooth
divergence-free tests to their complete physical `L²` closed span. -/
theorem norm_inner_selectedVelocity_sub_le_of_mem_divergenceFreeWeakTestClosedSpan
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ))
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ :
      Φ ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan) :
    ‖inner ℝ
        Φ
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)
          -
        h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (r : ℝ))‖
      ≤
    ((3 * ‖Φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)
      -
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (r : ℝ)

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
      (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S := by
    intro Ψ hΨ

    rw [
      h3DivergenceFreeWeakTestPhysicalL2Span_eq_submodule_zeroSpan
    ] at hΨ

    change
      Ψ ∈ h3DivergenceFreeWeakTestPhysicalL2Set
    at hΨ

    rcases hΨ with ⟨φ, hφ, rfl⟩

    dsimp only [S, V]

    exact
      norm_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedVelocity_sub_le
        hNS ht htau hE hTail htauR
        φ hφ r q hrq

  have hClosureSubset :
      closure
          (h3DivergenceFreeWeakTestPhysicalL2Span :
            Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S :=
    closure_minimal hSpanSubset hClosed

  have hΦClosure :
      Φ ∈
      closure
        (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert) := by
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan at hΦ
    change
      Φ ∈
      closure
        (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
    at hΦ
    exact hΦ

  have hResult := hClosureSubset hΦClosure

  dsimp only [S, V] at hResult
  exact hResult

/-- Strong arbitrary-pair physical `L²` Lipschitz estimate for the selected
restart branch. -/
theorem norm_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_sub_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)
        -
      h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (r : ℝ)‖
      ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)
      -
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (r : ℝ)

  have hSelectedQ :
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)) := by
    have h :=
      h3PreterminalSelectedUnitVelocityPhysicalL2HilbertOnRadius_lerayFixed
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)

    simpa only [
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using h

  have hSelectedR :
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (r : ℝ)) := by
    have h :=
      h3PreterminalSelectedUnitVelocityPhysicalL2HilbertOnRadius_lerayFixed
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR r)

    simpa only [
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using h

  have hVLeray :
      H3PhysicalRealFinVectorL2HilbertLerayFixed V := by
    dsimp only [V]
    exact
      H3PhysicalRealFinVectorL2HilbertLerayFixed.sub
        hSelectedQ hSelectedR

  have hVClosed :
      V ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]

    exact
      (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff V).2
        hVLeray

  have hPair :=
    norm_inner_selectedVelocity_sub_le_of_mem_divergenceFreeWeakTestClosedSpan
      hNS ht htau hE hTail htauR
      r q hrq V hVClosed

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
          (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail (q : ℝ)
            -
          h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail (r : ℝ))‖
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

  have hTimeNonneg :
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
          hTimeNonneg
    · have hVPos : 0 < ‖V‖ := by
        exact
          lt_of_le_of_ne
            (norm_nonneg V)
            (Ne.symm hV)

      nlinarith [hSq]

  simpa only [V] using hFinal

/-- Consequently the concrete selected-minus-old physical difference path has
a `6 C(E)` arbitrary-pair modulus on the same elapsed interval. -/
theorem norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_sub_le
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail r‖
      ≤
    (6 * h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  let Sq : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail (q : ℝ)

  let Sr : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail (r : ℝ)

  let Oq : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

  let Or : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail r

  have hSelected :
      ‖Sq - Sr‖
        ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    dsimp only [Sq, Sr]
    exact
      norm_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_sub_le
        hNS ht htau hE hTail htauR r q hrq

  have hOldRaw :=
    norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_of_allPressureDefect
      hNS ht htau hEnd hE hTail hPressure r q hrq

  have hOldEq :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q
        -
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail r
        =
      Oq - Or := by
    dsimp only [Oq, Or]
    unfold h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
    abel

  have hOld :
      ‖Oq - Or‖
        ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
    rw [hOldEq] at hOldRaw
    exact hOldRaw

  have hDecomp :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail r
        =
      (Sq - Sr) - (Oq - Or) := by
    unfold h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
    dsimp only [Sq, Sr, Oq, Or]
    abel

  rw [hDecomp]

  calc
    ‖(Sq - Sr) - (Oq - Or)‖
        ≤
      ‖Sq - Sr‖ + ‖Oq - Or‖ :=
        norm_sub_le _ _
    _ ≤
      (3 * h3UnitViscosityZeroRHSBound E)
          * ((q : ℝ) - (r : ℝ))
        +
      (3 * h3UnitViscosityZeroRHSBound E)
          * ((q : ℝ) - (r : ℝ)) := by
        exact add_le_add hSelected hOld
    _ =
      (6 * h3UnitViscosityZeroRHSBound E)
        *
      ((q : ℝ) - (r : ℝ)) := by
        ring

end

end Euclidean
end Bridge
end PrimeTensor
