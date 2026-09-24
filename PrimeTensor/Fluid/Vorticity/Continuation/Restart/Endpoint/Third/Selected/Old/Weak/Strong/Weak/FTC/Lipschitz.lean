import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.RHS.Difference.Product.Family
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Velocity.Lipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalVelocityDifferenceBound

/-!
# Strong temporal moduli from the scalar divergence-free weak FTC

The previous product-integrability route still asks for coordinatewise spacetime
integrability of the strong old temporal derivative.  That is stronger than the
weak--strong uniqueness argument itself needs.

For every divergence-free compact test and every elapsed endpoint, the actual
old-branch input is only:

1. interval integrability of the scalar projected-RHS pairing; and
2. the scalar weak FTC
       <φ, O(q)-O(0)> = ∫₀^q <φ,R_old(r)> dr.

This file packages exactly those two scalar facts as
`H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed`.

The existing temporal-product family implies this weaker interface, but all
subsequent estimates in this file use only the scalar weak FTC interface.

In particular:

    ‖O(q)-O(r)‖ ≤ 3 C(E) (q-r),

and hence

    ‖D(q)-D(r)‖ ≤ 6 C(E) (q-r).

This is the temporal-modulus layer with no reference to strong
`∂ₜu` product-space integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakFTCLipschitz
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact scalar old weak-evolution interface on one elapsed interval.

For every divergence-free compact test and every shortened endpoint, the
projected-RHS scalar pairing is interval-integrable and gives the old physical
velocity increment by weak FTC. -/
def H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ q : Set.Icc (0 : ℝ) tau,
      IntervalIntegrable
          (fun s : ℝ =>
            inner ℝ
              (h3WeakTestVectorPhysicalL2Hilbert φ)
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail s))
          volume
          (0 : ℝ)
          (q : ℝ)
      ∧
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q)
        =
      ∫ s in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail s)

/-- The stronger temporal-product family implies the exact scalar weak-FTC
interface. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allTemporalProductIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
      hNS ht htau hEnd hTail := by
  intro φ hφ q
  constructor
  · exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal_of_allTemporalProductIntegrable
        hNS ht hEnd hTail hProduct φ hφ q
  · exact
      inner_h3WeakTestVectorPhysicalL2Hilbert_oldVelocityIncrement_eq_projectedRHSHilbert_intervalIntegral_of_productIntegrable
        hNS ht htau hEnd hTail φ hφ q
        (hProduct φ hφ q)

/-- Arbitrary-pair old weak evolution from the scalar weak-FTC family. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementDifference_eq_projectedRHSHilbert_intervalIntegral_of_allProjectedRHSWeakFTC
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNS ht htau hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q
          -
        h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail r)
      =
    ∫ s in (r : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail s) := by
  let Φ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ

  let f : ℝ → ℝ :=
    fun s : ℝ =>
      inner ℝ
        Φ
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail s)

  have hQData :=
    hWeakFTC φ hφ q

  have hRData :=
    hWeakFTC φ hφ r

  have hQ :
      inner ℝ
          Φ
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q)
        =
      ∫ s in (0 : ℝ)..(q : ℝ), f s := by
    simpa only [Φ, f] using hQData.2

  have hR :
      inner ℝ
          Φ
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail r)
        =
      ∫ s in (0 : ℝ)..(r : ℝ), f s := by
    simpa only [Φ, f] using hRData.2

  have hIntQ :
      IntervalIntegrable f volume (0 : ℝ) (q : ℝ) := by
    simpa only [Φ, f] using hQData.1

  have hIntR :
      IntervalIntegrable f volume (0 : ℝ) (r : ℝ) := by
    simpa only [Φ, f] using hRData.1

  have hIntRQ :
      IntervalIntegrable f volume (r : ℝ) (q : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hrq]

    have hIntOnQ :
        IntegrableOn f (Set.Ioo (0 : ℝ) (q : ℝ)) volume := by
      exact
        (intervalIntegrable_iff_integrableOn_Ioo_of_le q.property.1).1
          hIntQ

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
      hIntR hIntRQ

  change
    inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q
          -
        h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail r)
      =
    ∫ s in (r : ℝ)..(q : ℝ), f s

  rw [inner_sub_right, hQ, hR]
  linarith

/-- Compact-test arbitrary-pair old weak estimate from scalar weak FTC. -/
theorem norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementDifference_le_of_allProjectedRHSWeakFTC
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNS ht htau hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q
          -
        h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail r)‖
      ≤
    ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementDifference_eq_projectedRHSHilbert_intervalIntegral_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail hWeakFTC φ hφ r q hrq
  ]

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.uIoc (r : ℝ) (q : ℝ) →
          ‖inner ℝ
              (h3WeakTestVectorPhysicalL2Hilbert φ)
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                hNS ht hEnd hTail s)‖
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
        ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail s‖
          ≤
        3 * h3UnitViscosityZeroRHSBound E := by
      rw [
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
          hNS ht hEnd hTail hsTau
      ]

      exact
        norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_le_three_mul
          hNS ht hEnd hE hTail ⟨s, hsTau⟩

    calc
      ‖inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail s)‖
          ≤
        ‖h3WeakTestVectorPhysicalL2Hilbert φ‖
          *
        ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail s‖ :=
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

/-- Extend the scalar weak-FTC estimate to the divergence-free physical closed
span. -/
theorem norm_inner_velocityIncrementDifference_le_of_mem_divergenceFreeWeakTestClosedSpan_of_allProjectedRHSWeakFTC
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNS ht htau hEnd hTail)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ))
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ :
      Φ ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan) :
    ‖inner ℝ
        Φ
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q
          -
        h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail r)‖
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
      norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementDifference_le_of_allProjectedRHSWeakFTC
        hNS ht htau hEnd hE hTail hWeakFTC
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

/-- Strong arbitrary-pair old physical `L²` estimate from scalar weak FTC. -/
theorem norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_of_allProjectedRHSWeakFTC
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNS ht htau hEnd hTail)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q
        -
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail r‖
      ≤
    (3 * h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      -
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail r

  have hLeray :
      V ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
    dsimp only [V]

    exact
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule.sub_mem
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
          hNS ht htau hEnd hTail q)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
          hNS ht htau hEnd hTail r)

  have hClosed :
      V ∈
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]
    exact hLeray

  have hPair :=
    norm_inner_velocityIncrementDifference_le_of_mem_divergenceFreeWeakTestClosedSpan_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail hWeakFTC
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
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail q
            -
          h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
              hNS ht htau hEnd hTail r)‖
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

/-- The selected-minus-old physical difference inherits the `6 C(E)` modulus
from scalar weak FTC. -/
theorem norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_sub_le_of_allProjectedRHSWeakFTC
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
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNS ht htau hEnd hTail)
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
    norm_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_sub_le_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail hWeakFTC r q hrq

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

/-- Ambient-real form of the `6 C(E)` selected--old modulus from scalar weak
FTC. -/
theorem norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem_of_allProjectedRHSWeakFTC
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNS ht htau hEnd hTail)
    (ha : a ∈ Set.Icc (0 : ℝ) tau)
    (hb : b ∈ Set.Icc (0 : ℝ) tau)
    (hab : a ≤ b) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail b
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail a‖
      ≤
    (6 * h3UnitViscosityZeroRHSBound E) * (b - a) := by
  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail hb,
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail ha
  ]

  exact
    norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_sub_le_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail htauR hWeakFTC
      ⟨a, ha⟩ ⟨b, hb⟩ hab

end

end Euclidean
end Bridge
end PrimeTensor
