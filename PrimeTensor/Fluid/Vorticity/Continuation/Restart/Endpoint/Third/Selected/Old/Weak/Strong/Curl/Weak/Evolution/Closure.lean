import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Velocity.Curl.Lipschitz.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Test.Fixed

/-!
# Extend the endpoint-independent curl evolution identity to all divergence-free tests

The pressure-free vorticity route gives the exact old weak evolution identity on
the algebraic span of the three elementary curl-test families.

The curl-density theorem identifies the closed span of those families with the
complete physical Leray-fixed subspace.  Every compact smooth divergence-free
weak test therefore admits arbitrarily accurate approximation in physical
`L²` by a curl-span state.

At one target `q`, let

    V = U_old(q) - U_old(0)

and let `R_old(r)` be the endpoint-independent projected RHS.  For a curl-span
approximant `Ψ` we already know

    <Ψ,V> = ∫₀^q <Ψ,R_old(r)> dr.

For the target divergence-free weak test `Φ`, scalar RHS interval
integrability is already automatic.  Hence the difference of the two RHS
integrals is the integral of the pairing against `Φ-Ψ`.  Cauchy--Schwarz and

    ‖R_old(r)‖ ≤ 3 C(E)

show that both sides vary continuously with the approximating Hilbert test.
Sending `Ψ -> Φ` therefore gives the exact evolution identity for every
divergence-free compact weak test.

This closes the evolution-only scalar frontier without endpoint continuity,
pressure estimates, temporal product integrability, or Hilbert-valued old-RHS
Bochner integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongCurlWeakEvolutionClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every divergence-free compact weak-test state can be approximated
arbitrarily well by an element of the algebraic span of the three elementary
curl-test families. -/
theorem exists_curlWeakTestSpan_dist_h3WeakTestVectorPhysicalL2Hilbert_lt
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Ψ : H3PhysicalRealFinVectorL2Hilbert,
      Ψ ∈ h3CurlWeakTestPhysicalL2Span
      ∧
      dist
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        Ψ
        < ε := by
  let Φ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ

  have hSet :
      Φ ∈ h3DivergenceFreeWeakTestPhysicalL2Set := by
    exact ⟨φ, hφ, rfl⟩

  have hLeray :
      Φ ∈ h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
    h3DivergenceFreeWeakTestPhysicalL2Set_subset_lerayFixedSubmodule
      hSet

  have hClosed :
      Φ ∈ h3CurlWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3CurlWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]
    exact hLeray

  unfold h3CurlWeakTestPhysicalL2ClosedSpan at hClosed

  change
    Φ ∈
      closure
        (h3CurlWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
    at hClosed

  rw [Metric.mem_closure_iff] at hClosed

  obtain ⟨Ψ, hΨ, hDist⟩ :=
    hClosed ε hε

  exact ⟨Ψ, hΨ, hDist⟩

/-- The exact endpoint-independent old weak evolution identity holds for every
compact smooth divergence-free weak test. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed
      hNS ht htau hEnd hTail := by
  intro φ hφ q

  let Φ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ

  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
      hNS ht htau hEnd hTail q

  let R : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
      hNS ht hEnd hTail

  let fΦ : ℝ → ℝ :=
    fun r : ℝ => inner ℝ Φ (R r)

  have hΦInt :
      IntervalIntegrable fΦ volume (0 : ℝ) (q : ℝ) := by
    dsimp only [fΦ, Φ, R]

    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
        hNS ht hEnd hE hTail φ hφ q

  let D : ℝ :=
    inner ℝ Φ V
      -
    ∫ r in (0 : ℝ)..(q : ℝ), fΦ r

  have hDZero : D = 0 := by
    by_contra hDNe

    have hDPos :
        0 < ‖D‖ :=
      norm_pos_iff.mpr hDNe

    let A : ℝ :=
      ‖V‖
        +
      (3 * h3UnitViscosityZeroRHSBound E) * (q : ℝ)
        +
      1

    have hCNonneg :
        0 ≤ h3UnitViscosityZeroRHSBound E :=
      h3UnitViscosityZeroRHSBound_nonneg hE

    have hqNonneg :
        0 ≤ (q : ℝ) :=
      q.property.1

    have hAPos :
        0 < A := by
      dsimp only [A]
      nlinarith [norm_nonneg V]

    let δ : ℝ :=
      ‖D‖ / (2 * A)

    have hδPos :
        0 < δ := by
      dsimp only [δ]
      positivity

    obtain ⟨Ψ, hΨSpan, hDist⟩ :=
      exists_curlWeakTestSpan_dist_h3WeakTestVectorPhysicalL2Hilbert_lt
        φ hφ hδPos

    have hΨIntegrated :
        H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
          hNS ht htau hEnd hTail q Ψ := by
      exact
        (h3CurlWeakTestPhysicalL2Span_le_oldProjectedRHSIntegratedPairingSubmoduleTo
          hNS ht htau hEnd hE hTail q)
          hΨSpan

    unfold
      H3PreterminalTailCanonicalOldProjectedRHSIntegratedPairingTo
      at hΨIntegrated

    rcases hΨIntegrated with
      ⟨hΨInt, hΨEq⟩

    let fΨ : ℝ → ℝ :=
      fun r : ℝ => inner ℝ Ψ (R r)

    have hΨInt' :
        IntervalIntegrable fΨ volume (0 : ℝ) (q : ℝ) := by
      simpa only [fΨ, R] using hΨInt

    have hΨEq' :
        inner ℝ Ψ V
          =
        ∫ r in (0 : ℝ)..(q : ℝ), fΨ r := by
      simpa only [V, fΨ, R] using hΨEq

    let fDiff : ℝ → ℝ :=
      fun r : ℝ =>
        inner ℝ (Φ - Ψ) (R r)

    have hDiffInt :
        IntervalIntegrable fDiff volume (0 : ℝ) (q : ℝ) := by
      have hSub :=
        hΦInt.sub hΨInt'

      simpa only [
        fDiff,
        fΦ,
        fΨ,
        inner_sub_left
      ] using hSub

    have hIntegralDiff :
        (∫ r in (0 : ℝ)..(q : ℝ), fDiff r)
          =
        (∫ r in (0 : ℝ)..(q : ℝ), fΦ r)
          -
        (∫ r in (0 : ℝ)..(q : ℝ), fΨ r) := by
      calc
        (∫ r in (0 : ℝ)..(q : ℝ), fDiff r)
            =
          ∫ r in (0 : ℝ)..(q : ℝ),
            (fΦ r - fΨ r) := by
              apply intervalIntegral.integral_congr
              intro r _hr
              dsimp only [fDiff, fΦ, fΨ]
              rw [inner_sub_left]
        _ =
          (∫ r in (0 : ℝ)..(q : ℝ), fΦ r)
            -
          (∫ r in (0 : ℝ)..(q : ℝ), fΨ r) :=
          intervalIntegral.integral_sub hΦInt hΨInt'

    have hDefectEq :
        D
          =
        inner ℝ (Φ - Ψ) V
          -
        ∫ r in (0 : ℝ)..(q : ℝ), fDiff r := by
      dsimp only [D]
      rw [
        hIntegralDiff,
        inner_sub_left,
        hΨEq'
      ]
      ring

    have hPointwise :
        ∀ᵐ r : ℝ ∂volume,
          r ∈ Set.uIoc (0 : ℝ) (q : ℝ) →
            ‖fDiff r‖
              ≤
            ‖Φ - Ψ‖
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

      have hRHS :
          ‖R r‖
            ≤
          3 * h3UnitViscosityZeroRHSBound E := by
        dsimp only [R]

        rw [
          h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
            hNS ht hEnd hTail hrTau
        ]

        exact
          norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_le_three_mul
            hNS ht hEnd hE hTail ⟨r, hrTau⟩

      dsimp only [fDiff]

      calc
        ‖inner ℝ (Φ - Ψ) (R r)‖
            ≤
          ‖Φ - Ψ‖ * ‖R r‖ :=
          norm_inner_le_norm _ _
        _ ≤
          ‖Φ - Ψ‖
            *
          (3 * h3UnitViscosityZeroRHSBound E) := by
            exact
              mul_le_mul_of_nonneg_left
                hRHS
                (norm_nonneg (Φ - Ψ))

    have hIntegralBound0 :=
      intervalIntegral.norm_integral_le_of_norm_le_const_ae
        hPointwise

    have hIntegralBound :
        ‖∫ r in (0 : ℝ)..(q : ℝ), fDiff r‖
          ≤
        (‖Φ - Ψ‖
          *
        (3 * h3UnitViscosityZeroRHSBound E))
          *
        (q : ℝ) := by
      simpa only [
        sub_zero,
        abs_of_nonneg q.property.1
      ] using hIntegralBound0

    have hInnerBound :
        ‖inner ℝ (Φ - Ψ) V‖
          ≤
        ‖Φ - Ψ‖ * ‖V‖ :=
      norm_inner_le_norm _ _

    have hDefectBound :
        ‖D‖
          ≤
        dist Φ Ψ * A := by
      rw [hDefectEq]

      calc
        ‖inner ℝ (Φ - Ψ) V
            -
          ∫ r in (0 : ℝ)..(q : ℝ), fDiff r‖
            ≤
          ‖inner ℝ (Φ - Ψ) V‖
            +
          ‖∫ r in (0 : ℝ)..(q : ℝ), fDiff r‖ :=
          norm_sub_le _ _
        _ ≤
          (‖Φ - Ψ‖ * ‖V‖)
            +
          ((‖Φ - Ψ‖
              *
            (3 * h3UnitViscosityZeroRHSBound E))
              *
            (q : ℝ)) := by
          exact add_le_add hInnerBound hIntegralBound
        _ =
          ‖Φ - Ψ‖
            *
          (‖V‖
            +
           (3 * h3UnitViscosityZeroRHSBound E) * (q : ℝ)) := by
          ring
        _ ≤
          ‖Φ - Ψ‖ * A := by
          apply mul_le_mul_of_nonneg_left
          · dsimp only [A]
            linarith
          · exact norm_nonneg (Φ - Ψ)
        _ =
          dist Φ Ψ * A := by
          rw [dist_eq_norm]

    have hStrict :
        dist Φ Ψ * A
          <
        δ * A :=
      mul_lt_mul_of_pos_right hDist hAPos

    have hδA :
        δ * A = ‖D‖ / 2 := by
      dsimp only [δ]
      field_simp [ne_of_gt hAPos]

    rw [hδA] at hStrict

    linarith

  have hEq :
      inner ℝ Φ V
        =
      ∫ r in (0 : ℝ)..(q : ℝ), fΦ r := by
    exact sub_eq_zero.mp hDZero

  simpa only [Φ, V, fΦ, R] using hEq

/-- Therefore the endpoint-independent curl/vorticity argument closes the
earlier scalar weak-FTC frontier outright. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_tailH3_curl
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
      hNS ht htau hEnd hTail := by
  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allProjectedRHSWeakEvolution
      hNS ht htau hEnd hE hTail
      (H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_tailH3_curl
        hNS ht htau hEnd hE hTail)

end

end Euclidean
end Bridge
end PrimeTensor
