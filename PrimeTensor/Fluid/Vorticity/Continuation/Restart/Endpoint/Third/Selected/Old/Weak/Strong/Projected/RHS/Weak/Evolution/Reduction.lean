import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Lipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.RHS.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalJointMeasurable

/-!
# Remove scalar projected-RHS integrability from the weak-FTC frontier

The scalar weak-FTC interface still contains two requirements:

1. interval integrability of the old projected-RHS pairing;
2. the actual weak evolution identity.

The first requirement is not an independent frontier.

For a divergence-free compact weak test `φ`, joint measurability of

    (r,x) ↦ φ_i(x) ∂ₜu_i(t+r,x)

is already proved endpoint-independently.  Spatial integration therefore makes

    r ↦ Σ_i ∫ φ_i(x) ∂ₜu_i(t+r,x) dx

a.e.-strongly measurable.  Snapshot-by-snapshot weak momentum identifies this
scalar function on `[0,τ]` with the physical projected-RHS Hilbert pairing.

The old projected RHS also has the uniform physical Hilbert bound

    ‖R_old(r)‖ ≤ 3 C(E).

Hence the scalar pairing is measurable and bounded on every finite elapsed
interval, so it is interval-integrable with no pressure, product-integrability,
or extra temporal hypothesis.

After this file the only remaining old temporal frontier is therefore the
scalar weak evolution identity itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongProjectedRHSWeakEvolutionReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongProjectedRHSWeakEvolutionReduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The scalar old projected-RHS Hilbert pairing is a.e.-strongly measurable
in elapsed time without any temporal product-integrability hypothesis. -/
theorem aestronglyMeasurable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    AEStronglyMeasurable
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
      (volume : Measure ℝ) := by
  let g : Fin 3 → ℝ → ℝ :=
    fun i r =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        ∂volume

  have hg
      (i : Fin 3) :
      AEStronglyMeasurable
        (g i)
        (volume : Measure ℝ) := by
    have hJoint :
        Measurable
          (fun z : ℝ × Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i z.2)
              (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
                hNS i (t + z.1) z.2)) :=
      measurable_h3WeakTest_mul_loggedPreterminalVelocity_temporalDerivative_onElapsed
        hNS (t := t) i (φ i)

    dsimp only [g]

    exact
      hJoint.aestronglyMeasurable.integral_prod_right'

  have hSum :
      AEStronglyMeasurable
        (fun r : ℝ => ∑ i : Fin 3, g i r)
        (volume : Measure ℝ) := by
    exact
      Finset.aestronglyMeasurable_fun_sum
        (Finset.univ : Finset (Fin 3))
        (fun i _hi => hg i)

  let S : Set ℝ :=
    Set.Icc (0 : ℝ) tau

  let P : ℝ → ℝ :=
    S.piecewise
      (fun r : ℝ => ∑ i : Fin 3, g i r)
      (fun _r : ℝ => 0)

  have hP :
      AEStronglyMeasurable
        P
        (volume : Measure ℝ) := by
    dsimp only [P]
    exact
      AEStronglyMeasurable.piecewise
        measurableSet_Icc
        (hSum.mono_measure Measure.restrict_le_self)
        aestronglyMeasurable_const

  have hEq :
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
        =
      P := by
    funext r

    by_cases hr : r ∈ Set.Icc (0 : ℝ) tau

    · have hAbs :
          t + r ∈ Set.Ioo (0 : ℝ) T := by
        constructor
        · linarith [ht.1, hr.1]
        · linarith [hEnd, hr.2]

      have hWeak :=
        h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail ⟨r, hr⟩ φ hφ

      have hSumEq :
          (∑ i : Fin 3, g i r)
            =
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
              hNS ht hEnd hTail ⟨r, hr⟩) := by
        calc
          (∑ i : Fin 3, g i r)
              =
            ∑ i : Fin 3,
              ∫ x : Point3,
                (ContinuousLinearMap.lsmul ℝ ℝ)
                  (φ i x)
                  (temporal.d
                    (fun a : ℝ =>
                      loggedVelocityComponent
                        u a (h3AxisOfFin3 i) x)
                    (t + r))
                ∂volume := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  dsimp only [g]
                  apply integral_congr_ae
                  filter_upwards with x
                  rw [
                    h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension_apply_of_mem
                      hNS i hAbs x
                  ]
          _ =
            inner ℝ
              (h3WeakTestVectorPhysicalL2Hilbert φ)
              (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
                hNS ht hEnd hTail ⟨r, hr⟩) := by
                  exact hWeak

      rw [
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
          hNS ht hEnd hTail hr
      ]

      simpa [P, S, hr] using hSumEq.symm

    · have hRealZero :
          h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r
            =
          0 := by
        simp only [
          h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal,
          dite_eq_right hr
        ]

      simp [hRealZero, P, S, hr]

  rw [hEq]

  exact hP

/-- On every finite elapsed interval, the old scalar projected-RHS Hilbert
pairing is interval-integrable outright. -/
theorem intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    IntervalIntegrable
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
      volume
      (0 : ℝ)
      (q : ℝ) := by
  let f : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r)

  have hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure ℝ) := by
    dsimp only [f]
    exact
      aestronglyMeasurable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
        hNS ht hEnd hTail φ hφ

  have hfBound :
      ∀ᵐ r : ℝ ∂((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (q : ℝ))),
        ‖f r‖
          ≤
        (3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
          *
        h3UnitViscosityZeroRHSBound E := by
    filter_upwards [
      ae_restrict_mem measurableSet_Ioc
    ] with r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau := by
      exact
        ⟨
          hr.1.le,
          hr.2.trans q.property.2
        ⟩

    have hRHS :
        ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r‖
          ≤
        3 * h3UnitViscosityZeroRHSBound E := by
      rw [
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
          hNS ht hEnd hTail hrTau
      ]

      exact
        norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_le_three_mul
          hNS ht hEnd hE hTail ⟨r, hrTau⟩

    dsimp only [f]

    calc
      ‖inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r)‖
          ≤
        ‖h3WeakTestVectorPhysicalL2Hilbert φ‖
          *
        ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r‖ :=
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

  have hfMeasOn :
      AEStronglyMeasurable
        f
        ((volume : Measure ℝ).restrict
          (Set.Ioc (0 : ℝ) (q : ℝ))) := by
    exact
      hfMeas.mono_measure Measure.restrict_le_self

  have hfIntOn :
      IntegrableOn
        f
        (Set.Ioc (0 : ℝ) (q : ℝ))
        volume := by
    exact
      IntegrableOn.of_bound
        measure_Ioc_lt_top
        hfMeasOn
        ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
          * h3UnitViscosityZeroRHSBound E)
        hfBound

  rw [
    intervalIntegrable_iff_integrableOn_Ioc_of_le q.property.1
  ]

  exact hfIntOn

/-- The actual remaining local temporal frontier: the scalar old weak
evolution identity, with integrability removed because it is automatic. -/
def H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed
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
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r)

/-- The evolution-only frontier implies the earlier scalar weak-FTC frontier
because projected-RHS scalar integrability is automatic. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allProjectedRHSWeakEvolution
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed
        hNS ht htau hEnd hTail) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
      hNS ht htau hEnd hTail := by
  intro φ hφ q

  constructor

  · exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal
        hNS ht hEnd hE hTail φ hφ q

  · exact
      hEvolution φ hφ q

end

end Euclidean
end Bridge
end PrimeTensor
