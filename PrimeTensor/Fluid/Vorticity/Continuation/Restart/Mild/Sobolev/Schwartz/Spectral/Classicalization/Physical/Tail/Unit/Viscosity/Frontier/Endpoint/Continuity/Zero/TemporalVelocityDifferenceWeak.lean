import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFamily

/-!
# Zeroth-order endpoint continuity: arbitrary-pair weak velocity difference bound

The preceding strong estimate controls only the increment from elapsed zero to
one target.  To obtain genuine Lipschitz continuity we need the difference
between two arbitrary elapsed times `r <= q`.

This file stays on the same original anchor interval.  It does not re-anchor
the tail or strengthen the pressure hypothesis.

The argument is:

* use the pressure-defect mass frontier to obtain product integrability;
* identify the physical projected-RHS weak pairing almost everywhere with the
  integrable old temporal-derivative weak pairing;
* deduce interval integrability of the projected-RHS weak pairing;
* subtract the two existing weak FTC identities `0 -> q` and `0 -> r`;
* collapse them with `intervalIntegral.integral_add_adjacent_intervals`;
* bound the resulting `r -> q` projected-RHS integral by the existing uniform
  physical RHS ceiling.

The final estimate has the correct `q-r` modulus and is ready for the same
closed-span/self-pairing upgrade used at elapsed zero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalVelocityDifferenceWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroTemporalVelocityDifferenceWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Product integrability makes the endpoint-independent physical projected-RHS
weak pairing genuinely interval-integrable on every shortened interval. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_intervalIntegrable_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    IntervalIntegrable
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ)
      volume
      (0 : ℝ)
      q := by
  let g : Fin 3 → ℝ → ℝ :=
    fun i r =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        ∂volume

  have hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t q φ :=
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_pressureDefect
      hNS ht hEnd hE hTail φ
      hq.1 hq.2 hPressure

  have hOuter
      (i : Fin 3) :
      Integrable
        (g i)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)) := by
    let f : ℝ → Point3 → ℝ :=
      fun r x =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)

    have hInt :
        Integrable
          (Function.uncurry f)
          (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
            (volume : Measure Point3)) := by
      dsimp only [Function.uncurry, f]
      exact hProd i

    have h := hInt.integral_prod_left

    change
      Integrable
        (fun r : ℝ =>
          ∫ x : Point3,
            Function.uncurry f (r, x)
            ∂volume)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))

    exact h

  have hSum :
      Integrable
        (fun r : ℝ => ∑ i : Fin 3, g i r)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)) := by
    exact
      integrable_finsetSum
        (μ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))
        (f := g)
        (Finset.univ : Finset (Fin 3))
        (fun i hi => hOuter i)

  have hAE :
      (fun r : ℝ => ∑ i : Fin 3, g i r)
        =ᵐ[((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))]
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau := by
      exact
        ⟨
          hr.1.le,
          hr.2.le.trans hq.2
        ⟩

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T := by
      constructor
      · linarith [ht.1, hr.1]
      · linarith [hEnd, hr.2, hq.2]

    rw [
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
        hNS ht hEnd hTail φ hrTau
    ]

    have hWeak :=
      h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht hEnd hTail ⟨r, hrTau⟩ φ hφ

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
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
          hNS ht hEnd hTail φ ⟨r, hrTau⟩ := by
            simpa only using hWeak

  have hRHS :
      Integrable
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
          hNS ht hEnd hTail φ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)) :=
    hSum.congr hAE

  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hq.1]
  exact hRHS

/-- The two elapsed-zero weak FTC identities subtract to the exact arbitrary
elapsed interval identity. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementDifference_eq_projectedRHS_intervalIntegral_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ))
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q
          -
        h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail r)
      =
    ∫ s in (r : ℝ)..(q : ℝ),
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ s := by
  let f : ℝ → ℝ :=
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
      hNS ht hEnd hTail φ

  have hQOld :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_oldIntegralDifference_zero
      hNS ht htau hEnd hTail φ q

  have hROld :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_oldIntegralDifference_zero
      hNS ht htau hEnd hTail φ r

  have hQFTC :=
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHS_intervalIntegral_of_pressureDefect
      hNS ht hEnd hE hTail φ hφ q.property hPressure

  have hRFTC :=
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHS_intervalIntegral_of_pressureDefect
      hNS ht hEnd hE hTail φ hφ r.property hPressure

  have hQ :
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q)
        =
      ∫ s in (0 : ℝ)..(q : ℝ), f s := by
    rw [hQOld]
    simpa only [f] using hQFTC

  have hR :
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail r)
        =
      ∫ s in (0 : ℝ)..(r : ℝ), f s := by
    rw [hROld]
    simpa only [f] using hRFTC

  have hIntQ :
      IntervalIntegrable f volume (0 : ℝ) (q : ℝ) := by
    simpa only [f] using
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_intervalIntegrable_of_pressureDefect
        hNS ht hEnd hE hTail φ hφ q.property hPressure

  have hIntR :
      IntervalIntegrable f volume (0 : ℝ) (r : ℝ) := by
    simpa only [f] using
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_intervalIntegrable_of_pressureDefect
        hNS ht hEnd hE hTail φ hφ r.property hPressure

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

  rw [inner_sub_right, hQ, hR]

  linarith

/-- The exact projected-RHS integral over an arbitrary ordered elapsed interval
inherits the uniform pointwise weak-pairing bound with the correct interval
length. -/
theorem norm_intervalIntegral_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_between_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (r q : Set.Icc (0 : ℝ) tau)
    (hrq : (r : ℝ) ≤ (q : ℝ)) :
    ‖∫ s in (r : ℝ)..(q : ℝ),
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ s‖
      ≤
    (h3WeakTestVectorPhysicalL2L1Norm φ
      *
    h3UnitViscosityZeroRHSBound E)
      *
    ((q : ℝ) - (r : ℝ)) := by
  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.uIoc (r : ℝ) (q : ℝ) →
          ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
              hNS ht hEnd hTail φ s‖
            ≤
          h3WeakTestVectorPhysicalL2L1Norm φ
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

    simpa only [Real.norm_eq_abs] using
      abs_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_le_of_mem
        hNS ht hEnd hE hTail φ hsTau

  have hBound :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae
      hPointwise

  simpa only [
    abs_of_nonneg (sub_nonneg.mpr hrq)
  ] using hBound

/-- Arbitrary-pair Hilbert weak velocity difference bound, under the family
pressure-defect frontier. -/
theorem norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementDifference_le_of_allDivergenceFreePressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
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
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementDifference_eq_projectedRHS_intervalIntegral_of_pressureDefect
      hNS ht htau hEnd hE hTail
      φ hφ r q hrq (hPressure φ hφ)
  ]

  have hRaw :=
    norm_intervalIntegral_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_between_le
      hNS ht hEnd hE hTail φ r q hrq

  have hTest :=
    h3WeakTestVectorPhysicalL2L1Norm_le_three_mul_norm φ

  have hRHSNonneg :
      0 ≤ h3UnitViscosityZeroRHSBound E :=
    h3UnitViscosityZeroRHSBound_nonneg hE

  have hTimeNonneg :
      0 ≤ (q : ℝ) - (r : ℝ) :=
    sub_nonneg.mpr hrq

  exact
    hRaw.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          hTest
          hRHSNonneg)
        hTimeNonneg)

end

end Euclidean
end Bridge
end PrimeTensor
