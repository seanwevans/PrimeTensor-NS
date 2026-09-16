import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongRHSDifference
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Single-integrand selected--old weak FTC

The selected branch FTC and the endpoint-independent old weak FTC are now both
closed, but the combined theorem still presents the RHS as

    ∫ <Φ, R_sel> - ∫ <Φ, R_old>.

For the relative-energy chain the natural object is the single
selected-minus-old RHS

    RΔ = R_sel - R_old.

This file closes that bookkeeping seam.

First, the old product-integrability hypothesis is unpacked one final time.
Exactly as in `TemporalWeakFTC`, product integrability gives integrability of
each spatially integrated temporal profile by `Integrable.integral_prod_left`;
the finite coordinate sum is therefore interval-integrable.  On the physical
open elapsed interval that summed temporal profile is exactly the old physical
projected-RHS Hilbert pairing.

Second, define the ambient-real selected-minus-old RHS vector by subtracting
the already-existing branchwise ambient extensions.  It agrees with the
closed-subtype `h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed`
at every physical elapsed time.

Finally, linearity of the interval integral gives the single-integrand weak
evolution identity

    <Φ, D(q)> = ∫₀^q <Φ, RΔ(r)> dr.

No old endpoint continuity or strong old `L²` temporal derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakRHSDifferenceFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongWeakRHSDifferenceFTC :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Under the same endpoint-independent product-integrability hypothesis used
by the old weak FTC, the old physical projected-RHS Hilbert pairing is
interval-integrable on `[0,q]`. -/
theorem intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t (q : ℝ) φ) :
    IntervalIntegrable
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
      volume
      (0 : ℝ)
      (q : ℝ) := by
  let g : Fin 3 → ℝ → ℝ :=
    fun i r =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)
        ∂volume

  have hOuter
      (i : Fin 3) :
      Integrable
        (g i)
        ((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ))) := by
    let f : ℝ → Point3 → ℝ :=
      fun r x =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + r) x)

    have hInt :
        Integrable
          (Function.uncurry f)
          (((volume : Measure ℝ).restrict
              (Set.Ioo (0 : ℝ) (q : ℝ))).prod
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
        ((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ)))

    exact h

  have hSum :
      Integrable
        (fun r : ℝ =>
          ∑ i : Fin 3, g i r)
        ((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ))) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun i hi => hOuter i)

  have hAE :
      (fun r : ℝ =>
        ∑ i : Fin 3, g i r)
        =ᵐ[((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ)))]
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r)) := by
    filter_upwards [
      ae_restrict_mem measurableSet_Ioo
    ] with r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau := by
      exact
        ⟨
          hr.1.le,
          hr.2.le.trans q.property.2
        ⟩

    have hAbs :
        t + r ∈ Set.Ioo (0 : ℝ) T := by
      constructor
      · linarith [ht.1, hr.1]
      · linarith [hEnd, hr.2, q.property.2]

    have hWeak :=
      h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail
        ⟨r, hrTau⟩
        φ hφ

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
            hNS ht hEnd hTail ⟨r, hrTau⟩) := by
              exact hWeak
      _ =
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) := by
              rw [
                h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
                  hNS ht hEnd hTail hrTau
              ]

  have hOldOpen :
      Integrable
        (fun r : ℝ =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r))
        ((volume : Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (q : ℝ))) :=
    hSum.congr hAE

  rw [
    intervalIntegrable_iff_integrableOn_Ioc_of_le q.property.1,
    integrableOn_Ioc_iff_integrableOn_Ioo
  ]

  exact hOldOpen

/-- Ambient-real selected-minus-old projected RHS on `[0,tau]`. -/
noncomputable def h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (r : ℝ) :
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
      hNS ht hE hTail htauR r
    -
  h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
      hNS ht hEnd hTail r

/-- On the physical closed elapsed interval, the ambient difference is exactly
the previously-defined selected-minus-old projected RHS vector. -/
@[simp]
theorem h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed_apply_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
        hNS ht hEnd hE hTail htauR r
      =
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
      hNS ht hEnd hE hTail htauR ⟨r, hr⟩ := by
  unfold h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
  unfold h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed

  rw [
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
      hNS ht hE hTail htauR hr,
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
      hNS ht hEnd hTail hr
  ]

/-- Complete endpoint-independent weak evolution identity with one
selected-minus-old projected-RHS integrand. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_productIntegrable
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
    ∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r) := by
  let F : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR r)

  let G : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r)

  have hF :
      IntervalIntegrable F volume (0 : ℝ) (q : ℝ) := by
    dsimp only [F]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
        hNS ht htau hE hTail htauR φ q.property

  have hG :
      IntervalIntegrable G volume (0 : ℝ) (q : ℝ) := by
    dsimp only [G]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal_of_productIntegrable
        hNS ht hEnd hTail φ hφ q hOldProd

  have hSeparated :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_selectedIntegral_sub_oldIntegral_of_productIntegrable
      hNS ht htau hEnd hE hTail htauR
      φ hφ q hOldProd

  have hSubIntegral :
      (∫ r in (0 : ℝ)..(q : ℝ), F r - G r)
        =
      (∫ r in (0 : ℝ)..(q : ℝ), F r)
        -
      (∫ r in (0 : ℝ)..(q : ℝ), G r) :=
    intervalIntegral.integral_sub hF hG

  rw [← hSubIntegral] at hSeparated

  have hIntegrandEq :
      (fun r : ℝ => F r - G r)
        =
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
            hNS ht hEnd hE hTail htauR r)) := by
    funext r

    unfold h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
    dsimp only [F, G]
    rw [inner_sub_right]

  rw [hIntegrandEq] at hSeparated

  exact hSeparated

end

end Euclidean
end Bridge
end PrimeTensor
