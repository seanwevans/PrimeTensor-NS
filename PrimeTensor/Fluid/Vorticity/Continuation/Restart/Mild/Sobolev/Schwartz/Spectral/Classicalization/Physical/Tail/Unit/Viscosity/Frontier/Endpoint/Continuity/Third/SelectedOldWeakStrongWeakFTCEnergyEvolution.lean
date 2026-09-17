import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakFTCLipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyApproximation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakFTCReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakRHSDifferenceFTC

/-!
# Weak-energy evolution from the scalar old weak FTC

The old temporal-product hypothesis has already been removed from the temporal
modulus layer.  This file carries the same reduction into the first weak-energy
layer.

The sole old-branch temporal input is now

    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed,

which contains exactly:

* scalar interval integrability of the old projected-RHS pairing; and
* scalar weak FTC for the old physical velocity increment.

The selected branch weak FTC is already proved outright.  Therefore the two
branchwise identities combine directly into the selected-minus-old identity

    <Φ,D(q)> = ∫₀^q <Φ,R_sel(r)-R_old(r)> dr.

Subtracting two endpoints gives the arbitrary two-time weak evolution needed by
the weak-energy argument.  The existing divergence-free approximation theorem
then gives the same self-test approximation, and the scalar-FTC Lipschitz
theorem gives continuity of the ambient difference path.

No product-space integrability of the strong old temporal derivative appears
in any theorem statement below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakFTCEnergyEvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected-minus-old projected-RHS scalar pairing is interval-integrable
under the scalar old weak-FTC interface. -/
theorem intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allProjectedRHSWeakFTC
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    IntervalIntegrable
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
            hNS ht hEnd hE hTail htauR r))
      volume
      (0 : ℝ)
      (q : ℝ) := by
  have hSelected :
      IntervalIntegrable
        (fun r : ℝ =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
              hNS ht hE hTail htauR r))
        volume
        (0 : ℝ)
        (q : ℝ) :=
    intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHSRealOnElapsed
      hNS ht htau hE hTail htauR φ q.property

  have hOld :
      IntervalIntegrable
        (fun r : ℝ =>
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r))
        volume
        (0 : ℝ)
        (q : ℝ) :=
    (hWeakFTC φ hφ q).1

  have hSub := hSelected.sub hOld

  simpa only [
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed,
    inner_sub_right
  ] using hSub

/-- One-endpoint selected-minus-old weak evolution from the scalar old weak FTC. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allProjectedRHSWeakFTC
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
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

  have hSelectedFTC :=
    h3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
      hNS ht htau hE hTail htauR

  have hSelected :=
    hSelectedFTC φ hφ q

  have hOld :=
    (hWeakFTC φ hφ q).2

  have hDecomp :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_selectedIncrement_sub_oldIncrement
      hNS ht htau hEnd hE hTail q

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
      (hWeakFTC φ hφ q).1

  rw [hDecomp, inner_sub_right]
  rw [hSelected, hOld]
  rw [← intervalIntegral.integral_sub hF hG]

  apply intervalIntegral.integral_congr
  intro r hr

  unfold h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
  dsimp only [F, G]
  rw [inner_sub_right]

/-- Arbitrary two-time selected-minus-old weak evolution from the scalar old
weak-FTC family. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_sub_eq_projectedRHSDifference_intervalIntegral_of_allProjectedRHSWeakFTC
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (a b : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail b
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail a)
      =
    ∫ r in (a : ℝ)..(b : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r) := by
  let F : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r)

  have hB :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail htauR hWeakFTC
      φ hφ b

  have hA :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail htauR hWeakFTC
      φ hφ a

  have hIntB :
      IntervalIntegrable F volume (0 : ℝ) (b : ℝ) := by
    dsimp only [F]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allProjectedRHSWeakFTC
        hNS ht htau hEnd hE hTail htauR hWeakFTC
        φ hφ b

  have hIntA :
      IntervalIntegrable F volume (0 : ℝ) (a : ℝ) := by
    dsimp only [F]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allProjectedRHSWeakFTC
        hNS ht htau hEnd hE hTail htauR hWeakFTC
        φ hφ a

  rw [inner_sub_right]

  change
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail b)
      -
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail a)
      =
    ∫ r in (a : ℝ)..(b : ℝ), F r

  rw [hB, hA]

  exact
    intervalIntegral.integral_interval_sub_left
      hIntB hIntA

/-- Self-test approximation retaining the scalar-FTC two-time weak evolution
identity. -/
theorem exists_divergenceFreeWeakTest_selectedOldDifference_leftApproximation_twoTime_of_allProjectedRHSWeakFTC
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
    (a b : Set.Icc (0 : ℝ) tau)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ
      ∧
      dist
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail a)
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        < ε
      ∧
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail b
            -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail a)
        =
      ∫ r in (a : ℝ)..(b : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
            hNS ht hEnd hE hTail htauR r)
      ∧
      |inner ℝ
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail a)
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail b
            -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail a)
        -
        (∫ r in (a : ℝ)..(b : ℝ),
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
              hNS ht hEnd hE hTail htauR r))|
        ≤
      ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail b
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail a‖ := by
  obtain ⟨φ, hφ, hApprox⟩ :=
    exists_divergenceFreeWeakTest_dist_selectedOldUnitVelocityDifference_lt
      hNS ht hEnd hE hTail htauR a hε

  let Da : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail a

  let Db : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail b

  let Φ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ

  let ΔD : H3PhysicalRealFinVectorL2Hilbert :=
    Db - Da

  have hWeak :
      inner ℝ Φ ΔD
        =
      ∫ r in (a : ℝ)..(b : ℝ),
        inner ℝ
          Φ
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
            hNS ht hEnd hE hTail htauR r) := by
    dsimp only [Φ, ΔD, Da, Db]
    exact
      inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_sub_eq_projectedRHSDifference_intervalIntegral_of_allProjectedRHSWeakFTC
        hNS ht htau hEnd hE hTail htauR hWeakFTC
        φ hφ a b

  have hApproxNorm :
      ‖Da - Φ‖ ≤ ε := by
    have hApprox' :
        ‖Da - Φ‖ < ε := by
      dsimp only [Da, Φ]
      simpa only [dist_eq_norm] using hApprox
    exact le_of_lt hApprox'

  have hError :
      |inner ℝ Da ΔD
        -
        (∫ r in (a : ℝ)..(b : ℝ),
          inner ℝ
            Φ
            (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
              hNS ht hEnd hE hTail htauR r))|
        ≤
      ε * ‖ΔD‖ := by
    rw [← hWeak]
    rw [← inner_sub_left]
    calc
      |inner ℝ (Da - Φ) ΔD|
          ≤ ‖Da - Φ‖ * ‖ΔD‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ε * ‖ΔD‖ := by
        exact
          mul_le_mul_of_nonneg_right
            hApproxNorm
            (norm_nonneg ΔD)

  refine ⟨φ, hφ, hApprox, ?_, ?_⟩
  · simpa only [Φ, ΔD, Da, Db] using hWeak
  · simpa only [Φ, ΔD, Da, Db] using hError

/-- The ambient selected-minus-old path is continuous on the physical elapsed
interval under the scalar weak-FTC interface. -/
theorem continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allProjectedRHSWeakFTC
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
        hNS ht htau hEnd hTail) :
    ContinuousOn
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail)
      (Set.Icc (0 : ℝ) tau) := by
  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let K : ℝ≥0 :=
    ⟨
      6 * h3UnitViscosityZeroRHSBound E,
      mul_nonneg
        (by norm_num)
        (h3UnitViscosityZeroRHSBound_nonneg hE)
    ⟩

  have hK :
      (K : ℝ) = 6 * h3UnitViscosityZeroRHSBound E := by
    rfl

  have hLip :
      LipschitzOnWith K D (Set.Icc (0 : ℝ) tau) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb

    rcases le_total a b with hab | hba

    · have h :=
        norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem_of_allProjectedRHSWeakFTC
          hNS ht htau hEnd hE hTail htauR hWeakFTC
          ha hb hab

      rw [dist_eq_norm, norm_sub_rev, Real.dist_eq]
      rw [hK]

      simpa only [
        D,
        abs_of_nonpos (sub_nonpos.mpr hab),
        neg_sub
      ] using h

    · have h :=
        norm_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_sub_le_of_mem_of_allProjectedRHSWeakFTC
          hNS ht htau hEnd hE hTail htauR hWeakFTC
          hb ha hba

      rw [dist_eq_norm, Real.dist_eq]
      rw [hK]

      simpa only [
        D,
        abs_of_nonneg (sub_nonneg.mpr hba)
      ] using h

  exact hLip.continuousOn

end

end Euclidean
end Bridge
end PrimeTensor
