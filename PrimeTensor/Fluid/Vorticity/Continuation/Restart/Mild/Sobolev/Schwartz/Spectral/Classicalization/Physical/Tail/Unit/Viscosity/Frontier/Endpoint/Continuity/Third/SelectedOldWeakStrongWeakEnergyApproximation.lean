import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyRHSBound

/-!
# Weak-energy self-test approximation

Approximate the actual left-endpoint selected--old difference by one compact
smooth divergence-free weak test.  The exact two-time weak evolution identity
then remains available for the approximant, while the endpoint pairing error
and the time-integrand error are controlled quantitatively.

This is the partition-ready replacement for assuming a strong old `L²`
temporal derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyApproximation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Approximate the actual left-endpoint difference by one admissible weak test,
retain the exact two-time weak evolution identity, and control the resulting
left-endpoint energy-pairing error. -/
theorem exists_divergenceFreeWeakTest_selectedOldDifference_leftApproximation_twoTime
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
      inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_sub_eq_projectedRHSDifference_intervalIntegral_of_allPressureDefect
        hNS ht htau hEnd hE hTail htauR hPressure
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

/-- Pointwise weak-energy estimate for one approximating weak test. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifference_le_energy_add_approximationError
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
    (φ : H3WeakTestVector)
    (a r : Set.Icc (0 : ℝ) tau)
    {ε : ℝ}
    (hε : 0 < ε)
    (hApprox :
      dist
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail a)
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        < ε) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR r)
      ≤
    3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail r‖ ^ 2
      +
    (ε +
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail a
        -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail r‖)
      *
    (6 * h3UnitViscosityZeroRHSBound E) := by
  let Da : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail a

  let Dr : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail r

  let Φ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ

  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
      hNS ht hEnd hE hTail htauR r

  have hApproxNorm :
      ‖Φ - Da‖ ≤ ε := by
    have hApprox' :
        ‖Da - Φ‖ < ε := by
      dsimp only [Da, Φ]
      simpa only [dist_eq_norm] using hApprox
    have hApproxRev :
        ‖Φ - Da‖ < ε := by
      simpa only [norm_sub_rev] using hApprox'
    exact le_of_lt hApproxRev

  have hEnergyTwo :
      2 * inner ℝ Dr R
        ≤
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        ‖Dr‖ ^ 2 := by
    dsimp only [Dr, R]
    exact
      two_inner_selectedOldUnitProjectedRHSDifference_le_six_mul_norm_sq_alternate_auto
        hNS ht hEnd hE hTail htauR r

  have hEnergy :
      inner ℝ Dr R
        ≤
      3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        ‖Dr‖ ^ 2 := by
    linarith

  have hDistance :
      ‖Φ - Dr‖
        ≤
      ε + ‖Da - Dr‖ := by
    calc
      ‖Φ - Dr‖
          =
        ‖(Φ - Da) + (Da - Dr)‖ := by
          congr 1
          abel
      _ ≤
        ‖Φ - Da‖ + ‖Da - Dr‖ :=
        norm_add_le _ _
      _ ≤
        ε + ‖Da - Dr‖ := by
        exact
          add_le_add
            hApproxNorm
            (le_refl ‖Da - Dr‖)

  have hR :
      ‖R‖ ≤ 6 * h3UnitViscosityZeroRHSBound E := by
    dsimp only [R]
    exact
      norm_h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_le_six_mul
        hNS ht hEnd hE hTail htauR r

  have hError :
      inner ℝ (Φ - Dr) R
        ≤
      (ε + ‖Da - Dr‖) *
        (6 * h3UnitViscosityZeroRHSBound E) := by
    calc
      inner ℝ (Φ - Dr) R
          ≤
        |inner ℝ (Φ - Dr) R| :=
        le_abs_self _
      _ ≤
        ‖Φ - Dr‖ * ‖R‖ :=
        abs_real_inner_le_norm _ _
      _ ≤
        (ε + ‖Da - Dr‖) *
          (6 * h3UnitViscosityZeroRHSBound E) := by
        exact
          mul_le_mul
            hDistance
            hR
            (norm_nonneg R)
            (by positivity)

  have hSplit :
      inner ℝ Φ R
        =
      inner ℝ Dr R + inner ℝ (Φ - Dr) R := by
    rw [inner_sub_left]
    ring

  calc
    inner ℝ Φ R
        =
      inner ℝ Dr R + inner ℝ (Φ - Dr) R :=
      hSplit
    _ ≤
      3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          ‖Dr‖ ^ 2
        +
      inner ℝ (Φ - Dr) R := by
      exact
        add_le_add
          hEnergy
          (le_refl (inner ℝ (Φ - Dr) R))
    _ ≤
      3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          ‖Dr‖ ^ 2
        +
      (ε + ‖Da - Dr‖) *
        (6 * h3UnitViscosityZeroRHSBound E) := by
      exact
        add_le_add
          (le_refl
            (3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖Dr‖ ^ 2))
          hError

end

end Euclidean
end Bridge
end PrimeTensor
