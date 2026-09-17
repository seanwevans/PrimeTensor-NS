import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyInterval

/-!
# Squared-norm weak-energy increment

The previous file controls the linear energy increment

    <D(a), D(b)-D(a)>.

For a real Hilbert space the exact polarization identity gives

    ‖D(b)‖² - ‖D(a)‖²
      =
    2 <D(a), D(b)-D(a)>
      + ‖D(b)-D(a)‖².

This file combines that identity with the ordered-interval weak-energy estimate.
The result exposes the final partition structure directly:

* the desired quadratic energy integral;
* the weak-test approximation error, proportional to `eps`;
* the genuine quadratic increment remainder `‖D(b)-D(a)‖²`.

The last two terms are the only temporal errors left for the mesh-limit step.
No strong old `L²` derivative or endpoint-continuity hypothesis is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergySquareIncrement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact squared-norm increment identity in the native physical real Hilbert
space. -/
theorem h3PhysicalRealFinVectorL2Hilbert_norm_sq_sub_eq_two_inner_add_norm_sub_sq
    (A B : H3PhysicalRealFinVectorL2Hilbert) :
    ‖B‖ ^ 2 - ‖A‖ ^ 2
      =
    2 * inner ℝ A (B - A) + ‖B - A‖ ^ 2 := by
  have hB :
      B = A + (B - A) := by
    abel

  rw [hB, norm_add_sq_real]

  have hCancel :
      A + (B - A) - A = B - A := by
    abel

  rw [hCancel]

  ring

/-- Ordered local squared-energy increment bound obtained from the weak
self-test approximation.

The integrand is the same one from the preceding interval theorem.  The only
additional term is the exact Hilbert quadratic remainder
`‖D(b)-D(a)‖²`. -/
theorem norm_sq_selectedOldDifference_sub_le_approximateEnergyIncrement
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
    (hab : (a : ℝ) ≤ (b : ℝ))
    {ε : ℝ}
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail b‖ ^ 2
      -
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail a‖ ^ 2
      ≤
    2 *
      (∫ r in (a : ℝ)..(b : ℝ),
        3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail r‖ ^ 2
          +
        (ε +
          ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
                (one_pos : (0 : ℝ) < 1)
                hNS ht hEnd hE hTail a
            -
            h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖)
          *
        (6 * h3UnitViscosityZeroRHSBound E))
      +
    2 * ε *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail b
        -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail a‖
      +
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail b
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail a‖ ^ 2 := by
  let Da : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail a

  let Db : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail b

  let G : ℝ → ℝ :=
    fun r : ℝ =>
      3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail r‖ ^ 2
        +
      (ε +
        ‖Da -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail r‖)
        *
      (6 * h3UnitViscosityZeroRHSBound E)

  obtain ⟨_φ, _hφ, _hApprox, hLinear⟩ :=
    exists_divergenceFreeWeakTest_selectedOldDifference_approximateEnergyIncrement
      hNS ht htau hEnd hE hTail htauR hPressure
      a b hab hε

  have hLinear' :
      inner ℝ Da (Db - Da)
        ≤
      (∫ r in (a : ℝ)..(b : ℝ), G r)
        +
      ε * ‖Db - Da‖ := by
    dsimp only [Da, Db, G]
    exact hLinear

  have hTwice :
      2 * inner ℝ Da (Db - Da)
        ≤
      2 *
        ((∫ r in (a : ℝ)..(b : ℝ), G r)
          +
        ε * ‖Db - Da‖) := by
    exact
      mul_le_mul_of_nonneg_left
        hLinear'
        (by norm_num)

  have hIdentity :
      ‖Db‖ ^ 2 - ‖Da‖ ^ 2
        =
      2 * inner ℝ Da (Db - Da)
        + ‖Db - Da‖ ^ 2 :=
    h3PhysicalRealFinVectorL2Hilbert_norm_sq_sub_eq_two_inner_add_norm_sub_sq
      Da Db

  rw [hIdentity]

  calc
    2 * inner ℝ Da (Db - Da)
        + ‖Db - Da‖ ^ 2
        ≤
      2 *
          ((∫ r in (a : ℝ)..(b : ℝ), G r)
            +
          ε * ‖Db - Da‖)
        +
      ‖Db - Da‖ ^ 2 := by
      exact
        add_le_add
          hTwice
          (le_refl (‖Db - Da‖ ^ 2))
    _ =
      2 * (∫ r in (a : ℝ)..(b : ℝ), G r)
        +
      2 * ε * ‖Db - Da‖
        +
      ‖Db - Da‖ ^ 2 := by
      ring

/-- The same local squared-energy estimate written with the ambient-real
difference at the two endpoints. -/
theorem norm_sq_selectedOldDifferenceReal_sub_le_approximateEnergyIncrement_of_mem
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (ha : a ∈ Set.Icc (0 : ℝ) tau)
    (hb : b ∈ Set.Icc (0 : ℝ) tau)
    (hab : a ≤ b)
    {ε : ℝ}
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail b‖ ^ 2
      -
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail a‖ ^ 2
      ≤
    2 *
      (∫ r in a..b,
        3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail r‖ ^ 2
          +
        (ε +
          ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail a
            -
            h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖)
          *
        (6 * h3UnitViscosityZeroRHSBound E))
      +
    2 * ε *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail b
        -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail a‖
      +
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail b
        -
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail a‖ ^ 2 := by
  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail hb,
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail ha
  ]

  exact
    norm_sq_selectedOldDifference_sub_le_approximateEnergyIncrement
      hNS ht htau hEnd hE hTail htauR hPressure
      ⟨a, ha⟩ ⟨b, hb⟩ hab hε

end

end Euclidean
end Bridge
end PrimeTensor
