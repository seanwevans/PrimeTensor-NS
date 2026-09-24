import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Energy.Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Square.Increment

/-!
# One-cell weak-energy increment from scalar old weak FTC

The selected--old weak evolution and temporal modulus have already been reduced
from old strong temporal product integrability to the scalar divergence-free
weak FTC interface

    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed.

This file carries that reduction through the local weak-energy estimate.

Nothing in the pointwise weak--strong RHS estimate depends on the old temporal
regularity mechanism.  Therefore the existing Hilbert-space approximation and
polarization argument goes through unchanged once:

* the selected-minus-old RHS pairing is interval-integrable;
* the ambient difference path is continuous; and
* the two-time weak evolution identity is available.

All three are now provided by `SelectedOldWeakStrongWeakFTCEnergyEvolution`.

The endpoint result is the same local squared-energy increment previously
proved from `hProduct`, but now from `hWeakFTC` alone.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakFTCEnergyIncrement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Integrated weak-energy estimate for one fixed self-test approximant from
the scalar old weak-FTC interface. -/
theorem intervalIntegral_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifference_le_energy_add_approximationError_of_allProjectedRHSWeakFTC
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
    (a b : Set.Icc (0 : ℝ) tau)
    (hab : (a : ℝ) ≤ (b : ℝ))
    {ε : ℝ}
    (hε : 0 < ε)
    (hApprox :
      dist
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail a)
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        < ε) :
    (∫ r in (a : ℝ)..(b : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r))
      ≤
    ∫ r in (a : ℝ)..(b : ℝ),
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
      (6 * h3UnitViscosityZeroRHSBound E) := by
  let F : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r)

  let Da : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail a

  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let G : ℝ → ℝ :=
    fun r : ℝ =>
      3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
          ‖D r‖ ^ 2
        +
      (ε + ‖Da - D r‖) *
        (6 * h3UnitViscosityZeroRHSBound E)

  have h0b : (0 : ℝ) ≤ (b : ℝ) :=
    b.property.1

  have hF0b :
      IntervalIntegrable F volume (0 : ℝ) (b : ℝ) := by
    dsimp only [F]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allProjectedRHSWeakFTC
        hNS ht htau hEnd hE hTail htauR hWeakFTC
        φ hφ b

  have hFInt :
      IntervalIntegrable F volume (a : ℝ) (b : ℝ) := by
    apply hF0b.mono_set

    rw [
      Set.uIcc_of_le hab,
      Set.uIcc_of_le h0b
    ]

    intro r hr
    exact
      ⟨a.property.1.trans hr.1, hr.2⟩

  have hSub :
      Set.Icc (a : ℝ) (b : ℝ)
        ⊆
      Set.Icc (0 : ℝ) tau := by
    intro r hr
    exact
      ⟨a.property.1.trans hr.1,
        hr.2.trans b.property.2⟩

  have hDCont :
      ContinuousOn D (Set.Icc (a : ℝ) (b : ℝ)) := by
    dsimp only [D]
    exact
      (continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allProjectedRHSWeakFTC
        hNS ht htau hEnd hE hTail htauR hWeakFTC).mono hSub

  have hNormSqCont :
      ContinuousOn
        (fun r : ℝ => ‖D r‖ ^ 2)
        (Set.Icc (a : ℝ) (b : ℝ)) :=
    (continuous_norm.comp_continuousOn hDCont).pow 2

  have hConstDa :
      ContinuousOn
        (fun _r : ℝ => Da)
        (Set.Icc (a : ℝ) (b : ℝ)) :=
    continuousOn_const

  have hErrorNormCont :
      ContinuousOn
        (fun r : ℝ => ‖Da - D r‖)
        (Set.Icc (a : ℝ) (b : ℝ)) :=
    continuous_norm.comp_continuousOn
      (hConstDa.sub hDCont)

  have hEnergyCont :
      ContinuousOn
        (fun r : ℝ =>
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            ‖D r‖ ^ 2)
        (Set.Icc (a : ℝ) (b : ℝ)) := by
    exact
      continuousOn_const.mul hNormSqCont

  have hApproxErrorCont :
      ContinuousOn
        (fun r : ℝ =>
          (ε + ‖Da - D r‖) *
            (6 * h3UnitViscosityZeroRHSBound E))
        (Set.Icc (a : ℝ) (b : ℝ)) := by
    exact
      (continuousOn_const.add hErrorNormCont).mul
        continuousOn_const

  have hGCont :
      ContinuousOn G (Set.Icc (a : ℝ) (b : ℝ)) := by
    dsimp only [G]
    exact hEnergyCont.add hApproxErrorCont

  have hGInt :
      IntervalIntegrable G volume (a : ℝ) (b : ℝ) :=
    hGCont.intervalIntegrable_of_Icc hab

  have hPointwise :
      ∀ r ∈ Set.Icc (a : ℝ) (b : ℝ),
        F r ≤ G r := by
    intro r hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau :=
      hSub hr

    have h :=
      inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifference_le_energy_add_approximationError
        hNS ht hEnd hE hTail htauR
        φ a ⟨r, hrTau⟩ hε hApprox

    dsimp only [F, G, D, Da]

    rw [
      h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed_apply_of_mem
        hNS ht hEnd hE hTail htauR hrTau,
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
        hNS ht hEnd hE hTail hrTau
    ]

    exact h

  change
    (∫ r in (a : ℝ)..(b : ℝ), F r)
      ≤
    ∫ r in (a : ℝ)..(b : ℝ), G r

  exact
    intervalIntegral.integral_mono_on
      hab hFInt hGInt hPointwise

/-- One ordered subinterval admits the same approximate linear energy increment
under only the scalar old weak-FTC interface. -/
theorem exists_divergenceFreeWeakTest_selectedOldDifference_approximateEnergyIncrement_of_allProjectedRHSWeakFTC
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
    (hab : (a : ℝ) ≤ (b : ℝ))
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
        ≤
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
      ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail b
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
              (one_pos : (0 : ℝ) < 1)
              hNS ht hEnd hE hTail a‖ := by
  obtain ⟨φ, hφ, hApprox, _hWeak, hEndpointError⟩ :=
    exists_divergenceFreeWeakTest_selectedOldDifference_leftApproximation_twoTime_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail htauR hWeakFTC
      a b hε

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

  let F : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        Φ
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r)

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

  have hEndpointUpper :
      inner ℝ Da (Db - Da)
        ≤
      (∫ r in (a : ℝ)..(b : ℝ), F r)
        +
      ε * ‖Db - Da‖ := by
    have hUpper :=
      (abs_le.mp hEndpointError).2

    dsimp only [Da, Db, Φ, F] at hUpper ⊢
    linarith

  have hIntegralUpper :
      (∫ r in (a : ℝ)..(b : ℝ), F r)
        ≤
      ∫ r in (a : ℝ)..(b : ℝ), G r := by
    dsimp only [F, G, Φ, Da]

    exact
      intervalIntegral_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifference_le_energy_add_approximationError_of_allProjectedRHSWeakFTC
        hNS ht htau hEnd hE hTail htauR hWeakFTC
        φ hφ a b hab hε hApprox

  refine ⟨φ, hφ, hApprox, ?_⟩

  change
    inner ℝ Da (Db - Da)
      ≤
    (∫ r in (a : ℝ)..(b : ℝ), G r)
      +
    ε * ‖Db - Da‖

  exact
    hEndpointUpper.trans
      (add_le_add_left hIntegralUpper _)

/-- Local squared-energy increment from scalar old weak FTC. -/
theorem norm_sq_selectedOldDifference_sub_le_approximateEnergyIncrement_of_allProjectedRHSWeakFTC
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
    exists_divergenceFreeWeakTest_selectedOldDifference_approximateEnergyIncrement_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail htauR hWeakFTC
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

/-- Ambient-real endpoint form of the scalar-weak-FTC local squared-energy
increment. -/
theorem norm_sq_selectedOldDifferenceReal_sub_le_approximateEnergyIncrement_of_mem_of_allProjectedRHSWeakFTC
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
    norm_sq_selectedOldDifference_sub_le_approximateEnergyIncrement_of_allProjectedRHSWeakFTC
      hNS ht htau hEnd hE hTail htauR hWeakFTC
      ⟨a, ha⟩ ⟨b, hb⟩ hab hε

end

end Euclidean
end Bridge
end PrimeTensor
