import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyApproximation

/-!
# Ordered interval weak-energy increment

The self-test approximation is now pointwise in time.  This file integrates
that estimate over one ordered subinterval `[a,b]`.

For an admissible weak-test approximant `Phi` with

    dist (D(a)) Phi < eps,

the preceding file gives, pointwise,

    <Phi,RDelta(r)>
      <= 3 B(E) ‖D(r)‖²
         + (eps + ‖D(a)-D(r)‖) 6 C(E).

Strong continuity of `D` makes the right-hand side interval-integrable.
The already-established scalar weak pairing is interval-integrable on every
subinterval, so interval-integral monotonicity gives the integrated estimate.

Combining this with the endpoint self-test error yields a genuine approximate
energy increment:

    <D(a),D(b)-D(a)>
      <= integral_a^b G_{a,eps}(r) dr
         + eps ‖D(b)-D(a)‖.

This is the exact local estimate to sum over a partition.  No strong old
`L²` derivative or endpoint-continuity hypothesis is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyInterval
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Integrate the pointwise weak-energy estimate for one fixed divergence-free
weak-test approximant over an ordered elapsed subinterval. -/
theorem intervalIntegral_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifference_le_energy_add_approximationError
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
      IntervalIntegrable
        F
        volume
        (0 : ℝ)
        (b : ℝ) := by
    dsimp only [F]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allPressureDefect
        hNS ht htau hEnd hE hTail htauR hPressure
        φ hφ b

  have hFInt :
      IntervalIntegrable
        F
        volume
        (a : ℝ)
        (b : ℝ) := by
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
      ContinuousOn
        D
        (Set.Icc (a : ℝ) (b : ℝ)) := by
    dsimp only [D]

    exact
      (continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allPressureDefect
        hNS ht htau hEnd hE hTail hPressure).mono hSub

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
      ContinuousOn
        G
        (Set.Icc (a : ℝ) (b : ℝ)) := by
    dsimp only [G]
    exact hEnergyCont.add hApproxErrorCont

  have hGInt :
      IntervalIntegrable
        G
        volume
        (a : ℝ)
        (b : ℝ) :=
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

/-- For every ordered subinterval and every positive approximation tolerance,
there is an admissible self-test approximation giving a genuine scalar
approximate energy increment inequality. -/
theorem exists_divergenceFreeWeakTest_selectedOldDifference_approximateEnergyIncrement
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
    exists_divergenceFreeWeakTest_selectedOldDifference_leftApproximation_twoTime
      hNS ht htau hEnd hE hTail htauR hPressure
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
      intervalIntegral_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifference_le_energy_add_approximationError
        hNS ht htau hEnd hE hTail htauR hPressure
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
      (add_le_add
        hIntegralUpper
        (le_refl (ε * ‖Db - Da‖)))

end

end Euclidean
end Bridge
end PrimeTensor
