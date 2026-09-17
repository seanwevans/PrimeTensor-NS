import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyEpsilonLimit
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall closure of the derivative-free selected--old weak energy argument

The exact relative-energy inequality is now

    ‖D(q)‖² ≤ K ∫₀^q ‖D(r)‖² dr,

with

    K = 6 * h3PreterminalSelectedWeakStrongGradientEnvelope E.

Instead of differentiating the old velocity branch, define the scalar
cumulative energy

    H(s) = ∫₀^s ‖D(r)‖² dr.

The already-proved strong continuity of `D` gives the fundamental theorem of
calculus

    H'(s) = ‖D(s)‖².

Hence the relative-energy inequality becomes the ordinary scalar differential
inequality

    |H'(s)| ≤ K |H(s)|,

while `H(0)=0`.  Mathlib's continuous Grönwall theorem therefore forces
`H ≡ 0`, and the original energy inequality then forces `D ≡ 0`.

This closes weak--strong uniqueness without any strong time derivative of the
old preterminal branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyGronwall
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact weak relative-energy inequality forces the selected--old
physical difference to vanish at every elapsed time in `[0,tau]`. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_eq_zero_of_weakEnergy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail q
      =
    0 := by
  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let e : ℝ → ℝ :=
    fun r : ℝ => ‖D r‖ ^ 2

  let H : ℝ → ℝ :=
    fun s : ℝ => ∫ r in (0 : ℝ)..s, e r

  let K : ℝ :=
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E

  have heCont :
      ContinuousOn e (Set.Icc (0 : ℝ) tau) := by
    dsimp only [e, D]
    exact
      continuousOn_norm_sq_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allPressureDefect
        hNS ht htau hEnd hE hTail hPressure

  have hHDerivIcc :
      ∀ s ∈ Set.Icc (0 : ℝ) tau,
        HasDerivWithinAt
          H
          (e s)
          (Set.Icc (0 : ℝ) tau)
          s := by
    intro s hs

    letI : Fact (s ∈ Set.Icc (0 : ℝ) tau) :=
      ⟨hs⟩

    have hInt :
        IntervalIntegrable
          e
          volume
          (0 : ℝ)
          s := by
      exact
        (heCont.mono
          (Set.Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc
            hs.1

    have hMeas :
        StronglyMeasurableAtFilter
          e
          (𝓝[Set.Icc (0 : ℝ) tau] s) := by
      exact
        heCont.stronglyMeasurableAtFilter_nhdsWithin
          measurableSet_Icc s

    have hCont :
        ContinuousWithinAt
          e
          (Set.Icc (0 : ℝ) tau)
          s :=
      heCont.continuousWithinAt hs

    dsimp only [H]

    exact
      intervalIntegral.integral_hasDerivWithinAt_right
        hInt hMeas hCont

  have hHCont :
      ContinuousOn
        H
        (Set.Icc (0 : ℝ) tau) := by
    intro s hs
    exact
      (hHDerivIcc s hs).continuousWithinAt

  have hHDerivRight :
      ∀ s ∈ Set.Ico (0 : ℝ) tau,
        HasDerivWithinAt
          H
          (e s)
          (Set.Ici s)
          s := by
    intro s hs

    have hsClosed :
        s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1, le_of_lt hs.2⟩

    have hBase :=
      hHDerivIcc s hsClosed

    have hSmall :
        HasDerivWithinAt
          H
          (e s)
          (Set.Icc s tau)
          s := by
      exact
        hBase.mono
          (by
            intro x hx
            exact
              ⟨hs.1.trans hx.1, hx.2⟩)

    have hLocal :
        Set.Icc s tau
          =ᶠ[𝓝 s]
        Set.Ici s := by
      filter_upwards [Iio_mem_nhds hs.2] with x hx

      have hxt : x < tau :=
        Set.mem_Iio.mp hx

      apply propext
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, le_of_lt hxt⟩

    exact
      hSmall.congr_set hLocal

  have hHZero :
      H 0 = 0 := by
    simp [H]

  have hHNonneg :
      ∀ s ∈ Set.Icc (0 : ℝ) tau,
        0 ≤ H s := by
    intro s hs
    dsimp only [H]
    exact
      intervalIntegral.integral_nonneg
        hs.1
        (fun r _hr => sq_nonneg ‖D r‖)

  have hEnergy :
      ∀ s ∈ Set.Icc (0 : ℝ) tau,
        e s ≤ K * H s := by
    intro s hs

    have h :=
      norm_sq_selectedOldDifferenceReal_le_energyIntegral
        hNS ht htau hEnd hE hTail htauR hPressure hs

    simpa only [e, D, H, K] using h

  have hDerivBound :
      ∀ s ∈ Set.Ico (0 : ℝ) tau,
        ‖e s‖ ≤ K * ‖H s‖ := by
    intro s hs

    have hsClosed :
        s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hs.1, le_of_lt hs.2⟩

    have he0 :
        0 ≤ e s := by
      dsimp only [e]
      exact sq_nonneg ‖D s‖

    have hH0 :
        0 ≤ H s :=
      hHNonneg s hsClosed

    have h :=
      hEnergy s hsClosed

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg he0,
      abs_of_nonneg hH0
    ] using h

  have hHVanishing :
      ∀ s ∈ Set.Icc (0 : ℝ) tau,
        H s = 0 := by
    exact
      eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
        hHCont hHDerivRight hHZero hDerivBound

  have hEq :
      e q = 0 := by
    have hqEnergy :=
      hEnergy q hq

    have hqH :=
      hHVanishing q hq

    rw [hqH, mul_zero] at hqEnergy

    have heq0 :
        0 ≤ e q := by
      dsimp only [e]
      exact sq_nonneg ‖D q‖

    exact
      le_antisymm hqEnergy heq0

  have hNormSq :
      ‖D q‖ ^ 2 = 0 := by
    simpa only [e] using hEq

  have hNorm :
      ‖D q‖ = 0 := by
    nlinarith [norm_nonneg (D q)]

  have hDZero :
      D q = 0 :=
    norm_eq_zero.mp hNorm

  simpa only [D] using hDZero

/-- Subtype form of the same weak-energy uniqueness conclusion. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_weakEnergy
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
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q
      =
    0 := by
  have h :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_eq_zero_of_weakEnergy
      hNS ht htau hEnd hE hTail htauR hPressure q.property

  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail q.property
  ] at h

  exact h

end

end Euclidean
end Bridge
end PrimeTensor
