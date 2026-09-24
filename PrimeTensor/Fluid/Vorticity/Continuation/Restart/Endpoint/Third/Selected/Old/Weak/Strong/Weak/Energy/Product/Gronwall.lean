import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Product.Exact
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.L2.Difference.Gronwall
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall and physical agreement from temporal product integrability

The product-family weak-energy route now gives the exact inequality

    ‖D(q)‖² ≤ K ∫₀^q ‖D(r)‖² dr,

where `K = 6 * h3PreterminalSelectedWeakStrongGradientEnvelope E`.

Define the cumulative scalar energy

    H(s) = ∫₀^s ‖D(r)‖² dr.

The pressure-free Lipschitz theorem gives continuity of `D`, hence the
fundamental theorem of calculus gives `H' = ‖D‖²`.  The exact relative-energy
inequality becomes the scalar Grönwall inequality

    |H'| ≤ K |H|,

with `H(0)=0`.  Therefore `H = 0`, hence `D = 0`.

The existing concrete `L²` representation bridge then upgrades this to
pointwise selected--old physical agreement and decoder agreement on every
strictly positive elapsed time in the fixed interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyProductGronwall
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact product-integrable weak relative-energy inequality forces the
ambient-real selected--old physical difference to vanish. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_eq_zero_of_allTemporalProductIntegrable
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
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
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

  have hDCont :
      ContinuousOn D (Set.Icc (0 : ℝ) tau) := by
    dsimp only [D]
    exact
      continuousOn_h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct

  have heCont :
      ContinuousOn e (Set.Icc (0 : ℝ) tau) := by
    dsimp only [e]
    exact
      (continuous_norm.comp_continuousOn hDCont).pow 2

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
      norm_sq_selectedOldDifferenceReal_le_energyIntegral_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct hs

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

/-- Subtype form of product-integrable weak-energy uniqueness. -/
theorem h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_allTemporalProductIntegrable
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
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail q
      =
    0 := by
  have h :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_eq_zero_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct q.property

  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail q.property
  ] at h

  exact h

/-- Product-integrable weak-energy uniqueness upgrades to pointwise selected/old
physical agreement at one positive elapsed time. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_allTemporalProductIntegrable
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
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      (one_pos : (0 : ℝ) < 1)
      q
      hNS ht hE hTail := by
  let qClosed : Set.Icc (0 : ℝ) tau :=
    ⟨q, hq.1.le, hq.2⟩

  have hZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail qClosed
        =
      0 := by
    exact
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct qClosed

  have hqR :
      (qClosed : ℝ)
        ≤
      h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    simpa only [qClosed] using hq.2.trans htauR

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2Difference_eq_zero
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail
      qClosed
      (by simpa only [qClosed] using hq.1)
      hqR
      hZero

/-- Fixed-interval selected/old physical agreement under only temporal product
integrability. -/
theorem h3PreterminalSelectedPhysicalAgreementOnElapsed_of_allTemporalProductIntegrable
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
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail) :
    ∀ q : Set.Ioc (0 : ℝ) tau,
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail := by
  intro q

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_allTemporalProductIntegrable
      hNS ht htau hEnd hE hTail htauR hProduct q.property

/-- Fixed-interval selected decoder agreement under only temporal product
integrability. -/
theorem h3PreterminalSelectedDecoderAgreementOnElapsed_of_allTemporalProductIntegrable
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
    (hProduct :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail) :
    ∀ q : Set.Ioc (0 : ℝ) tau,
      H3PreterminalSelectedDecoderAgreesAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail := by
  intro q

  exact
    h3PreterminalSelectedDecoderAgreesAt_of_physicalAgreement
      (one_pos : (0 : ℝ) < 1)
      (q : ℝ)
      hNS ht hE hTail
      (h3PreterminalSelectedPhysicalAgreementOnElapsed_of_allTemporalProductIntegrable
        hNS ht htau hEnd hE hTail htauR hProduct q)

end

end Euclidean
end Bridge
end PrimeTensor
