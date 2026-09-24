import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Physical.L2.Evolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Selected restart: strong physical L² time derivative

The selected physical `L²` evolution has now been upgraded from compact-test
weak FTC to an exact Hilbert-valued Bochner identity.  Since its projected RHS
is strongly continuous on every closed elapsed interval inside the restart
radius, the Banach-valued fundamental theorem of calculus applies directly.

Thus the selected physical velocity path has the genuine strong derivative

    d/dq S(q) = R(q)

at every strict elapsed interior point.  No additional temporal regularity or
weak-density hypothesis remains at this stage.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPhysicalL2Derivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected unit-viscosity physical `L²` velocity path has the projected
physical RHS as its genuine strong derivative at every strict elapsed interior
point. -/
theorem h3PreterminalSelectedVelocityPhysicalL2HilbertAt_hasDerivAt_unit
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivAt
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR q)
      q := by
  let S : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
      hNS ht hE hTail htauR

  have hGContinuous :
      ContinuousOn G (Set.Icc (0 : ℝ) tau) := by
    dsimp only [G]
    exact
      continuousOn_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht htau hE hTail htauR

  have hGAt :
      ∀ y ∈ Set.Ioo (0 : ℝ) tau,
        ContinuousAt G y := by
    intro y hy
    exact
      ContinuousWithinAt.continuousAt
        (hGContinuous y ⟨hy.1.le, hy.2.le⟩)
        (Icc_mem_nhds hy.1 hy.2)

  have hSub :
      Set.Icc (0 : ℝ) q
        ⊆ Set.Icc (0 : ℝ) tau := by
    intro y hy
    exact
      ⟨hy.1, hy.2.trans hq.2.le⟩

  have hGIntegrable :
      IntervalIntegrable G volume (0 : ℝ) q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hq.1.le]
    exact hGContinuous.mono hSub

  have hGMeasurable :
      StronglyMeasurableAtFilter
        G
        (𝓝 q)
        (volume : Measure ℝ) := by
    exact
      ContinuousAt.stronglyMeasurableAtFilter
        (μ := (volume : Measure ℝ))
        isOpen_Ioo
        hGAt
        q
        hq

  have hIntegralDerivative :
      HasDerivAt
        (fun y : ℝ =>
          ∫ s in (0 : ℝ)..y, G s)
        (G q)
        q :=
    intervalIntegral.integral_hasDerivAt_right
      hGIntegrable
      hGMeasurable
      (hGAt q hq)

  let J : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    fun y =>
      S 0 + ∫ s in (0 : ℝ)..y, G s

  have hJDerivative :
      HasDerivAt J (G q) q := by
    dsimp only [J]
    exact hIntegralDerivative.const_add (S 0)

  have hJEq :
      ∀ y ∈ Set.Icc (0 : ℝ) tau,
        J y = S y := by
    intro y hy

    have hEvolution :=
      h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed_eq_BochnerProjectedRHSTo
        hNS ht htau hE hTail htauR
        (⟨y, hy⟩ : Set.Icc (0 : ℝ) tau)

    dsimp only [J, S, G]
    unfold
      h3PreterminalSelectedUnitVelocityIncrementPhysicalL2HilbertOnElapsed
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2BochnerIntegralTo
      at hEvolution

    rw [← hEvolution]
    abel

  have hIccNeighborhood :
      Set.Icc (0 : ℝ) tau ∈ 𝓝 q :=
    Icc_mem_nhds hq.1 hq.2

  have hEventuallyEq :
      S =ᶠ[𝓝 q] J := by
    filter_upwards [hIccNeighborhood] with y hy
    exact (hJEq y hy).symm

  have hSDerivative :
      HasDerivAt S (G q) q :=
    hJDerivative.congr_of_eventuallyEq hEventuallyEq

  dsimp only [S, G] at hSDerivative ⊢
  exact hSDerivative

/-- Right-restricted form of the selected strong physical `L²` derivative. -/
theorem h3PreterminalSelectedVelocityPhysicalL2HilbertAt_hasDerivWithinAt_right_unit
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivWithinAt
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR q)
      (Set.Ioi q)
      q := by
  exact
    (h3PreterminalSelectedVelocityPhysicalL2HilbertAt_hasDerivAt_unit
      hNS ht htau hE hTail htauR hq).hasDerivWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
