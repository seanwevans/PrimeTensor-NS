import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.Open.L2.Continuity
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact restart-slab bounds for selected forcing radial Fourier L² states

The selected forcing radial Fourier `L²` path is now strongly continuous on
the whole strict restart interval at every natural radial order.  Therefore its
restriction to any compact positive restart slab has one finite norm ceiling.

This file records that compactness consequence in the exact quotient-safe form
needed by the remaining order-two velocity argument.

The statement is generic in the radial order `m`.  In particular:

* `m = 0` supplies an unweighted forcing `L²` ceiling for the midpoint-history
  estimate;
* `m = 5` supplies the weighted forcing `L²` ceiling for the terminal tail;
* `m = 6` is available unchanged for the later order-three argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingRadialCompactL2Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The direct open-restart radial forcing path has a finite norm ceiling on
every compact slab strictly contained in the positive restart interval. -/
theorem exists_norm_bound_h3SelectedRestartForcingRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ s : Set.Icc a b,
        ‖h3SelectedRestartForcingRadialFourierL2OnRestartRadius
            m hν U₀ hA hU₀
            ⟨(s : ℝ),
              lt_of_lt_of_le ha s.property.1,
              lt_of_le_of_lt s.property.2 hbR⟩
            i‖
          ≤ C := by

  let toOpen :
      Set.Icc a b →
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) :=
    fun s =>
      ⟨(s : ℝ),
        lt_of_lt_of_le ha s.property.1,
        lt_of_le_of_lt s.property.2 hbR⟩

  have hToOpen : Continuous toOpen := by
    dsimp only [toOpen]
    exact
      Continuous.subtype_mk
        continuous_subtype_val
        _

  let F : Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3SelectedRestartForcingRadialFourierL2OnRestartRadius
        m hν U₀ hA hU₀ (toOpen s) i

  have hF : Continuous F := by
    dsimp only [F]
    exact
      (continuous_h3SelectedRestartForcingRadialFourierL2OnRestartRadius
        m hν U₀ hA hU₀ i).comp hToOpen

  have hCompact :
      IsCompact (Set.univ : Set (Set.Icc a b)) :=
    isCompact_univ

  obtain ⟨C, hC⟩ :=
    hCompact.exists_bound_of_continuousOn
      hF.continuousOn

  let C0 : ℝ := max C 0

  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact le_max_right C 0

  refine ⟨C0, hC0, ?_⟩

  intro s

  have hRaw :
      ‖F s‖ ≤ C :=
    hC s (Set.mem_univ s)

  have hBound :
      ‖F s‖ ≤ C0 :=
    hRaw.trans (le_max_left C 0)

  simpa only [F, toOpen] using hBound

/-- Unweighted specialization used to bound the earlier Duhamel history. -/
theorem exists_norm_bound_h3SelectedRestartForcingRawFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ s : Set.Icc a b,
        ‖h3SelectedRestartForcingRadialFourierL2OnRestartRadius
            0 hν U₀ hA hU₀
            ⟨(s : ℝ),
              lt_of_lt_of_le ha s.property.1,
              lt_of_le_of_lt s.property.2 hbR⟩
            i‖
          ≤ C :=
  exists_norm_bound_h3SelectedRestartForcingRadialFourierL2OnCompact
    0 hν U₀ hA hU₀ ha hbR i

/-- Fifth-radial specialization used for the terminal portion of the selected
Duhamel integral. -/
theorem exists_norm_bound_h3SelectedRestartForcingFifthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ s : Set.Icc a b,
        ‖h3SelectedRestartForcingRadialFourierL2OnRestartRadius
            5 hν U₀ hA hU₀
            ⟨(s : ℝ),
              lt_of_lt_of_le ha s.property.1,
              lt_of_le_of_lt s.property.2 hbR⟩
            i‖
          ≤ C :=
  exists_norm_bound_h3SelectedRestartForcingRadialFourierL2OnCompact
    5 hν U₀ hA hU₀ ha hbR i

/-- Sixth-radial specialization reserved for the order-three continuation. -/
theorem exists_norm_bound_h3SelectedRestartForcingSixthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ s : Set.Icc a b,
        ‖h3SelectedRestartForcingRadialFourierL2OnRestartRadius
            6 hν U₀ hA hU₀
            ⟨(s : ℝ),
              lt_of_lt_of_le ha s.property.1,
              lt_of_le_of_lt s.property.2 hbR⟩
            i‖
          ≤ C :=
  exists_norm_bound_h3SelectedRestartForcingRadialFourierL2OnCompact
    6 hν U₀ hA hU₀ ha hbR i

end

end Euclidean
end Bridge
end PrimeTensor
