import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitude

/-!
# Continuation criteria from the canonical full-tail H³ balance amplitude

The canonical branch-free balance amplitude is

`B(t) = max (-E'(t)) (-T_H3(t))`.

Under hypothetical nonextension the preceding file proves three full-tail
obstructions:

* `B(t) -> +∞`;
* `(T-t) B(t) -> +∞`;
* `B(t) / E(t) -> +∞`.

Each obstruction immediately yields a positive continuation criterion.  If one
finite upper threshold recurs arbitrarily late for any one of these three
quantities, then smooth continuation across `T` must exist.

These criteria remain neutral about how the exact H³ balance is split between
energy decay and adverse transport.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A reusable contradiction principle for an `atTop` quantity on the left
terminal neighborhood: if it tends to `+∞`, one fixed finite upper threshold
cannot recur arbitrarily late. -/
private theorem recurring_lt_contradicts_tendsto_atTop_nhdsLT
    {F : ℝ → ℝ}
    {T a M : ℝ}
    (haT : a < T)
    (hTop : Tendsto F (𝓝[<] T) atTop)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T ∧
          F t < M) :
    False := by
  have hEventually :
      {t : ℝ | M ≤ F t} ∈ 𝓝[<] T :=
    hTop.eventually
      (eventually_ge_atTop M)

  obtain ⟨d, hdT, hdSubset⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset).1
      hEventually

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        haT

  let c : ℝ := max d b

  have hc : c ∈ Set.Ioo a T := by
    constructor
    · dsimp only [c]
      exact
        lt_of_lt_of_le
          hb.1
          (le_max_right _ _)
    · dsimp only [c]
      exact
        max_lt
          hdT
          hb.2

  obtain ⟨t, ht, hUpper⟩ :=
    hRecurring c hc

  have hMaxLt : max d b < t := by
    simpa only [c] using ht.1

  have htD : t ∈ Set.Ioo d T := by
    constructor
    · exact
        lt_of_le_of_lt
          (le_max_left d b)
          hMaxLt
    · exact ht.2

  have hLower : M ≤ F t :=
    hdSubset htD

  exact
    (not_lt_of_ge hLower)
      hUpper

/-- If the raw canonical balance amplitude is below one finite threshold at
arbitrarily late strict times, then the H³ path extends smoothly across `T`. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitude_bounded_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T ∧
          h3TerminalBalanceAmplitudeAt u t < M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension

  exact
    recurring_lt_contradicts_tendsto_atTop_nhdsLT
      hClass.terminal_start.2
      (h3TerminalBalanceAmplitudeAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass)
      hRecurring

/-- If the physical clock `(T-t) B(t)` of the canonical balance amplitude is
below one finite threshold at arbitrarily late strict times, then the H³ path
extends smoothly across `T`. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitudePhysicalClock_bounded_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T ∧
          (T - t) * h3TerminalBalanceAmplitudeAt u t < M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension

  exact
    recurring_lt_contradicts_tendsto_atTop_nhdsLT
      hClass.terminal_start.2
      (h3TerminalBalanceAmplitudePhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass)
      hRecurring

/-- If the full-energy normalized canonical balance amplitude `B(t) / E(t)` is
below one finite threshold at arbitrarily late strict times, then the H³ path
extends smoothly across `T`. -/
theorem exists_smoothContinuationExtension_of_balanceAmplitudeNormalizedRate_bounded_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hRecurring :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T ∧
          h3TerminalBalanceAmplitudeAt u t /
              velocityH3EnergyAt u t < M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension

  exact
    recurring_lt_contradicts_tendsto_atTop_nhdsLT
      hClass.terminal_start.2
      (h3TerminalBalanceAmplitudeNormalizedRate_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3 hNoExtension hClass)
      hRecurring

end

end Euclidean
end Bridge
end PrimeTensor
