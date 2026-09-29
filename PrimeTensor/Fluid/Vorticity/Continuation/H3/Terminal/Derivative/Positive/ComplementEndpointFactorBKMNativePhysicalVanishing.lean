import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativePhysicalCubicThreshold

/-!
# A vanishing physical clock criterion

An upper bound for raw dissipation whose physical cubic terminal
quantity tends to zero rules out the necessary rate on a hypothetical
nonextending path. This criterion concerns all times on a terminal
neighborhood, so selecting or reindexing a native witness cannot
change its meaning.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A physical raw dissipation ceiling with vanishing cubic terminal
quantity forces smooth continuation. -/
theorem smoothContinuationExtension_of_physicalRawCeiling_vanishingCubic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {F : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeiling : H3TerminalPhysicalRawDissipationCeiling u b T F)
    (hVanishing : Tendsto
      (fun t : ℝ =>
        h3NativePhysicalClockCubicCoefficient u b *
          (T - t) ^ 2 * (F (T - t)) ^ 3)
      (𝓝[<] T) (𝓝 (0 : ℝ))) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨c, hc, hThreshold⟩ :=
    exists_terminalTail_physicalRawCeiling_cubicRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb hCeiling
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    exists_terminal_positiveGrowth_quantitativeNativeData_on_subtail
      hH3 hNoExtension hClass hb
  have hTauLT : Tendsto τ atTop (𝓝[<] T) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hData.2.1,
        Eventually.of_forall (fun n => (hData.1 n).1.2)⟩
  have hBelow : ∀ᶠ n : ℕ in atTop,
      h3NativePhysicalClockCubicCoefficient u b *
        (T - τ n) ^ 2 * (F (T - τ n)) ^ 3 < 1 :=
    (hVanishing.comp hTauLT).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hInTail : ∀ᶠ n : ℕ in atTop, τ n ∈ Set.Ioo c T := by
    filter_upwards [hData.2.1.eventually (Ioi_mem_nhds hc.2)] with n hn
    exact ⟨hn, (hData.1 n).1.2⟩
  obtain ⟨n, hnTail, hnBelow⟩ := (hInTail.and hBelow).exists
  exact (not_lt_of_ge (hThreshold (τ n) hnTail)) hnBelow

end

end Euclidean
end Bridge
end PrimeTensor
