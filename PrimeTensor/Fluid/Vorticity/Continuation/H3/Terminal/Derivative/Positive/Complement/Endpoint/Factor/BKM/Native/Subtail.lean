import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Oriented.Ratio.Exponential.Continuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Reindex.Cascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Quantitative.Native.Cascade

/-!
# Quantitative native cascade on an arbitrary late subtail

A native positive-growth sequence tending to the terminal time eventually
lies above every fixed earlier time `b < T`. A cofinal reindexing with
`n ≤ m n` preserves all quantitative thresholds and directional escapes,
while moving its time points into the later interval `Ioo b T`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The entire quantitative native cascade may be placed on any later
subtail while preserving its indexed lower bounds. -/
theorem positiveGrowth_quantitativeNativeData_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hb : b < T) :
    ∃ m : ℕ → ℕ,
      (∀ n : ℕ, n ≤ m n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) := by
  have hCopy := hData
  obtain ⟨_, hTau, _, _, _, _, _, _, _⟩ := hCopy
  have hEventually : ∀ᶠ i : ℕ in atTop, b < τ i :=
    hTau.eventually (Ioi_mem_nhds hb)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hEventually
  let m : ℕ → ℕ := fun n => max n N
  have hm : ∀ n : ℕ, n ≤ m n :=
    fun n => le_max_left n N
  have hTail : ∀ n : ℕ, b < τ (m n) := by
    intro n
    exact hN (m n) (le_max_right n N)
  have hRefined :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) :=
    positiveGrowth_quantitativeNativeData_comp_cofinal hData hm
  obtain ⟨hAt, hTau', hEnergy, hDiss, hTransport, hFrequency,
    hCurlEscape, hGradientEscape, _⟩ := hRefined
  have hAtSub : ∀ n : ℕ,
      (fun i => τ (m i)) n ∈ Set.Ioo b T ∧
      (fun i => τ (m i)) n ∈
        Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
      (n : ℝ) < deriv (velocityH3EnergyAt u) (τ (m n)) ∧
      (n : ℝ) <
        h3TerminalOrientedValue sCurl
          (PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeCurlForPair u p (τ (m n)) (y (m n)))) ∧
      (n : ℝ) <
        h3TerminalOrientedValue sGradient
          (PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeGradientForPair u p (τ (m n)) (y (m n)))) := by
    intro n
    exact ⟨⟨hTail n, (hAt n).1.2⟩, (hAt n).2⟩
  have hDirectionalSub :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u b T p sCurl sGradient := by
    refine ⟨(fun n => τ (m n)), (fun n => y (m n)), ?_,
      hTau', hCurlEscape, hGradientEscape⟩
    intro n
    exact ⟨(hAtSub n).1, (hAtSub n).2.1,
      (hAtSub n).2.2.2.1, (hAtSub n).2.2.2.2⟩
  refine ⟨m, hm, ?_⟩
  exact ⟨hAtSub,
    hTau', hEnergy, hDiss, hTransport, hFrequency,
    hCurlEscape, hGradientEscape, hDirectionalSub⟩

/-- Under hypothetical nonextension, a complete quantitative native
positive-growth cascade exists on any chosen strict terminal subtail. -/
theorem exists_terminal_positiveGrowth_quantitativeNativeData_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ p : H3TerminalCurlGradientPair,
      ∃ sCurl sGradient : H3TerminalOrientation,
        ∃ τ : ℕ → ℝ,
          ∃ y : ℕ → Point3,
            H3TerminalPositiveGrowthQuantitativeNativeData
              u b T p sCurl sGradient τ y := by
  obtain ⟨p, sCurl, sGradient, τ, y,
      hAt, hTau, hEnergy, hDiss, hTransport, hFrequency,
      hCurlEscape, hGradientEscape, hDirectional⟩ :=
    exists_terminal_positiveGrowth_fullCascade_quantitativeNativeDoubleEscape_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  have hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y :=
    ⟨hAt, hTau, hEnergy, hDiss, hTransport, hFrequency,
      hCurlEscape, hGradientEscape, hDirectional⟩
  obtain ⟨m, _, hTail⟩ :=
    positiveGrowth_quantitativeNativeData_on_subtail hData hb.2
  exact ⟨p, sCurl, sGradient,
    (fun n => τ (m n)), (fun n => y (m n)), hTail⟩

end

end Euclidean
end Bridge
end PrimeTensor
