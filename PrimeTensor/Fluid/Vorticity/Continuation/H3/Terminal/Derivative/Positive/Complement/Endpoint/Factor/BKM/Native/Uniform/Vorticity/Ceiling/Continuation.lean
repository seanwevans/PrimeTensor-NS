import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Uniform.Ceiling.Continuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Native.Vorticity.Synchronization

/-!
# A uniform indexed vorticity ceiling forces continuation

Under hypothetical nonextension, every admissible vorticity envelope
diverges in magnitude on each quantitative native witness. Such a
witness can be cofinally reindexed so that its envelope magnitude
dominates the new index. Therefore an eventual constant bound for
`(1 + |g(τ n)|)² / (n+1)` on *every* quantitative native witness is
incompatible with hypothetical nonextension. The coefficient is
allowed to depend on the witness; reindexing still contradicts it.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- If an envelope diverges on one quantitative native witness, its
cofinal reindexings rule out a uniform eventual normalized envelope
ceiling over all quantitative native witnesses. -/
theorem not_nativeUniformVorticityCeiling_of_envelopeTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ} {g : ℝ → ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hEnvelopeTop : Tendsto (fun n : ℕ => |g (τ n)|) atTop atTop) :
    ¬ H3TerminalNativeUniformVorticityCeiling u b T g := by
  classical
  intro hCeiling
  have hPick : ∀ n : ℕ, ∃ j : ℕ,
      n ≤ j ∧
      (n : ℝ) + 1 <
        (1 + |g (τ j)|) ^ 2 / ((n : ℝ) + 1) := by
    intro n
    have hDenPos : 0 < (n : ℝ) + 1 := by positivity
    have hLarge : ∀ᶠ j : ℕ in atTop,
        (n : ℝ) + 1 < |g (τ j)| :=
      hEnvelopeTop.eventually
        (eventually_gt_atTop ((n : ℝ) + 1))
    obtain ⟨j, hjIndex, hjMagnitude⟩ :=
      ((eventually_ge_atTop n).and hLarge).exists
    have hDifference :
        0 < (1 + |g (τ j)|) - ((n : ℝ) + 1) := by
      linarith
    have hSum :
        0 < (1 + |g (τ j)|) + ((n : ℝ) + 1) := by
      have hAbs : 0 ≤ |g (τ j)| := abs_nonneg _
      linarith
    have hSquare :
        ((n : ℝ) + 1) * ((n : ℝ) + 1) <
          (1 + |g (τ j)|) ^ 2 := by
      nlinarith [mul_pos hDifference hSum]
    refine ⟨j, hjIndex, ?_⟩
    exact (lt_div_iff₀ hDenPos).2 hSquare
  choose k hk using hPick
  have hCofinal : ∀ n : ℕ, n ≤ k n := fun n => (hk n).1
  have hReindexed : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient
        (fun n => τ (k n)) (fun n => y (k n)) :=
    positiveGrowth_quantitativeNativeData_comp_cofinal hData hCofinal
  obtain ⟨C, hUpper⟩ := hCeiling p sCurl sGradient
    (fun n => τ (k n)) (fun n => y (k n)) hReindexed
  obtain ⟨N, hCN⟩ := exists_nat_gt C
  obtain ⟨n, hnIndex, hnUpper⟩ :=
    ((eventually_ge_atTop N).and hUpper).exists
  have hnCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnIndex
  have hnFast := (hk n).2
  linarith

/-- A vorticity envelope under hypothetical nonextension excludes
the uniform normalized ceiling on every native witness of a subtail. -/
theorem not_nativeUniformVorticityCeiling_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) :
    ¬ H3TerminalNativeUniformVorticityCeiling u b T g := by
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    exists_terminal_positiveGrowth_quantitativeNativeData_on_subtail
      hH3 hNoExtension hClass hb
  have hEnvelopeTop :
      Tendsto (fun n : ℕ => |g (τ n)|) atTop atTop :=
    positiveGrowth_nativeWitness_vorticityEnvelope_atTop
      hH3 hNoExtension hClass hb hg hData
  exact not_nativeUniformVorticityCeiling_of_envelopeTop
    hData hEnvelopeTop

/-- A normalized vorticity ceiling quantified over every native
witness already yields smooth continuation. -/
theorem smoothContinuationExtension_of_nativeUniformVorticityCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hCeiling : H3TerminalNativeUniformVorticityCeiling u b T g) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  exact (not_nativeUniformVorticityCeiling_of_noH3PathExtension
    hH3 hNoExtension hClass hb hg) hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
