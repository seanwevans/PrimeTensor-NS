import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalSequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFixedActualVorticityRate

/-!
# Fixed actual-vorticity component on the pure physical escape sequence

The pure physical minimal-vorticity escape sequence carries actual-vorticity
blowup at selected spatial points, but its maximizing component may vary with
the index.  Since there are only three physical vorticity components, a cofinal
subsequence freezes one component while retaining the physical terminal
localization and minimal-envelope escape.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Pure physical-time terminal escape with one fixed actual vorticity
component. -/
def H3TerminalMinimalVorticityPhysicalFixedComponentEscapeSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∃ i : Fin 3,
    ∃ τ : ℕ → ℝ,
      ∃ z : ℕ → Point3,
        (∀ n : ℕ,
          τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
            ∧
          (n : ℝ) < h3MinimalVorticityEnvelopeAt u (τ n))
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
          atTop atTop
          ∧
        (∀ n : ℕ,
          (n : ℝ) - 2 <
            |h3NativeActualVorticityComponentAt u i (τ n) (z n)|)
          ∧
        Tendsto
          (fun n : ℕ =>
            |h3NativeActualVorticityComponentAt u i (τ n) (z n)|)
          atTop atTop

/-- Hypothetical nonextension produces a purely physical terminal sequence on
which the minimal envelope and one fixed actual vorticity component both
diverge. -/
theorem exists_terminal_minimalVorticityPhysicalFixedComponentEscapeSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalMinimalVorticityPhysicalFixedComponentEscapeSequence u T := by
  obtain
    ⟨
      τ,
      hData,
      hTauTendsto,
      hEnvelopeTendsto,
      _y,
      _hActualTendsto
    ⟩ :=
    exists_terminal_minimalVorticityPhysicalEscapeSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hExists :
      ∀ n : ℕ,
        ∃ z : Point3,
          (
            (n : ℝ) - 2 <
              |realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n) z|
          )
            ∨
          (
            (n : ℝ) - 2 <
              |realVorticityY
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n) z|
          )
            ∨
          (
            (n : ℝ) - 2 <
              |realVorticityZ
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n) z|
          ) := by
    intro n
    have hThreshold :
        (n : ℝ) - 2 < h3MinimalVorticityEnvelopeAt u (τ n) := by
      linarith [(hData n).2]
    exact
      exists_actualVorticityComponent_gt_of_lt_h3MinimalVorticityEnvelopeAt
        hThreshold

  choose z hz using hExists

  obtain ⟨i, k, hk, hFixed, hFixedTendsto⟩ :=
    native_actualVorticity_fixedComponent_extraction
      u τ z hz

  have hKTop :
      Tendsto k atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hk n)

  have hReindexedData :
      ∀ n : ℕ,
        τ (k n) ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
          ∧
        (n : ℝ) < h3MinimalVorticityEnvelopeAt u (τ (k n)) := by
    intro n

    have hCast :
        (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hk n

    have hDenN :
        0 < (n : ℝ) + 1 := by
      positivity

    have hInv :
        (1 : ℝ) / ((k n : ℝ) + 1)
          ≤
        1 / ((n : ℝ) + 1) := by
      exact
        one_div_le_one_div_of_le
          hDenN
          (by linarith)

    have hOrig := hData (k n)

    constructor
    · constructor
      · linarith [(hOrig.1).1, hInv]
      · exact (hOrig.1).2
    · exact lt_of_le_of_lt hCast hOrig.2

  exact
    ⟨
      i,
      (fun n : ℕ => τ (k n)),
      (fun n : ℕ => z (k n)),
      hReindexedData,
      hTauTendsto.comp hKTop,
      hEnvelopeTendsto.comp hKTop,
      hFixed,
      hFixedTendsto
    ⟩

/-- Neutral formulation: either the H³ path continues smoothly, or one fixed
actual vorticity component diverges on a purely physical terminal sequence
that also carries minimal-envelope escape. -/
theorem smoothContinuationExtension_or_terminal_minimalVorticityPhysicalFixedComponentEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalMinimalVorticityPhysicalFixedComponentEscapeSequence u T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_minimalVorticityPhysicalFixedComponentEscapeSequence_of_noH3PathExtension
          hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
