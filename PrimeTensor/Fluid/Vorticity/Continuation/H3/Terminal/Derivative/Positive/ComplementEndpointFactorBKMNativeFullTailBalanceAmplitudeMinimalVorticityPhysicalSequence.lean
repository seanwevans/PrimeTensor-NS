import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityEndpointEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCancellationActualVorticity

/-!
# Pure physical minimal-vorticity escape sequence

The cofinal terminal escape theorem does not require any distinguished native
witness.  This file extracts from it a standard physical-time sequence.

Under hypothetical nonextension, choose `τ n` inside the shrinking window

    (max(midpoint, T - 1/(n+1)), T)

with minimal common vorticity envelope larger than `n`.  Then `τ n → T`, the
minimal envelope tends to `+∞`, and actual vorticity tends to `+∞` at selected
spatial points on exactly the same times.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem tendsto_terminal_of_one_div_natSucc_localization
    {T : ℝ}
    {τ : ℕ → ℝ}
    (hτ :
      ∀ n : ℕ,
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T) :
    Tendsto τ atTop (𝓝 T) := by
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / ε)

  refine ⟨N, ?_⟩
  intro n hn

  have hCast : (N : ℝ) ≤ n := by
    exact_mod_cast hn

  have hDenN : 0 < (N : ℝ) + 1 := by
    positivity

  have hInvN :
      (1 : ℝ) / ((n : ℝ) + 1)
        ≤ 1 / ((N : ℝ) + 1) := by
    exact
      one_div_le_one_div_of_le
        hDenN
        (by linarith)

  have hSmallN :
      1 / ((N : ℝ) + 1) < ε := by
    have hεPos : 0 < ε := hε
    have hInvEps : 1 / ε < (N : ℝ) := hN
    have hNPlus : 1 / ε < (N : ℝ) + 1 := by
      linarith
    have hMulRaw : 1 < ((N : ℝ) + 1) * ε :=
      (div_lt_iff₀ hεPos).1 hNPlus
    have hMul : 1 < ε * ((N : ℝ) + 1) := by
      simpa only [mul_comm] using hMulRaw
    exact
      (div_lt_iff₀ hDenN).2
        (by simpa only [one_mul] using hMul)

  have hSmall :
      (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    lt_of_le_of_lt hInvN hSmallN

  have hLower := (hτ n).1
  have hUpper := (hτ n).2

  rw [Real.dist_eq]
  have hDiffNonpos : τ n - T ≤ 0 := by
    linarith
  rw [abs_of_nonpos hDiffNonpos]
  linarith

private theorem tendsto_atTop_of_natCast_lt
    {f : ℕ → ℝ}
    (hf : ∀ n : ℕ, (n : ℝ) < f n) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M

  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M

  filter_upwards [eventually_ge_atTop N] with n hn

  have hNat : M < (n : ℝ) := by
    exact
      lt_of_lt_of_le
        hN
        (by exact_mod_cast hn)

  exact le_of_lt (lt_trans hNat (hf n))

/-- Pure physical-time terminal escape data for the minimal common vorticity
envelope, together with actual-vorticity escape at selected spatial points. -/
def H3TerminalMinimalVorticityPhysicalEscapeSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∃ τ : ℕ → ℝ,
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
    ∃ y : ℕ → Point3,
      Tendsto
        (fun n : ℕ => h3ActualVorticityMaxAt u (τ n) (y n))
        atTop atTop

/-- Hypothetical nonextension produces a purely physical terminal sequence on
which both the minimal common vorticity envelope and actual vorticity diverge.
No native witness or balance-share extraction is used in the selection. -/
theorem exists_terminal_minimalVorticityPhysicalEscapeSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalMinimalVorticityPhysicalEscapeSequence u T := by
  have hCofinal :
      H3TerminalMinimalVorticityEnvelopeCofinallyUnbounded u a T :=
    h3TerminalMinimalVorticityEnvelope_cofinallyUnbounded_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hMid :
      h3BKMKineticTailMidpoint a T ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2

  have hSelect :
      ∀ n : ℕ,
        ∃ t : ℝ,
          t ∈
              Set.Ioo
                (max
                  (h3BKMKineticTailMidpoint a T)
                  (T - (1 : ℝ) / ((n : ℝ) + 1)))
                T
            ∧
          (n : ℝ) < h3MinimalVorticityEnvelopeAt u t := by
    intro n

    have hWindow :
        T - (1 : ℝ) / ((n : ℝ) + 1) < T := by
      have hPos :
          0 < (1 : ℝ) / ((n : ℝ) + 1) := by
        positivity
      linarith

    have hb :
        max
            (h3BKMKineticTailMidpoint a T)
            (T - (1 : ℝ) / ((n : ℝ) + 1))
          ∈ Set.Ioo a T := by
      constructor
      · exact
          lt_of_lt_of_le
            hMid.1
            (le_max_left _ _)
      · exact max_lt hMid.2 hWindow

    exact
      hCofinal
        (max
          (h3BKMKineticTailMidpoint a T)
          (T - (1 : ℝ) / ((n : ℝ) + 1)))
        hb
        (n : ℝ)

  choose τ hτ using hSelect

  have hLocalized :
      ∀ n : ℕ,
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T := by
    intro n
    exact
      ⟨
        lt_of_le_of_lt
          (le_max_right
            (h3BKMKineticTailMidpoint a T)
            (T - (1 : ℝ) / ((n : ℝ) + 1)))
          (hτ n).1.1,
        (hτ n).1.2
      ⟩

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) :=
    tendsto_terminal_of_one_div_natSucc_localization hLocalized

  have hEnvelopeTendsto :
      Tendsto
        (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
        atTop atTop :=
    tendsto_atTop_of_natCast_lt
      (fun n => (hτ n).2)

  obtain ⟨y, hActualTendsto⟩ :=
    exists_actualVorticityMax_tendsto_atTop_of_minimalEnvelope_tendsto_atTop
      hEnvelopeTendsto

  exact
    ⟨
      τ,
      (fun n => ⟨hLocalized n, (hτ n).2⟩),
      hTauTendsto,
      hEnvelopeTendsto,
      y,
      hActualTendsto
    ⟩

/-- Neutral formulation: either the H³ path continues smoothly, or there is a
purely physical terminal sequence carrying synchronized minimal-envelope and
actual-vorticity escape. -/
theorem smoothContinuationExtension_or_terminal_minimalVorticityPhysicalEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalMinimalVorticityPhysicalEscapeSequence u T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_minimalVorticityPhysicalEscapeSequence_of_noH3PathExtension
          hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
