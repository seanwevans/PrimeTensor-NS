import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Vorticity.Ceiling.Reduced.Regime.Witness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKM.Vorticity.Envelope.Divergence

/-!
# Terminal vorticity-envelope ceiling forces continuation

The preceding balance-share reduction used a uniform terminal bound for the
minimal common vorticity envelope to remove every positive-H³-growth branch.
The existing BKM positive-growth cascade gives a stronger conclusion directly.

Under hypothetical nonextension, every admissible scalar vorticity envelope on
a strict terminal tail diverges along a positive-growth sequence approaching the
terminal time.  Consequently any uniform absolute bound for one such envelope
on that tail is incompatible with nonextension.

Specializing to the minimal common vorticity envelope gives the terminal ceiling
used in the balance-share reductions.  Thus that ceiling forces a smooth
continuation extension outright; the reduced balance witness remains useful as
a structural diagnostic but is not a surviving nonextension alternative under
the ceiling itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A uniformly bounded admissible scalar vorticity envelope on one strict
terminal tail forces smooth continuation. -/
theorem smoothContinuationExtension_of_terminal_vorticityEnvelope_abs_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b M : ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope u g s)
    (hCeiling :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          |g s| ≤ M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  classical
  by_contra hNoExtension

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      _hEnergyTendsto,
      _hDissRatioTendsto,
      _hTransportRatioTendsto,
      _hFrequencyTendsto,
      hEnvelopeAbsTendsto
    ⟩ :=
    exists_terminal_positiveGrowth_fullCascade_vorticityEnvelope_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      hg

  have hEventuallyPastB :
      ∀ᶠ n : ℕ in atTop,
        b < σ n :=
    (tendsto_order.1 hSigmaTendsto).1 b hb.2

  have hEventuallyCeiling :
      ∀ᶠ n : ℕ in atTop,
        |g (σ n)| ≤ M := by
    filter_upwards [hEventuallyPastB] with n hn
    exact hCeiling (σ n) ⟨hn, (hσ n).1.2⟩

  have hEventuallyAbove :
      ∀ᶠ n : ℕ in atTop,
        M < |g (σ n)| :=
    hEnvelopeAbsTendsto.eventually
      (eventually_gt_atTop M)

  obtain ⟨n, hLe, hGt⟩ :=
    (hEventuallyCeiling.and hEventuallyAbove).exists

  exact (not_lt_of_ge hLe) hGt

/-- A uniform upper bound for the minimal common vorticity envelope on one
strict terminal tail forces smooth continuation. -/
theorem smoothContinuationExtension_of_terminal_minimalVorticityEnvelope_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          h3MinimalVorticityEnvelopeAt u t ≤ M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope
            u (h3MinimalVorticityEnvelopeAt u) s := by
    intro s hs
    exact
      vorticityEnvelope_h3MinimalVorticityEnvelopeAt
        hH3
        ⟨
          lt_trans
            hClass.terminal_start.1
            (lt_trans hb.1 hs.1),
          hs.2
        ⟩

  have hAbsCeiling :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          |h3MinimalVorticityEnvelopeAt u s| ≤ M := by
    intro s hs
    have hNonneg :
        0 ≤ h3MinimalVorticityEnvelopeAt u s :=
      h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path
        hH3
        ⟨
          lt_trans
            hClass.terminal_start.1
            (lt_trans hb.1 hs.1),
          hs.2
        ⟩
    rw [abs_of_nonneg hNonneg]
    exact hCeiling s hs

  exact
    smoothContinuationExtension_of_terminal_vorticityEnvelope_abs_ceiling
      hH3
      hClass
      hb
      hg
      hAbsCeiling

/-- Canonical midpoint-anchor specialization of the terminal minimal-vorticity
ceiling continuation theorem. -/
theorem smoothContinuationExtension_of_midpoint_minimalVorticityEnvelope_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T →
          h3MinimalVorticityEnvelopeAt u t ≤ M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  exact
    smoothContinuationExtension_of_terminal_minimalVorticityEnvelope_ceiling
      hH3
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
