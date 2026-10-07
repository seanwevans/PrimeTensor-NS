import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.InverseSqrt.Package.Normalized.Package.PhysicalClock.Sample

/-!
# Quantitative collapse of the sampling clock relative to the left clock

From arbitrarily late clock comparisons at every positive factor, select a
strictly increasing subsequence with ratio in `(0, 1 / (n + 1))`. The ratio
therefore converges to zero.

The forcing corollary retains the hypotheses excluding energy escape and
requiring both sampling-clock normalized radial families to vanish. It also
retains terminal convergence of both time sequences. No unconditional
clock collapse or PDE continuation conclusion is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- An explicit inverse-index upper bound forces a positive ratio to zero. -/
theorem h3TerminalClockRatio_tendsto_zero_of_inverse_index_bound
    (ratio : ℕ → ℝ)
    (hPos : ∀ n : ℕ, 0 < ratio n)
    (hUpper : ∀ n : ℕ, ratio n < 1 / ((n : ℝ) + 1)) :
    Tendsto ratio atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hOne : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hN
  have hRecip : 1 / ((n : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    nlinarith [mul_le_mul_of_nonneg_right hNn hε.le]
  rw [Real.dist_eq, sub_zero, abs_of_pos (hPos n)]
  exact lt_trans (hUpper n) hRecip

/-- Select a strict subsequence of positive clocks with an explicit vanishing ratio. -/
theorem h3Terminal_exists_strictMono_clockRatio_collapse
    (left sample : ℕ → ℝ)
    (hLeft : ∀ n : ℕ, 0 < left n)
    (hSample : ∀ n : ℕ, 0 < sample n)
    (hSmall : ∀ c : ℝ, 0 < c →
      ∃ᶠ n : ℕ in atTop, sample n < c * left n) :
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      (∀ n : ℕ, 0 < sample (v n) / left (v n)) ∧
      (∀ n : ℕ, sample (v n) / left (v n) < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n : ℕ => sample (v n) / left (v n)) atTop (𝓝 0) := by
  classical
  have hPick : ∀ k N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ sample n < (1 / ((k : ℝ) + 1)) * left n := by
    intro k N
    by_contra hNone
    have hNot : ∀ᶠ n : ℕ in atTop,
        ¬ (sample n < (1 / ((k : ℝ) + 1)) * left n) := by
      apply Filter.eventually_atTop.2
      refine ⟨N, ?_⟩
      intro n hn hBound
      exact hNone ⟨n, hn, hBound⟩
    have hFreq := hSmall (1 / ((k : ℝ) + 1)) (by positivity)
    exact hFreq hNot
  choose f hf using hPick
  let v : ℕ → ℕ := Nat.rec (f 0 0) (fun k prev => f (k + 1) (prev + 1))
  have hvZero : v 0 = f 0 0 := rfl
  have hvSucc (n : ℕ) : v (n + 1) = f (n + 1) (v n + 1) := rfl
  have hMono : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hvSucc]
    exact lt_of_lt_of_le (Nat.lt_succ_self (v n)) (hf (n + 1) (v n + 1)).1
  have hBound : ∀ n : ℕ,
      sample (v n) < (1 / ((n : ℝ) + 1)) * left (v n) := by
    intro n
    cases n with
    | zero => simpa only [hvZero] using (hf 0 0).2
    | succ n => simpa only [hvSucc] using (hf (n + 1) (v n + 1)).2
  have hRatioPos : ∀ n : ℕ, 0 < sample (v n) / left (v n) := by
    intro n
    exact div_pos (hSample (v n)) (hLeft (v n))
  have hRatioUpper : ∀ n : ℕ,
      sample (v n) / left (v n) < 1 / ((n : ℝ) + 1) := by
    intro n
    exact (div_lt_iff₀ (hLeft (v n))).2 (hBound n)
  exact ⟨v, hMono, hRatioPos, hRatioUpper,
    h3TerminalClockRatio_tendsto_zero_of_inverse_index_bound
      (fun n : ℕ => sample (v n) / left (v n)) hRatioPos hRatioUpper⟩

/-- Conditional clock collapse, synchronized with both terminal time sequences. -/
theorem resolvedCanonicalForcing_exists_sampleClockRatio_collapse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s : ℕ → ℝ) (δ : ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hsT : Tendsto s atTop (𝓝 T))
    (hτT : Tendsto τ atTop (𝓝 T))
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ (fun n : ℕ => T - s n))
    (hNoEnergy : ¬ (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop))
    (hSecondZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingThirdQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0))
    (hFourthZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingFourthQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0)) :
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => s (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      (∀ n : ℕ, 0 < (T - τ (v n)) / (T - s (v n))) ∧
      (∀ n : ℕ, (T - τ (v n)) / (T - s (v n)) < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n : ℕ => (T - τ (v n)) / (T - s (v n))) atTop (𝓝 0) := by
  have hSmall :=
    resolvedCanonicalForcing_frequently_small_sampleClock_of_vanishing
      hH3 hClass τ hτ s δ hBranch hNoEnergy hSecondZero hFourthZero
  obtain ⟨v, hMono, hPos, hUpper, hZero⟩ :=
    h3Terminal_exists_strictMono_clockRatio_collapse
      (fun n : ℕ => T - s n) (fun n : ℕ => T - τ n)
      (fun n : ℕ => sub_pos.mpr (hs n))
      (fun n : ℕ => sub_pos.mpr (hτ n).2)
      hSmall
  exact ⟨v, hMono, hsT.comp hMono.tendsto_atTop,
    hτT.comp hMono.tendsto_atTop, hPos, hUpper, hZero⟩

end

end Euclidean
end Bridge
end PrimeTensor
