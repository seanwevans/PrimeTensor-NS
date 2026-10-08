import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive.Rate.Classify.Radial.Resolve.Package.NoExtension.Higher.Rate.Branch.Higher.Direct.Branch.Scale.Width.InverseSqrt.Package.Normalized.Package.PhysicalClock.Sample.Collapse.Synchronized.Geometry.Width.Critical.Alternative

/-!
# Quantitative sampled nonvanishing in the critical-width alternative

Each failure of sampled normalized vanishing now yields a fixed positive
finite threshold on a strictly increasing terminal subsequence. The energy
and critical-width cases are retained without change.
The new floor is a normalized lower bound, not a claim that the normalized
quantity diverges. The full package adds no analytic hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000


/-- Failure to converge to zero gives a positive finite recurrent threshold. -/
theorem h3Terminal_exists_finite_positive_threshold_of_not_tendsto_zero
    (F : ℕ → ℝ≥0∞)
    (hNot : ¬ Tendsto F atTop (𝓝 0)) :
    ∃ B : ℝ≥0∞, 0 < B ∧ B < ∞ ∧ (∃ᶠ n : ℕ in atTop, B ≤ F n) := by
  classical
  have hFail : ∃ b : ℝ≥0∞, 0 < b ∧ ¬ (∀ᶠ n : ℕ in atTop, F n < b) := by
    by_contra hNone
    apply hNot
    apply tendsto_order.2
    constructor
    · intro b hb
      exact False.elim ((not_lt_of_ge (zero_le : (0 : ℝ≥0∞) ≤ b)) hb)
    · intro b hb
      by_contra hNotEventually
      exact hNone ⟨b, hb, hNotEventually⟩
  obtain ⟨b, hb, hFail⟩ := hFail
  refine ⟨min b 1, lt_min hb zero_lt_one, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right b 1) (by simp)
  · change ¬ (∀ᶠ n : ℕ in atTop, ¬ (min b 1 ≤ F n))
    intro hBelow
    apply hFail
    filter_upwards [hBelow] with n hn
    exact lt_of_lt_of_le (lt_of_not_ge hn) (min_le_left b 1)

/-- Select one strict subsequence carrying a fixed pointwise threshold. -/
theorem h3Terminal_exists_strictMono_threshold_of_frequently
    (F : ℕ → ℝ≥0∞) (B : ℝ≥0∞)
    (hFreq : ∃ᶠ n : ℕ in atTop, B ≤ F n) :
    ∃ v : ℕ → ℕ, StrictMono v ∧ ∀ n : ℕ, B ≤ F (v n) := by
  classical
  have hPick : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ B ≤ F n := by
    intro N
    by_contra hNone
    apply hFreq
    apply Filter.eventually_atTop.2
    refine ⟨N, ?_⟩
    intro n hn hBound
    exact hNone ⟨n, hn, hBound⟩
  choose f hf using hPick
  let v : ℕ → ℕ := Nat.rec (f 0) (fun _ prev => f (prev + 1))
  have hvZero : v 0 = f 0 := rfl
  have hvSucc (n : ℕ) : v (n + 1) = f (v n + 1) := rfl
  have hMono : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hvSucc]
    exact lt_of_lt_of_le (Nat.lt_succ_self (v n)) (hf (v n + 1)).1
  refine ⟨v, hMono, ?_⟩
  intro n
  cases n with
  | zero => simpa only [hvZero] using (hf 0).2
  | succ n => simpa only [hvSucc] using (hf (v n + 1)).2

/-- A fixed finite positive sampled-clock normalized floor on a terminal subsequence. -/
def H3TerminalHigherRadialSampleClockNonvanishingWitness
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (radialOrder : ℕ) : Prop :=
  ∃ B : ℝ≥0∞,
    0 < B ∧ B < ∞ ∧
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      (∀ n : ℕ,
        B ≤ ENNReal.ofReal (Real.sqrt (T - τ (v n))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n)))

theorem h3TerminalHigherRadialSampleClockNonvanishingWitness_of_not_tendsto_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (radialOrder : ℕ)
    (hTau : Tendsto τ atTop (𝓝 T))
    (hNot : ¬ Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt (T - τ n)) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ n) (hτ n))
      atTop (𝓝 0)) :
    H3TerminalHigherRadialSampleClockNonvanishingWitness hH3 hClass τ hτ radialOrder := by
  let F : ℕ → ℝ≥0∞ := fun n : ℕ =>
    ENNReal.ofReal (Real.sqrt (T - τ n)) *
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass radialOrder (τ n) (hτ n)
  obtain ⟨B, hB, hFinite, hFreq⟩ :=
    h3Terminal_exists_finite_positive_threshold_of_not_tendsto_zero F hNot
  obtain ⟨v, hMono, hBound⟩ := h3Terminal_exists_strictMono_threshold_of_frequently F B hFreq
  exact ⟨B, hB, hFinite, v, hMono, hTau.comp hMono.tendsto_atTop, hBound⟩

def H3TerminalResolvedCanonicalForcingQuantitativeCriticalAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (δ : ℝ) : Prop :=
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSampleClockNonvanishingWitness hH3 hClass τ hτ
        (h3TerminalForcingThirdQHigherRadialShift qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSampleClockNonvanishingWitness hH3 hClass τ hτ
        (h3TerminalForcingFourthQHigherRadialShift qRadial)) ∨
    (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialForwardWidthCriticalThreshold
        hH3 hClass τ hτ s σ
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialForwardWidthCriticalThreshold
        hH3 hClass τ hτ s σ
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial))

theorem resolvedCanonicalForcingQuantitativeCriticalAlternative_of_criticalAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (δ : ℝ)
    (hTau : Tendsto τ atTop (𝓝 T))
    (hAlternative : H3TerminalResolvedCanonicalForcingForwardWidthCriticalAlternative hH3 hClass τ hτ s σ δ) :
    H3TerminalResolvedCanonicalForcingQuantitativeCriticalAlternative hH3 hClass τ hτ s σ δ := by
  rcases hAlternative with hSecond | hFourth | hRemaining
  · obtain ⟨qRadial, hNot⟩ := hSecond
    exact Or.inl ⟨qRadial,
      h3TerminalHigherRadialSampleClockNonvanishingWitness_of_not_tendsto_zero
        hH3 hClass τ hτ _ hTau hNot⟩
  · obtain ⟨qRadial, hNot⟩ := hFourth
    exact Or.inr (Or.inl ⟨qRadial,
      h3TerminalHigherRadialSampleClockNonvanishingWitness_of_not_tendsto_zero
        hH3 hClass τ hτ _ hTau hNot⟩)
  · exact Or.inr (Or.inr hRemaining)

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingQuantitativeCriticalAlternativeEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ ψ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        StrictMono ψ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              ∃ hr :
                ∀ n : ℕ,
                  r (φ (ψ n)) ∈ Set.Ioo a T,
                Tendsto (fun n : ℕ => s (φ (ψ n))) atTop (𝓝 T)
                  ∧
                Tendsto
                  (fun n : ℕ => σ (m (q (φ (ψ n)))))
                  atTop
                  (𝓝 T)
                  ∧
                (∀ n : ℕ,
                  s (φ (ψ n)) < σ (m (q (φ (ψ n)))))
                  ∧
                (∀ n : ℕ,
                  r (φ (ψ n)) ∈
                    Set.Icc
                      (s (φ (ψ n)))
                      (σ (m (q (φ (ψ n))))))
                  ∧
                Tendsto (fun n : ℕ => r (φ (ψ n))) atTop (𝓝 T)
                  ∧
                ∃ χ ω : ℕ → ℕ,
                  StrictMono χ
                    ∧
                  StrictMono ω
                    ∧
                  Tendsto
                    (fun n : ℕ => s (φ (ψ (χ (ω n)))))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (fun n : ℕ => σ (m (q (φ (ψ (χ (ω n)))))))
                    atTop
                    (𝓝 T)
                    ∧
                  Tendsto
                    (fun n : ℕ => r (φ (ψ (χ (ω n)))))
                    atTop
                    (𝓝 T)
                    ∧
                  let τ : ℕ → ℝ :=
                    fun n : ℕ =>
                      r (φ (ψ (χ (ω n))))
                  let hτ :
                      ∀ n : ℕ,
                        τ n ∈ Set.Ioo a T :=
                    fun n : ℕ =>
                      hr (χ (ω n))
                  let clock : ℕ → ℝ :=
                    fun n : ℕ => T - s (φ (ψ (χ (ω n))))
                  (∀ n : ℕ, 0 < clock n) ∧
                  Tendsto clock atTop (𝓝 0) ∧
                  H3TerminalResolvedCanonicalForcingQuantitativeCriticalAlternative
                    hH3 hClass τ hτ
                    (fun n : ℕ => s (φ (ψ (χ (ω n)))))
                    (fun n : ℕ => σ (m (q (φ (ψ (χ (ω n)))))))
                    δ

theorem resolvedCanonicalForcingQuantitativeCriticalAlternativeEscapeSubsequenceOf_of_criticalEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hWidth :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingForwardWidthCriticalAlternativeEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingQuantitativeCriticalAlternativeEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      χ,
      ω,
      hChiMono,
      hOmegaMono,
      hsFinal,
      hSigmaFinal,
      hrFinal,
      hClockPos,
      hClockZero,
      hBranch
    ⟩ :=
    hWidth

  refine
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      χ,
      ω,
      hChiMono,
      hOmegaMono,
      hsFinal,
      hSigmaFinal,
      hrFinal,
      hClockPos,
      hClockZero,
      ?_
    ⟩

  let τ : ℕ → ℝ := fun n : ℕ => r (φ (ψ (χ (ω n))))
  let hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T := fun n : ℕ => hr (χ (ω n))
  let left : ℕ → ℝ := fun n : ℕ => s (φ (ψ (χ (ω n))))
  let right : ℕ → ℝ := fun n : ℕ => σ (m (q (φ (ψ (χ (ω n))))))
  have hTau : Tendsto τ atTop (𝓝 T) := by
    simpa only [τ] using hrFinal
  have hQualitative : H3TerminalResolvedCanonicalForcingForwardWidthCriticalAlternative hH3 hClass τ hτ left right δ := by
    simpa only [τ, hτ, left, right] using hBranch
  have hQuantitative : H3TerminalResolvedCanonicalForcingQuantitativeCriticalAlternative hH3 hClass τ hτ left right δ :=
    resolvedCanonicalForcingQuantitativeCriticalAlternative_of_criticalAlternative
      hH3 hClass τ hτ left right δ hTau hQualitative
  simpa only [τ, hτ, left, right] using hQuantitative

end

end Euclidean
end Bridge
end PrimeTensor
