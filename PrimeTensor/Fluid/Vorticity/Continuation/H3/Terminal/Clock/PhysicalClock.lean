import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.NormalizedPackage

/-!
# Transfer the normalized floor to the physical left-endpoint clock

The canonical forward interval satisfies `sigma - s ≤ T - s`.
Consequently its positive `sqrt gap * moment` lower bound transfers to
`sqrt (T - s) * moment` on the same selected radial subsequence.
The physical clock is strictly positive and converges to zero.

The moment is sampled at the retained intermediate time `r`; the clock is
anchored at `s`. No comparison with the sampled clock `T - r` is asserted.
The energy branch and all retained terminal geometry are unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000


/-- A larger clock preserves the selected positive normalized lower bound. -/
theorem h3TerminalHigherRadialSqrtWidthPositiveFloor_mono_clock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (gap clock : ℕ → ℝ)
    (radialOrder : ℕ) (C : ℝ)
    (hClock : ∀ n : ℕ, gap n ≤ clock n)
    (hFloor : H3TerminalHigherRadialSqrtWidthPositiveFloor
      hH3 hClass τ hτ gap radialOrder C) :
    H3TerminalHigherRadialSqrtWidthPositiveFloor
      hH3 hClass τ hτ clock radialOrder C := by
  obtain ⟨hC, v, hMono, hTau, hLower, _hNonzero, hHigher⟩ := hFloor
  have hClockLower :
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal C ≤
          ENNReal.ofReal (Real.sqrt (clock (v n))) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass radialOrder (τ (v n)) (hτ (v n)) := by
    filter_upwards [hLower] with n hn
    apply le_trans hn
    have hScale :
        ENNReal.ofReal (Real.sqrt (gap (v n))) ≤
          ENNReal.ofReal (Real.sqrt (clock (v n))) :=
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hClock (v n)))
    gcongr 1 <;> exact hScale
  exact ⟨hC, v, hMono, hTau, hClockLower,
    h3Terminal_not_tendsto_zero_of_eventually_ofReal_pos_le hC hClockLower,
    hHigher⟩

/-- Transfer either radial floor to a larger clock; retain energy escape. -/
theorem resolvedCanonicalForcingSqrtWidthPositiveFloorBranch_mono_clock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (δ : ℝ) (gap clock : ℕ → ℝ)
    (hClock : ∀ n : ℕ, gap n ≤ clock n)
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ gap) :
    H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ clock := by
  rcases hBranch with hEnergy | hSecond | hFourth
  · exact Or.inl hEnergy
  · obtain ⟨qRadial, hFloor⟩ := hSecond
    exact Or.inr (Or.inl ⟨qRadial,
      h3TerminalHigherRadialSqrtWidthPositiveFloor_mono_clock
        hH3 hClass τ hτ gap clock _ _ hClock hFloor⟩)
  · obtain ⟨qRadial, hFloor⟩ := hFourth
    exact Or.inr (Or.inr ⟨qRadial,
      h3TerminalHigherRadialSqrtWidthPositiveFloor_mono_clock
        hH3 hClass τ hτ gap clock _ _ hClock hFloor⟩)

def H3TerminalPhysicalTopDissipationResolvedCanonicalForcingPhysicalLeftClockPositiveFloorEscapeSubsequenceOf
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
                  H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
                    hH3 hClass τ hτ δ clock

theorem resolvedCanonicalForcingPhysicalLeftClockPositiveFloorEscapeSubsequenceOf_of_sqrtWidthPositiveFloorEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hWidth :
      H3TerminalPhysicalTopDissipationResolvedCanonicalForcingSqrtWidthPositiveFloorEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationResolvedCanonicalForcingPhysicalLeftClockPositiveFloorEscapeSubsequenceOf
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
      ?_
    ⟩

  let τ : ℕ → ℝ :=
    fun n : ℕ =>
      r (φ (ψ (χ (ω n))))

  let hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T :=
    fun n : ℕ =>
      hr (χ (ω n))

  let gap : ℕ → ℝ :=
    fun n : ℕ =>
      σ (m (q (φ (ψ (χ (ω n)))))) - s (φ (ψ (χ (ω n))))
  let clock : ℕ → ℝ :=
    fun n : ℕ => T - s (φ (ψ (χ (ω n))))

  have hClockPos : ∀ n : ℕ, 0 < clock n := by
    intro n
    exact sub_pos.mpr (hs (φ (ψ (χ (ω n))))).2

  have hClockZero : Tendsto clock atTop (𝓝 0) := by
    have hDiff :
        Tendsto (fun n : ℕ => T - s (φ (ψ (χ (ω n)))))
          atTop (𝓝 (T - T)) :=
      tendsto_const_nhds.sub hsFinal
    simpa only [sub_self] using hDiff

  have hGapLe : ∀ n : ℕ, gap n ≤ clock n := by
    intro n
    exact sub_le_sub_right (hσ (m (q (φ (ψ (χ (ω n))))))).2.le _

  have hWidthBranch :
      H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
        hH3 hClass τ hτ δ gap := by
    simpa only [τ, hτ, gap] using hBranch

  have hClockBranch :
      H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
        hH3 hClass τ hτ δ clock :=
    resolvedCanonicalForcingSqrtWidthPositiveFloorBranch_mono_clock
      hH3 hClass τ hτ δ gap clock hGapLe hWidthBranch

  dsimp only
  simpa only [τ, hτ, clock] using
    And.intro hClockPos (And.intro hClockZero hClockBranch)

end

end Euclidean
end Bridge
end PrimeTensor
