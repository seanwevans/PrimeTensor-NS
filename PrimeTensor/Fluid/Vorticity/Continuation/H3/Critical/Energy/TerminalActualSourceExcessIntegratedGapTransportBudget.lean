import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessCumulativeSignedReplenishment
import Mathlib.Tactic

/-!
# From sampled gap replenishment to integrated signed physical transport

At each already selected physical gap, the exact balance
  E' = -Transport - 2 D
identifies the positive signed transport surplus. If the actual energy
rate and its positive signed surplus are interval-integrable on that
*compact* gap, the fundamental theorem of calculus bounds its FULL energy
gain by the positive-part transport integral, instead of by a single
mean-value sample.

The cofinal statement records the local compact-gap integrability premises
explicitly, INSIDE the existential witness, with no integrability premise
on the entire terminal interval. It preserves the SAME source-driven
windows, their drain-or-Riccati alternatives and pairwise separation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- An integrable local majorant of the derivative pays for the ENTIRE
signed endpoint gain by FTC, not just for a sampled derivative. -/
theorem h3Critical_scalar_gapIntegratedMajorant_pays_energyGain
    (E G : ℝ → ℝ) (x y : ℝ) (hxy : x < y)
    (hDiff : ∀ s : ℝ, s ∈ Set.Icc x y → DifferentiableAt ℝ E s)
    (hDerivInt : IntervalIntegrable (deriv E) volume x y)
    (hGInt : IntervalIntegrable G volume x y)
    (hUpper : ∀ s : ℝ, s ∈ Set.Icc x y → deriv E s ≤ G s) :
    E y - E x ≤ ∫ s in x..y, G s := by
  have hDiffU : ∀ s : ℝ, s ∈ Set.uIcc x y → DifferentiableAt ℝ E s := by
    intro s hs
    rw [Set.uIcc_of_le hxy.le] at hs
    exact hDiff s hs
  have hFTC : (∫ s in x..y, deriv E s) = E y - E x :=
    intervalIntegral.integral_deriv_eq_sub hDiffU hDerivInt
  have hIntegral : (∫ s in x..y, deriv E s) ≤ ∫ s in x..y, G s :=
    intervalIntegral.integral_mono_on hxy.le hDerivInt hGInt hUpper
  rw [hFTC] at hIntegral
  exact hIntegral

/-- The local positive-part of the EXACT physical transport minus both
viscous copies pays every signed H³ energy gain across one gap. The only
extra requirements are the indicated compact-gap interval integrals. -/
theorem h3Critical_physicalGap_integratedSignedTransport_pays_energyGain
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y)
    (hDerivInt : IntervalIntegrable
      (deriv (velocityH3EnergyAt u)) volume x y)
    (hSignedInt : IntervalIntegrable
      (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)) volume x y) :
    velocityH3EnergyAt u y - velocityH3EnergyAt u x ≤
      ∫ s in x..y, max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s) := by
  have hInside (s : ℝ) (hs : s ∈ Set.Icc x y) :
      s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
  have hDiff (s : ℝ) (hs : s ∈ Set.Icc x y) :
      DifferentiableAt ℝ (velocityH3EnergyAt u) s :=
    h3Critical_actualH3Energy_differentiableAt_onStrict
      hH3 hClass (hInside s hs)
  have hUpper (s : ℝ) (hs : s ∈ Set.Icc x y) :
      deriv (velocityH3EnergyAt u) s ≤
        max 0 (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s) := by
    have hBalance :=
      deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
        hH3 hClass (hInside s hs)
    have hEq : deriv (velocityH3EnergyAt u) s =
        -velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s := by
      linarith only [hBalance]
    rw [hEq]
    exact le_max_right _ _
  exact h3Critical_scalar_gapIntegratedMajorant_pays_energyGain
    (velocityH3EnergyAt u)
    (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s))
    x y hxy hDiff hDerivInt hSignedInt hUpper

/-- A finite integrated replenishment budget is incompatible with a larger
sum of certified H³ window drains unless some window pays the Riccati
energy alternative. The integrated budget uses the same scalar telescoping
lemma as the accepted sampled-gap result. -/
theorem h3Critical_scalar_finiteIntegratedGapDrainOrEnergy
    (x y c G : ℕ → ℝ) (P : ℕ → Prop)
    (hWindow : ∀ k, P k ∨ c k + y k ≤ x k)
    (hIntegratedGap : ∀ k, x (k + 1) - y k ≤ G k) :
    ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧ P k) ∨
      (∑ k ∈ Finset.range (m + 1), c k) + y m ≤
        x 0 + ∑ k ∈ Finset.range m, G k := by
  exact h3Critical_scalar_finiteDrainOrReplenishmentAccounting
    x y c G P hWindow hIntegratedGap

/-- The accepted cofinal physical source windows acquire an INTEGRATED
signed-gap compensation alternative whenever the two natural local
compact-gap integrability statements hold. Neither statement is assumed
on the terminal half-open interval; they are exposed as the precise next
regularity task for the physical PDE. -/
theorem h3Critical_noL2Trace_cofinalQuintic_integratedSignedGapBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n) :
    ∃ t : ℕ → ℝ, ∃ v : ℕ → ℕ, ∃ δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ, 0 < δ k ∧ t (v k) + δ k < t (v (k + 1))) ∧
      (∀ k : ℕ,
        (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        velocityH3EnergyAt u (t (v k) + δ k) +
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k ≤
          velocityH3EnergyAt u (t (v k))) ∧
      ((∀ k : ℕ,
          IntervalIntegrable (deriv (velocityH3EnergyAt u)) volume
            (t (v k) + δ k) (t (v (k + 1))) ∧
          IntervalIntegrable
            (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
              2 * velocityH3DissipationAt u s)) volume
            (t (v k) + δ k) (t (v (k + 1)))) →
        ∀ m : ℕ,
          (∃ k : ℕ, k ≤ m ∧
            ∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
              h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
                h3PathSqrtEnergyRiccatiCoefficient *
                  Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
          (∑ k ∈ Finset.range (m + 1),
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k) + 1 ≤
            velocityH3EnergyAt u (t (v 0)) +
              ∑ k ∈ Finset.range m,
                ∫ s in (t (v k) + δ k)..(t (v (k + 1))),
                  max 0 (-velocityH3TransportDerivativeAt u s -
                    2 * velocityH3DissipationAt u s)) := by
  obtain ⟨t, _w, v, _A, _B, _R, δ, hv, hLimit,
      hSeparated, hWindows, _hReplenish, _hCosts, _hGate⟩ :=
    h3Critical_noL2Trace_cofinalQuintic_endpointDrain_or_gapTransport
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  have hWindowAlt (k : ℕ) :
      (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
        h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
          h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      velocityH3EnergyAt u (t (v k) + δ k) +
        h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k ≤
        velocityH3EnergyAt u (t (v k)) := by
    rcases hWindows k with ⟨_hs, _hw, _hEnd, _hR, _hδ, _hδw,
      _hWidth, hAlt⟩
    exact hAlt
  refine ⟨t, v, δ, hv, hLimit, ?_, hWindowAlt, ?_⟩
  · intro k
    have hWindow := hWindows k
    exact ⟨hWindow.2.2.2.2.1,
      hSeparated k (k + 1) (Nat.lt_succ_self k)⟩
  · intro hRegular m
    let x : ℕ → ℝ := fun k => velocityH3EnergyAt u (t (v k))
    let y : ℕ → ℝ := fun k => velocityH3EnergyAt u (t (v k) + δ k)
    let cost : ℕ → ℝ := fun k =>
      h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k
    let P : ℕ → Prop := fun k =>
      ∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
        h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
          h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s
    let G : ℕ → ℝ := fun k =>
      ∫ s in (t (v k) + δ k)..(t (v (k + 1))),
        max 0 (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s)
    have hStep (k : ℕ) : P k ∨ cost k + y k ≤ x k := by
      rcases hWindowAlt k with hLarge | hDrain
      · exact Or.inl hLarge
      · right
        dsimp only [cost, y, x]
        linarith only [hDrain]
    have hGap (k : ℕ) : x (k + 1) - y k ≤ G k := by
      have hSep : t (v k) + δ k < t (v (k + 1)) :=
        hSeparated k (k + 1) (Nat.lt_succ_self k)
      obtain ⟨hStartK, _hwK, hEndK, _hRK, hδK, hδwK,
        _hWidthK, _hAltK⟩ := hWindows k
      obtain ⟨hStartL, _hwL, _hEndL, _hRL, _hδL, _hδwL,
        _hWidthL, _hAltL⟩ := hWindows (k + 1)
      have hx : t (v k) + δ k ∈ Set.Ioo a T := by
        have hStartA : a < t (v k) :=
          lt_trans hb.1 (lt_trans (hc (v k)).1 hStartK.1)
        have hShort : t (v k) + δ k ≤ t (v k) + _w (v k) :=
          add_le_add_right hδwK (t (v k))
        exact ⟨by linarith only [hStartA, hδK],
          lt_of_le_of_lt hShort hEndK⟩
      have hy : t (v (k + 1)) ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 (lt_trans (hc (v (k + 1))).1 hStartL.1), hStartL.2⟩
      dsimp only [x, y, G]
      exact h3Critical_physicalGap_integratedSignedTransport_pays_energyGain
        hH3 hClass _ _ hx hy hSep (hRegular k).1 (hRegular k).2
    have hFinite := h3Critical_scalar_finiteIntegratedGapDrainOrEnergy
      x y cost G P hStep hGap m
    rcases hFinite with ⟨k, hk, hp⟩ | hAccounting
    · exact Or.inl ⟨k, hk, hp⟩
    · right
      have hFinalEnergy : 1 ≤ y m := by
        dsimp only [y]
        exact one_le_velocityH3EnergyAt u (t (v m) + δ m)
      have hBound :
          (∑ k ∈ Finset.range (m + 1), cost k) + 1 ≤
            x 0 + ∑ k ∈ Finset.range m, G k := by
        calc
          (∑ k ∈ Finset.range (m + 1), cost k) + 1 ≤
              (∑ k ∈ Finset.range (m + 1), cost k) + y m :=
            add_le_add_right hFinalEnergy _
          _ ≤ x 0 + ∑ k ∈ Finset.range m, G k := hAccounting
      exact hBound

end
end PrimeTensor.Bridge.Euclidean
