import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessIntegratedGapTransportBudget
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakAutomaticIntegratedTransport244
import Mathlib.Tactic

/-!
# Automatic compact-gap signed H³ transport replenishment

The accepted compact-interval Landau / one-sided-derivative theorem makes
E'(t) interval-integrable on every strict H³ energy-class interval, without
assuming a terminal or even local viscous-dissipation integral.

The exact physical PDE balance identifies
  max(0,-Transport_H3(t)-2 D_H3(t)) = max(0,E'(t))
on the entire open strict-time gap. Since the positive part of an integrable
real function is integrable, this closes both local hypotheses of the earlier
integrated-gap budget, *without* finite terminal H³ dissipation.

The last theorem selects the same cofinal source windows and applies actual
integrated positive signed transport replenishment with no new time-integrability
hypothesis. It retains the Riccati-energy exception and does not assert a
uniform integrated transport bound or terminal regularity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The positive part of the actual scalar energy derivative is locally
integrable whenever the signed derivative is. The proof uses the exact
real identity `max 0 z = (|z|+z)/2`, not a derivative-continuity premise. -/
theorem h3Critical_scalar_positiveDerivative_intervalIntegrable
    (E : ℝ → ℝ) (x y : ℝ)
    (hDerivativeInt : IntervalIntegrable (deriv E) volume x y) :
    IntervalIntegrable (fun s : ℝ => max 0 (deriv E s)) volume x y := by
  have hAbs : IntervalIntegrable (fun s : ℝ => |deriv E s|) volume x y := by
    simpa only [Real.norm_eq_abs] using hDerivativeInt.norm
  have hHalf : IntervalIntegrable
      (fun s : ℝ => (1 / 2 : ℝ) * (|deriv E s| + deriv E s))
      volume x y := by
    simpa only [Pi.add_apply] using
      (hAbs.add hDerivativeInt).const_mul (1 / 2 : ℝ)
  apply hHalf.congr_uIoo
  intro s _hs
  change (1 / 2 : ℝ) * (|deriv E s| + deriv E s) = max 0 (deriv E s)
  rcases le_total 0 (deriv E s) with hn | hn
  · rw [max_eq_right hn, abs_of_nonneg hn]
    ring
  · rw [max_eq_left hn, abs_of_nonpos hn]
    ring

/-- On EVERY compact strict H³ time gap, both interval-integrability
premises of the previous integrated-gap theorem hold automatically.
No full-H³-dissipation budget, and no transport-time regularity assumption,
is used. The key identification is the *full* signed PDE energy balance. -/
theorem h3Critical_physicalGap_signedPositiveTransport_intervalIntegrable_automatic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) :
    IntervalIntegrable (deriv (velocityH3EnergyAt u)) volume x y ∧
    IntervalIntegrable
      (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)) volume x y := by
  have hDerivativeInt :=
    h3Path_canonicalEnergyDerivative_intervalIntegrable_automatic244
      hH3 hClass x y hx hy hxy.le
  have hPosInt := h3Critical_scalar_positiveDerivative_intervalIntegrable
    (velocityH3EnergyAt u) x y hDerivativeInt
  have hSame : Set.EqOn
      (fun s : ℝ => max 0 (deriv (velocityH3EnergyAt u) s))
      (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s))
      (Set.uIoo x y) := by
    intro s hs
    rw [Set.uIoo_of_le hxy.le] at hs
    have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_trans hx.1 hs.1, lt_trans hs.2 hy.2⟩
    have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hsClass
    have hSigned : deriv (velocityH3EnergyAt u) s =
        -velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s := by
      linarith only [hBalance]
    change max 0 (deriv (velocityH3EnergyAt u) s) =
      max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)
    exact congrArg (fun z : ℝ => max 0 z) hSigned
  exact ⟨hDerivativeInt, hPosInt.congr_uIoo hSame⟩

/-- The genuine physical integrated signed-gap estimate is automatically
available on every compact gap of an H³ energy class, without any additional
integrability hypotheses. -/
theorem h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) :
    velocityH3EnergyAt u y - velocityH3EnergyAt u x ≤
      ∫ s in x..y, max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s) := by
  obtain ⟨hDerivativeInt, hPositiveInt⟩ :=
    h3Critical_physicalGap_signedPositiveTransport_intervalIntegrable_automatic
      hH3 hClass x y hx hy hxy
  exact h3Critical_physicalGap_integratedSignedTransport_pays_energyGain
    hH3 hClass x y hx hy hxy hDerivativeInt hPositiveInt

/-- The original no-physical-L²-terminal-trace quintic source windows
unconditionally satisfy the integrated positive signed-transport budget.
The only hypotheses are those already used to select these windows.
In particular, neither finite full-H³-dissipation nor global signed
transport integrability is assumed. -/
theorem h3Critical_noL2Trace_cofinalQuintic_automaticIntegratedSignedGapBudget
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
        IntervalIntegrable (deriv (velocityH3EnergyAt u)) volume
          (t (v k) + δ k) (t (v (k + 1))) ∧
        IntervalIntegrable
          (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
            2 * velocityH3DissipationAt u s)) volume
          (t (v k) + δ k) (t (v (k + 1)))) ∧
      (∀ k : ℕ,
        (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        velocityH3EnergyAt u (t (v k) + δ k) +
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k ≤
          velocityH3EnergyAt u (t (v k))) ∧
      (∀ m : ℕ,
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
  obtain ⟨t, w, v, _A, _B, _R, δ, hv, hLimit,
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
    obtain ⟨_hs, _hw, _hEnd, _hR, _hδ, _hδw, _hWidth, hAlt⟩ := hWindows k
    exact hAlt
  have hGapTime (k : ℕ) : t (v k) + δ k < t (v (k + 1)) :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hGapEndpoints (k : ℕ) :
      t (v k) + δ k ∈ Set.Ioo a T ∧
      t (v (k + 1)) ∈ Set.Ioo a T := by
    obtain ⟨hStartK, _hwK, hEndK, _hRK, hδK, hδwK,
      _hWidthK, _hAltK⟩ := hWindows k
    obtain ⟨hStartL, _hwL, _hEndL, _hRL, _hδL, _hδwL,
      _hWidthL, _hAltL⟩ := hWindows (k + 1)
    have hx : t (v k) + δ k ∈ Set.Ioo a T := by
      have hStartA : a < t (v k) :=
        lt_trans hb.1 (lt_trans (hc (v k)).1 hStartK.1)
      have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
        add_le_add_right hδwK (t (v k))
      exact ⟨by linarith only [hStartA, hδK],
        lt_of_le_of_lt hShort hEndK⟩
    have hy : t (v (k + 1)) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v (k + 1))).1 hStartL.1), hStartL.2⟩
    exact ⟨hx, hy⟩
  have hRegular (k : ℕ) :
      IntervalIntegrable (deriv (velocityH3EnergyAt u)) volume
        (t (v k) + δ k) (t (v (k + 1))) ∧
      IntervalIntegrable
        (fun s : ℝ => max 0 (-velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s)) volume
        (t (v k) + δ k) (t (v (k + 1))) :=
    h3Critical_physicalGap_signedPositiveTransport_intervalIntegrable_automatic
      hH3 hClass _ _ (hGapEndpoints k).1 (hGapEndpoints k).2 (hGapTime k)
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
    dsimp only [x, y, G]
    exact h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic
      hH3 hClass _ _ (hGapEndpoints k).1 (hGapEndpoints k).2 (hGapTime k)
  have hFinite := h3Critical_scalar_finiteIntegratedGapDrainOrEnergy
    x y cost G P hStep hGap
  refine ⟨t, v, δ, hv, hLimit, ?_, hRegular, hWindowAlt, ?_⟩
  · intro k
    obtain ⟨_hs, _hw, _hEnd, _hR, hδ, _hδw, _hWidth, _hAlt⟩ := hWindows k
    exact ⟨hδ, hGapTime k⟩
  · intro m
    rcases hFinite m with ⟨k, hk, hp⟩ | hAccounting
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
