import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAutomaticIntegratedGapTransport
import Mathlib.Tactic

/-!
# Physical gradient-energy budget for signed transport replenishment

The existing quintic-source windows force genuine viscous H³ dissipation.
The intervening gaps can replenish that energy only through positive signed
nonlinear transport. The exact physical H³ transport commutator bounds its
positive surplus by the continuous canonical gradient-energy profile

  4422 * (1 + |h(t)|) * E(t),

where h is the established canonical square-root-energy C¹-gradient envelope.
The bound is integrated on each actual compact gap and telescoped across the
original cofinal source windows. No terminal-uniform estimate for h or E is
asserted, and no terminal-integrability premise is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual signed transport surplus, after retaining both copies of
viscosity, is bounded at each strict-time slice by the established physical
H³ commutator coefficient times the actual H³ energy. -/
theorem h3Critical_positiveSignedTransport_le_canonicalGradientEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s) ≤
      (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
        velocityH3EnergyAt u s := by
  let G : ℝ :=
    (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
      velocityH3EnergyAt u s
  have hE : 0 ≤ velocityH3EnergyAt u s :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_velocityH3EnergyAt u s)
  have hG : 0 ≤ G := by
    dsimp only [G]
    positivity
  have hTransport : |velocityH3TransportDerivativeAt u s| ≤ G := by
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass
      (fun q hq => h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hq)
      s hs).2
  have hViscous : 0 ≤ velocityH3DissipationAt u s :=
    velocityH3DissipationAt_nonneg u s
  have hNeg : -velocityH3TransportDerivativeAt u s ≤
      |velocityH3TransportDerivativeAt u s| := neg_le_abs _
  have hUpper : -velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s ≤ G := by
    linarith only [hTransport, hViscous, hNeg]
  change max 0 (-velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s) ≤ G
  exact max_le hG hUpper

/-- The physical gradient-energy cost profile is interval-integrable on
EVERY compact strict-time H³ energy-class subinterval. No terminal estimate
is used: both factors are continuous on the strict energy-class tail. -/
theorem h3Critical_canonicalGradientEnergy_intervalIntegrable_onGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x ≤ y) :
    IntervalIntegrable
      (fun s : ℝ =>
        (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
          velocityH3EnergyAt u s) volume x y := by
  have hEnergyCont : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo a T) :=
    continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass
  have hCoeffCont : ContinuousOn
      (fun s : ℝ =>
        4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|))
      (Set.Ioo a T) :=
    continuousOn_h3PathCanonicalSqrtEnergyGradientCoefficient_on_energyClassTail
      hH3 hClass
  have hSubset : Set.Icc x y ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
  exact ((hCoeffCont.mul hEnergyCont).mono hSubset).intervalIntegrable_of_Icc hxy

/-- An actual strict physical gap can receive no more positive signed H³
transport energy than the interval integral of the canonical gradient-energy
commutator. This is a genuine integral over the original physical time gap,
not the earlier single mean-value sample. -/
theorem h3Critical_physicalGap_positiveTransportIntegral_le_gradientEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) :
    (∫ s in x..y,
      max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)) ≤
    ∫ s in x..y,
      (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
        velocityH3EnergyAt u s := by
  have hPositiveInt :=
    (h3Critical_physicalGap_signedPositiveTransport_intervalIntegrable_automatic
      hH3 hClass x y hx hy hxy).2
  have hGradientInt :=
    h3Critical_canonicalGradientEnergy_intervalIntegrable_onGap
      hH3 hClass x y hx hy hxy.le
  apply intervalIntegral.integral_mono_on hxy.le hPositiveInt hGradientInt
  intro s hs
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
  exact h3Critical_positiveSignedTransport_le_canonicalGradientEnergy
    hH3 hClass hsClass

/-- On the SAME cofinal quintic source-excess windows as before, the finite
sum of genuine enhanced full-H³ dissipation charges must be paid either by
some actual large-Riccati-energy observation, or by the initial H³ energy
plus the continuous physical gradient-energy cost integrated in the gaps.
There is no terminal-uniform bound on the canonical gradient coefficient. -/
theorem h3Critical_noL2Trace_cofinalQuintic_gradientTransportBudget
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
        IntervalIntegrable
          (fun s : ℝ =>
            (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
              velocityH3EnergyAt u s) volume
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
                (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
                  velocityH3EnergyAt u s) := by
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
      (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
        velocityH3EnergyAt u s
  have hStep (k : ℕ) : P k ∨ cost k + y k ≤ x k := by
    rcases hWindowAlt k with hLarge | hDrain
    · exact Or.inl hLarge
    · right
      dsimp only [cost, y, x]
      linarith only [hDrain]
  have hGap (k : ℕ) : x (k + 1) - y k ≤ G k := by
    dsimp only [x, y, G]
    calc
      velocityH3EnergyAt u (t (v (k + 1))) -
          velocityH3EnergyAt u (t (v k) + δ k) ≤
        ∫ s in (t (v k) + δ k)..(t (v (k + 1))),
          max 0 (-velocityH3TransportDerivativeAt u s -
            2 * velocityH3DissipationAt u s) :=
        h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic
          hH3 hClass _ _ (hGapEndpoints k).1 (hGapEndpoints k).2 (hGapTime k)
      _ ≤ ∫ s in (t (v k) + δ k)..(t (v (k + 1))),
          (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
            velocityH3EnergyAt u s :=
        h3Critical_physicalGap_positiveTransportIntegral_le_gradientEnergy
          hH3 hClass _ _ (hGapEndpoints k).1 (hGapEndpoints k).2 (hGapTime k)
  have hFinite := h3Critical_scalar_finiteIntegratedGapDrainOrEnergy
    x y cost G P hStep hGap
  refine ⟨t, v, δ, hv, hLimit, ?_, ?_, hWindowAlt, ?_⟩
  · intro k
    obtain ⟨_hs, _hw, _hEnd, _hR, hδ, _hδw, _hWidth, _hAlt⟩ := hWindows k
    exact ⟨hδ, hGapTime k⟩
  · intro k
    exact h3Critical_canonicalGradientEnergy_intervalIntegrable_onGap
      hH3 hClass _ _ (hGapEndpoints k).1 (hGapEndpoints k).2 (hGapTime k).le
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
