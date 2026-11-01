import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessSignedEnergyCompetition
import Mathlib.Tactic

/-!
# Source-driven signed H³ energy: endpoint drain and inter-window replenishment

On an existing enhanced-dissipation source window, the previously proved
pointwise alternative E' ≤ -H or H < K sqrt(E) E can be upgraded using
one-dimensional calculus to a **whole-window endpoint alternative**:

  either some time has H < K sqrt(E) E,
  or E(t+δ) + H δ ≤ E(t).

The exact physical energy is differentiable at every strict time, so the
endpoint result requires no a priori integrability of full dissipation.
Moreover any net energy gain from an earlier source window's endpoint to a
later source window's start forces a positive signed energy slope in the
gap, hence -Transport > 2 D at a genuine intermediate physical time.

All quantities refer to the original, already proved cofinal disjoint
quintic-source windows; we do not select different windows or assert
terminal summability or global continuation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Every strict-time physical H³ energy representative is differentiable,
by the established actual energy derivative identities. -/
theorem h3Critical_actualH3Energy_differentiableAt_onStrict
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    DifferentiableAt ℝ (velocityH3EnergyAt u) s := by
  have hIds : H3OrderEnergyDerivativeIdentities u s :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3 a hClass s hs
  exact (hasDerivAt_velocityH3EnergyAt hIds).differentiableAt

/-- Real-variable endpoint drain, obtained from the nonpositive derivative
of the shifted energy x ↦ E(x)+H*x. No integrability of E' is used. -/
theorem h3Critical_scalar_uniformDrain_forces_endpointCost
    (E : ℝ → ℝ) (t δ H : ℝ) (hδ : 0 ≤ δ)
    (hDiff : ∀ s ∈ Set.Icc t (t + δ), DifferentiableAt ℝ E s)
    (hDrain : ∀ s ∈ Set.Icc t (t + δ), deriv E s ≤ -H) :
    E (t + δ) + H * δ ≤ E t := by
  let F : ℝ → ℝ := E + fun s => H * s
  have hHas (s : ℝ) (hs : s ∈ Set.Icc t (t + δ)) :
      HasDerivAt F (deriv E s + H) s := by
    simpa only [F] using
      ((hDiff s hs).hasDerivAt.add
        (hasDerivAt_const_mul (x := s) H))
  have hDiffOn : DifferentiableOn ℝ F (Set.Icc t (t + δ)) := by
    intro s hs
    exact (hHas s hs).differentiableAt.differentiableWithinAt
  have hAnti : AntitoneOn F (Set.Icc t (t + δ)) := by
    refine antitoneOn_of_deriv_nonpos
      (convex_Icc t (t + δ))
      hDiffOn.continuousOn
      (hDiffOn.mono interior_subset) ?_
    intro s hs
    have hsIcc : s ∈ Set.Icc t (t + δ) := interior_subset hs
    rw [(hHas s hsIcc).deriv]
    linarith only [hDrain s hsIcc]
  have hStart : t ∈ Set.Icc t (t + δ) := by
    constructor <;> linarith only [hδ]
  have hEnd : t + δ ∈ Set.Icc t (t + δ) := by
    constructor <;> linarith only [hδ]
  have hBound := hAnti hStart hEnd (by linarith only [hδ])
  simp only [F, Pi.add_apply] at hBound
  linarith only [hBound]

/-- A pointwise signed drain / Riccati alternative yields a whole-window
endpoint drain, unless at least one actual time pays the Riccati energy cost.
This is valid for negative signed energy slopes and does not integrate D. -/
theorem h3Critical_scalar_signedCompetition_forces_endpointOrRiccati
    (E : ℝ → ℝ) (t δ H K : ℝ) (hδ : 0 ≤ δ)
    (hDiff : ∀ s ∈ Set.Icc t (t + δ), DifferentiableAt ℝ E s)
    (hComp : ∀ s ∈ Set.Icc t (t + δ),
      deriv E s ≤ -H ∨ H < K * Real.sqrt (E s) * E s) :
    (∃ s : ℝ, s ∈ Set.Icc t (t + δ) ∧
      H < K * Real.sqrt (E s) * E s) ∨
    E (t + δ) + H * δ ≤ E t := by
  by_cases hLarge : ∃ s : ℝ, s ∈ Set.Icc t (t + δ) ∧
      H < K * Real.sqrt (E s) * E s
  · exact Or.inl hLarge
  · right
    apply h3Critical_scalar_uniformDrain_forces_endpointCost E t δ H hδ hDiff
    intro s hs
    rcases hComp s hs with hDrain | hCost
    · exact hDrain
    · exact False.elim (hLarge ⟨s, hs, hCost⟩)

/-- Every actual source-excess persistence window has a certified endpoint
energy drain unless the genuine H³ Riccati energy cost is attained somewhere
on the SAME window. The only physical premise is the already proved full
viscous floor. -/
theorem h3Critical_sourceExcessWindow_endpointDrain_or_RiccatiEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t δ H : ℝ)
    (ht : t ∈ Set.Ioo a T)
    (hδ : 0 ≤ δ) (hEnd : t + δ < T)
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      H < velocityH3DissipationAt u s) :
    (∃ s : ℝ, s ∈ Set.Icc t (t + δ) ∧
      H < h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
    velocityH3EnergyAt u (t + δ) + H * δ ≤
      velocityH3EnergyAt u t := by
  have hInside (s : ℝ) (hs : s ∈ Set.Icc t (t + δ)) :
      s ∈ Set.Ioo a T := by
    exact ⟨lt_of_lt_of_le ht.1 hs.1,
      lt_of_le_of_lt hs.2 hEnd⟩
  have hDiff : ∀ s ∈ Set.Icc t (t + δ),
      DifferentiableAt ℝ (velocityH3EnergyAt u) s := by
    intro s hs
    exact h3Critical_actualH3Energy_differentiableAt_onStrict
      hH3 hClass (hInside s hs)
  have hComp : ∀ s ∈ Set.Icc t (t + δ),
      deriv (velocityH3EnergyAt u) s ≤ -H ∨
        H < h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s := by
    intro s hs
    exact h3Critical_fullDissipationFloor_signedDrainOrRiccati
      hH3 hClass (hInside s hs) H (hFloor s hs)
  exact h3Critical_scalar_signedCompetition_forces_endpointOrRiccati
    (velocityH3EnergyAt u) t δ H
    h3PathSqrtEnergyRiccatiCoefficient hδ hDiff hComp

/-- A net H³ energy increase between two strictly separated times forces
an actual strictly positive energy derivative in their interior. This uses
scalar antitonicity by contradiction, not derivative integrability. -/
theorem h3Critical_scalar_endpointReplenishment_forces_positiveSlope
    (E : ℝ → ℝ) (x y : ℝ) (hxy : x < y)
    (hDiff : ∀ s ∈ Set.Icc x y, DifferentiableAt ℝ E s)
    (hGain : E x < E y) :
    ∃ s : ℝ, s ∈ Set.Ioo x y ∧ 0 < deriv E s := by
  by_contra hNone
  have hDiffOn : DifferentiableOn ℝ E (Set.Icc x y) := by
    intro s hs
    exact (hDiff s hs).differentiableWithinAt
  have hAnti : AntitoneOn E (Set.Icc x y) := by
    refine antitoneOn_of_deriv_nonpos
      (convex_Icc x y) hDiffOn.continuousOn
      (hDiffOn.mono interior_subset) ?_
    intro s hsInterior
    have hs : s ∈ Set.Ioo x y := by
      simpa only [interior_Icc] using hsInterior
    exact le_of_not_gt (fun hPositive => hNone ⟨s, hs, hPositive⟩)
  have hBound : E y ≤ E x :=
    hAnti ⟨le_refl _, hxy.le⟩ ⟨hxy.le, le_refl _⟩ hxy.le
  exact (not_lt_of_ge hBound) hGain

/-- If actual physical H³ energy is replenished between already separated
source windows, exact signed Navier--Stokes energy balance identifies a
strict positive transport overshoot at a real intermediate physical time. -/
theorem h3Critical_interWindowH3Replenishment_forces_signedTransportOvershoot
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y)
    (hGain : velocityH3EnergyAt u x < velocityH3EnergyAt u y) :
    ∃ s : ℝ, s ∈ Set.Ioo x y ∧
      2 * velocityH3DissipationAt u s <
        -velocityH3TransportDerivativeAt u s := by
  have hDiff (s : ℝ) (hs : s ∈ Set.Icc x y) :
      DifferentiableAt ℝ (velocityH3EnergyAt u) s := by
    have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
    exact h3Critical_actualH3Energy_differentiableAt_onStrict
      hH3 hClass hsClass
  obtain ⟨s, hs, hSlope⟩ :=
    h3Critical_scalar_endpointReplenishment_forces_positiveSlope
      (velocityH3EnergyAt u) x y hxy hDiff hGain
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hx.1 hs.1, lt_trans hs.2 hy.2⟩
  have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass hsClass
  refine ⟨s, hs, ?_⟩
  linarith only [hBalance, hSlope]

/-- On the existing cofinal, separated quintic-source windows, each energy
interval has a certified drain-or-Riccati endpoint alternative. Between any
two of these same windows, an actual recovery of endpoint H³ energy forces
strict signed transport expenditure in the intervening gap. The original
extended physical costs and local quintic gate are preserved. -/
theorem h3Critical_noL2Trace_cofinalQuintic_endpointDrain_or_gapTransport
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
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ A B R δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        1 ≤ R k ∧ 0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        ((∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
              h3PathSqrtEnergyRiccatiCoefficient *
                Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
          velocityH3EnergyAt u (t (v k) + δ k) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k ≤
            velocityH3EnergyAt u (t (v k)))) ∧
      (∀ k l : ℕ, k < l →
        velocityH3EnergyAt u (t (v k) + δ k) <
          velocityH3EnergyAt u (t (v l)) →
        ∃ s : ℝ, s ∈ Set.Ioo (t (v k) + δ k) (t (v l)) ∧
          2 * velocityH3DissipationAt u s <
            -velocityH3TransportDerivativeAt u s) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ, ∀ J : ℝ, 0 < J →
        (∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
            ENNReal.ofReal J →
        w (v k) ≤ J / h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (q (v k)) ∨
        (q (v k) ≤
            16 * (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
              (max 1 (σ (v k)) + 1) ^ 4 ∨
          16 * (q (v k)) ^ 5 ≤
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
              ((A k) ^ 2 * (B k)) ^ 2)) := by
  obtain ⟨t, w, v, A, B, R, δ, hv, hLimit, hWindows,
      hSeparated, hCosts, hGate⟩ :=
    h3Critical_noL2Trace_cofinalQuintic_signedH3EnergyCompetition
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, A, B, R, δ, hv, hLimit, hSeparated, ?_, ?_, hCosts, hGate⟩
  · intro k
    obtain ⟨hStart, hw, hEnd, hR, hδ, hδw, hWidth, hPoint⟩ := hWindows k
    have ht : t (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v k)).1 hStart.1), hStart.2⟩
    have hEndSmall : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right hδw (t (v k))
    have hTerminal : t (v k) + δ k < T :=
      lt_of_le_of_lt hEndSmall hEnd
    have hFloor (s : ℝ) (hs : s ∈ Set.Icc (t (v k)) (t (v k) + δ k)) :
        h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
          velocityH3DissipationAt u s :=
      (hPoint s hs).1
    exact ⟨hStart, hw, hEnd, hR, hδ, hδw, hWidth,
      h3Critical_sourceExcessWindow_endpointDrain_or_RiccatiEnergy
        hH3 hClass (t (v k)) (δ k)
        (h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))
        ht hδ.le hTerminal hFloor⟩
  · intro k l hkl hGain
    have hklTime : t (v k) + δ k < t (v l) := hSeparated k l hkl
    obtain ⟨hStartK, _hwK, hEndK, _hRK, hδK, hδwK, _hWidthK, _hPointK⟩ :=
      hWindows k
    obtain ⟨hStartL, _hwL, _hEndL, _hRL, _hδL, _hδwL, _hWidthL, _hPointL⟩ :=
      hWindows l
    have hx : t (v k) + δ k ∈ Set.Ioo a T := by
      have hStartA : a < t (v k) :=
        lt_trans hb.1 (lt_trans (hc (v k)).1 hStartK.1)
      have hSmall : t (v k) + δ k ≤ t (v k) + w (v k) :=
        add_le_add_right hδwK (t (v k))
      exact ⟨by linarith only [hStartA, hδK],
        lt_of_le_of_lt hSmall hEndK⟩
    have hy : t (v l) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v l)).1 hStartL.1), hStartL.2⟩
    exact h3Critical_interWindowH3Replenishment_forces_signedTransportOvershoot
      hH3 hClass _ _ hx hy hklTime hGain

end
end PrimeTensor.Bridge.Euclidean
