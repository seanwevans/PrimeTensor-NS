import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellSignedTransportBudget
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAutomaticIntegratedGapTransport
import Mathlib.Tactic

/-!
# Minimal-shell cubic drain versus actual integrated signed-gap replenishment

The original strictly disjoint canonical first-crossing windows obey
  E'(s) + R^3 < -Transport_H3(s).
In particular, at each time either E'(s) <= -R^3/2 or the true
Riccati nonlinear energy factor exceeds R^3/2. If the latter never
happens on a window, the exact physical energy loses at least delta R^3/2.

The compact-gap FTC and positive-part of the actual signed transport
then telescope these charges over the ORIGINAL cofinal selector. We shift
past a finite prefix because the signed window theorem is eventually true.
No full-terminal H3 dissipation integral or globally integrable transport
is assumed. The Riccati arm is an actual exception, not eliminated.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalCumulativeSigned
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalCumulativeSigned :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A uniform negative derivative on a compact interval gives a real
endpoint energy drain. Uses the genuine Lebesgue/FTC derivative identity. -/
theorem h3Critical_scalar_uniformNegativeDerivative_forces_intervalDrain
    (E : ℝ → ℝ) (x y H : ℝ) (hxy : x < y)
    (hDiff : ∀ s : ℝ, s ∈ Set.Icc x y → DifferentiableAt ℝ E s)
    (hDerivInt : IntervalIntegrable (deriv E) volume x y)
    (hSlope : ∀ s : ℝ, s ∈ Set.Icc x y → deriv E s ≤ -H) :
    E y + (y - x) * H ≤ E x := by
  have hConstInt : IntervalIntegrable (fun _ : ℝ => -H) volume x y :=
    intervalIntegrable_const
  have hFTC := h3Critical_scalar_gapIntegratedMajorant_pays_energyGain
    E (fun _ : ℝ => -H) x y hxy hDiff hDerivInt hConstInt hSlope
  have hIntegral : (∫ _s in x..y, (-H)) = -(y - x) * H := by
    simp [intervalIntegral.integral_const]
    ring
  rw [hIntegral] at hFTC
  linarith only [hFTC]

/-- On an original minimal first-crossing physical PDE window, either an
actual time realizes the nonlinear Riccati cost, or the H3 endpoint energy
loses at least the certified cubic annular charge. There is no extra
assumption on the energy slope. -/
theorem h3Critical_minimalShellSignedWindow_integratedDrainOrRiccati
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n N m : ℕ) (C δ : ℝ)
    (hWindow : h3CriticalMinimalShellEnergyWindow hH3 t n N m C δ)
    (hSigned : h3CriticalMinimalShellSignedTransportBudgetAt hH3 t n δ) :
    (∃ s : ℝ, s ∈ Set.Icc t (t + δ) ∧
       ((n : ℝ) + 1) ^ 3 / 2 <
         h3PathSqrtEnergyRiccatiCoefficient *
           Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
    velocityH3EnergyAt u (t + δ) +
      δ * (((n : ℝ) + 1) ^ 3 / 2) ≤ velocityH3EnergyAt u t := by
  let H : ℝ := ((n : ℝ) + 1) ^ 3 / 2
  by_cases hRiccati : ∃ s : ℝ, s ∈ Set.Icc t (t + δ) ∧
      H < h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s
  · exact Or.inl (by simpa only [H] using hRiccati)
  · right
    have hδ : 0 < δ := by
      rcases hWindow with ⟨_, _, _, _, hPositive, _⟩
      exact hPositive
    have hEnd : t + δ < T := by
      rcases hWindow with ⟨_, _, _, _, _, hBefore, _⟩
      exact hBefore
    have hEndTime : t + δ ∈ Set.Ioo a T := by
      exact ⟨by linarith only [ht.1, hδ], hEnd⟩
    have hSubset : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
      intro s hs
      exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
    have hDiff (s : ℝ) (hs : s ∈ Set.Icc t (t + δ)) :
        DifferentiableAt ℝ (velocityH3EnergyAt u) s :=
      h3Critical_actualH3Energy_differentiableAt_onStrict
        hH3 hClass (hSubset hs)
    have hDerivativeInt : IntervalIntegrable
        (deriv (velocityH3EnergyAt u)) volume t (t + δ) :=
      h3Path_canonicalEnergyDerivative_intervalIntegrable_automatic244
        hH3 hClass t (t + δ) ht hEndTime (by linarith only [hδ])
    have hSlope (s : ℝ) (hs : s ∈ Set.Icc t (t + δ)) :
        deriv (velocityH3EnergyAt u) s ≤ -H := by
      have hAlternative := (hSigned s hs).2.1
      rcases hAlternative with hDrain | hLarge
      · simpa only [H] using hDrain
      · exfalso
        exact hRiccati ⟨s, hs, by simpa only [H] using hLarge⟩
    have hDrain := h3Critical_scalar_uniformNegativeDerivative_forces_intervalDrain
      (velocityH3EnergyAt u) t (t + δ) H
      (by linarith only [hδ]) hDiff hDerivativeInt hSlope
    have hWidth : (t + δ - t) * H = δ * H := by ring
    rw [hWidth] at hDrain
    simpa only [H] using hDrain

/-- The SAME disjoint first-crossing selector, including physical anchor
energy and exact source-rate alternatives, satisfies finite signed accounting
on a terminal tail. Without a Riccati-heavy window, every sum of its cubic
costs is paid by initial H3 energy and the integrated POSITIVE signed
transport residual on the inter-window gaps. No terminal full-H3 integral. -/
theorem h3Critical_noL2Trace_minimalShell_cumulativeSignedReplenishment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ, ∃ k₀ : ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
        T t N C δ v ∧
      (∀ k : ℕ,
        1 < 4 * (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1)) *
          (((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) ^ 2) ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (∀ k : ℕ, k₀ ≤ k →
        h3CriticalMinimalShellSignedTransportBudgetAt
          hH3 (t (v k)) (v k) (δ (v k))) ∧
      (∀ q : ℕ,
        (∃ i : ℕ, i ≤ q ∧ ∃ s : ℝ,
          s ∈ Set.Icc (t (v (i + k₀)))
            (t (v (i + k₀)) + δ (v (i + k₀))) ∧
          ((v (i + k₀) : ℝ) + 1) ^ 3 / 2 <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        (∑ i ∈ Finset.range (q + 1),
          δ (v (i + k₀)) * (((v (i + k₀) : ℝ) + 1) ^ 3 / 2)) + 1 ≤
          velocityH3EnergyAt u (t (v k₀)) +
          ∑ i ∈ Finset.range q,
            ∫ s in (t (v (i + k₀)) + δ (v (i + k₀)))..
                (t (v ((i + 1) + k₀))),
              max 0 (-velocityH3TransportDerivativeAt u s -
                2 * velocityH3DissipationAt u s)) := by
  obtain ⟨t, N, m, C, δ, v, j, hv, hLimit, hSeparate,
      hWindow, _hSum, hRates, hShell, hEnergyWidth, hSigned⟩ :=
    h3Critical_noL2Trace_disjointMinimalShell_energyWidth_signedTransport
      hH3 hClass hNoTrace
  have hTail : ∀ᶠ k : ℕ in atTop,
      a < t (v k) ∧
      h3CriticalMinimalShellSignedTransportBudgetAt
        hH3 (t (v k)) (v k) (δ (v k)) := by
    have hOpen : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact (hLimit.eventually hOpen).and hSigned
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hTail
  have hLate (k : ℕ) (hk : k₀ ≤ k) :
      a < t (v k) ∧
      h3CriticalMinimalShellSignedTransportBudgetAt
        hH3 (t (v k)) (v k) (δ (v k)) := hk₀ k hk
  have hStart (i : ℕ) : t (v (i + k₀)) ∈ Set.Ioo a T := by
    have ha := (hLate (i + k₀) (by omega)).1
    have hw := hWindow (i + k₀)
    rcases hw with ⟨_, _, _, _, hδ, hEnd, _⟩
    exact ⟨ha, by linarith only [hδ, hEnd]⟩
  let x : ℕ → ℝ := fun i => velocityH3EnergyAt u (t (v (i + k₀)))
  let y : ℕ → ℝ := fun i =>
    velocityH3EnergyAt u (t (v (i + k₀)) + δ (v (i + k₀)))
  let cost : ℕ → ℝ := fun i =>
    δ (v (i + k₀)) * (((v (i + k₀) : ℝ) + 1) ^ 3 / 2)
  let P : ℕ → Prop := fun i => ∃ s : ℝ,
    s ∈ Set.Icc (t (v (i + k₀)))
      (t (v (i + k₀)) + δ (v (i + k₀))) ∧
    ((v (i + k₀) : ℝ) + 1) ^ 3 / 2 <
      h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s
  let G : ℕ → ℝ := fun i =>
    ∫ s in (t (v (i + k₀)) + δ (v (i + k₀)))..
        (t (v ((i + 1) + k₀))),
      max 0 (-velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s)
  have hStep (i : ℕ) : P i ∨ cost i + y i ≤ x i := by
    have hLocal := h3Critical_minimalShellSignedWindow_integratedDrainOrRiccati
      hH3 hClass (t (v (i + k₀))) (hStart i)
      (v (i + k₀)) (N (v (i + k₀))) (m (v (i + k₀)))
      (C (v (i + k₀))) (δ (v (i + k₀)))
      (hWindow (i + k₀)) (hLate (i + k₀) (by omega)).2
    rcases hLocal with hp | hd
    · exact Or.inl hp
    · right
      dsimp only [cost, y, x]
      calc
        _ = velocityH3EnergyAt u
              (t (v (i + k₀)) + δ (v (i + k₀))) +
              δ (v (i + k₀)) *
                (((v (i + k₀) : ℝ) + 1) ^ 3 / 2) := add_comm _ _
        _ ≤ velocityH3EnergyAt u (t (v (i + k₀))) := hd
  have hGap (i : ℕ) : x (i + 1) - y i ≤ G i := by
    have hs : t (v (i + k₀)) + δ (v (i + k₀)) ∈ Set.Ioo a T := by
      have ht := hStart i
      have hw := hWindow (i + k₀)
      rcases hw with ⟨_, _, _, _, hδ, hEnd, _⟩
      exact ⟨by linarith only [ht.1, hδ], hEnd⟩
    have he : t (v ((i + 1) + k₀)) ∈ Set.Ioo a T := hStart (i + 1)
    have hSep : t (v (i + k₀)) + δ (v (i + k₀)) <
        t (v ((i + 1) + k₀)) :=
      hSeparate (i + k₀) ((i + 1) + k₀) (by omega)
    exact h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic
      hH3 hClass _ _ hs he hSep
  refine ⟨t, N, m, C, δ, v, j, k₀, hv, hLimit, hSeparate,
    hWindow, hRates, (fun k => (hEnergyWidth k).1), hShell,
    (fun k hk => (hLate k hk).2), ?_⟩
  intro q
  have hFinite := h3Critical_scalar_finiteIntegratedGapDrainOrEnergy
    x y cost G P hStep hGap q
  rcases hFinite with ⟨i, hi, hp⟩ | hBound
  · exact Or.inl ⟨i, hi, hp⟩
  · right
    have hEndEnergy : 1 ≤ y q := by
      dsimp only [y]
      exact one_le_velocityH3EnergyAt u _
    have hFinal : (∑ i ∈ Finset.range (q + 1), cost i) + 1 ≤
        x 0 + ∑ i ∈ Finset.range q, G i := by
      calc
        (∑ i ∈ Finset.range (q + 1), cost i) + 1 ≤
            (∑ i ∈ Finset.range (q + 1), cost i) + y q :=
          by
            have hAdded := add_le_add_left hEndEnergy
              (∑ i ∈ Finset.range (q + 1), cost i)
            linarith only [hAdded]
        _ ≤ x 0 + ∑ i ∈ Finset.range q, G i := hBound
    simpa only [x, y, cost, G, Nat.zero_add] using hFinal

end
end PrimeTensor.Bridge.Euclidean
