import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellCumulativeSignedReplenishment
import Mathlib.Tactic

/-!
# Every-tail minimal H3 signed transport compensation, not one fixed prefix

An early Riccati-heavy window cannot pay for every later cubic dissipation
charge. The accepted cumulative theorem applies from a fixed finite prefix;
we upgrade its scalar accounting to EVERY shifted finite block on exactly the
same selected physical minimal first crossings and disjoint PDE clocks.

A finite positive signed-gap budget and unbounded cubic charges on every tail
then force Riccati-heavy windows at arbitrarily late selected indices.
The budgeted-gap and divergent-tail-charge premises are EXPLICIT; neither
is claimed to follow from Navier--Stokes or from the existing sixth/ninth
PDE alternative. No terminal full-H3 dissipation integrability is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeEveryTailSigned
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceEveryTailSigned :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Shift-invariant finite-block scalar accounting. The terminal energy
floor is kept, so the last value of y is replaced with the same fixed 1
for EVERY starting index, rather than only for the original first block. -/
theorem h3Critical_scalar_everyTailFiniteDrainOrRiccati
    (x y c G : ℕ → ℝ) (P : ℕ → Prop)
    (hy : ∀ k, 1 ≤ y k)
    (hStep : ∀ k, P k ∨ c k + y k ≤ x k)
    (hGap : ∀ k, x (k + 1) - y k ≤ G k) :
    ∀ b q : ℕ,
      (∃ i : ℕ, i ≤ q ∧ P (i + b)) ∨
      (∑ i ∈ Finset.range (q + 1), c (i + b)) + 1 ≤
        x b + ∑ i ∈ Finset.range q, G (i + b) := by
  intro b q
  let xs : ℕ → ℝ := fun i => x (i + b)
  let ys : ℕ → ℝ := fun i => y (i + b)
  let cs : ℕ → ℝ := fun i => c (i + b)
  let gs : ℕ → ℝ := fun i => G (i + b)
  let Ps : ℕ → Prop := fun i => P (i + b)
  have hs (i : ℕ) : Ps i ∨ cs i + ys i ≤ xs i := hStep (i + b)
  have hg (i : ℕ) : xs (i + 1) - ys i ≤ gs i := by
    change x ((i + 1) + b) - y (i + b) ≤ G (i + b)
    rw [show (i + 1) + b = (i + b) + 1 by omega]
    exact hGap (i + b)
  rcases h3Critical_scalar_finiteIntegratedGapDrainOrEnergy
      xs ys cs gs Ps hs hg q with ⟨i, hi, hp⟩ | hBound
  · exact Or.inl ⟨i, hi, hp⟩
  · right
    have hY : 1 ≤ ys q := hy (q + b)
    have hProof : (∑ i ∈ Finset.range (q + 1), cs i) + 1 ≤
        xs 0 + ∑ i ∈ Finset.range q, gs i := by
      linarith only [hBound, hY]
    simpa only [xs, cs, gs, Nat.zero_add] using hProof

/-- If every tail carries arbitrarily large certified charges while the
positive signed-gap replenishment is bounded on every tail, then actual
Riccati exceptions recur beyond every finite index. The two asymptotic
premises are genuinely distinct and are not silently inferred. -/
theorem h3Critical_scalar_boundedGap_unboundedTailCharge_forces_cofinalRiccati
    (x y c G : ℕ → ℝ) (P : ℕ → Prop)
    (hy : ∀ k, 1 ≤ y k)
    (hStep : ∀ k, P k ∨ c k + y k ≤ x k)
    (hGap : ∀ k, x (k + 1) - y k ≤ G k)
    (hCharge : ∀ b : ℕ, ∀ M : ℝ,
      ∃ q : ℕ, M < ∑ i ∈ Finset.range (q + 1), c (i + b))
    (hBudget : ∀ b : ℕ, ∃ B : ℝ, ∀ q : ℕ,
      (∑ i ∈ Finset.range q, G (i + b)) ≤ B) :
    ∀ b : ℕ, ∃ k : ℕ, b ≤ k ∧ P k := by
  intro b
  obtain ⟨B, hB⟩ := hBudget b
  obtain ⟨q, hLarge⟩ := hCharge b (x b + B - 1)
  rcases h3Critical_scalar_everyTailFiniteDrainOrRiccati
      x y c G P hy hStep hGap b q with ⟨i, hi, hp⟩ | hAccounting
  · exact ⟨i + b, by omega, hp⟩
  · have hBound := hB q
    exfalso
    linarith only [hLarge, hAccounting, hBound]

/-- The actual Riccati-amplitude branch on a selected minimal window. -/
def h3CriticalMinimalShellRiccatiWindowAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ s : ℝ,
    s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) ∧
    ((v k : ℝ) + 1) ^ 3 / 2 <
      h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s

/-- Original certified cubic window cost, without replacement cutoffs. -/
noncomputable def h3CriticalMinimalShellCubicWindowCost
    (δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ) : ℝ :=
  δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)

/-- Positive part of the exact signed H3 energy replenishment on the gap
after the original selected PDE window. -/
noncomputable def h3CriticalMinimalShellSignedGapIntegral
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ) : ℝ :=
  ∫ s in (t (v k) + δ (v k))..(t (v (k + 1))),
    max 0 (-velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s)

/-- Every shifted finite block is paid by initial physical H3 energy plus
its actual signed-gap compensation, unless THAT BLOCK contains a Riccati
exception. The final 1 is the actual positive physical energy floor. -/
def h3CriticalMinimalShellEveryTailSignedAccounting
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k₁ : ℕ) : Prop :=
  ∀ b q : ℕ,
    (∃ i : ℕ, i ≤ q ∧
      h3CriticalMinimalShellRiccatiWindowAt u t δ v ((i + b) + k₁)) ∨
    (∑ i ∈ Finset.range (q + 1),
      h3CriticalMinimalShellCubicWindowCost δ v ((i + b) + k₁)) + 1 ≤
      velocityH3EnergyAt u (t (v (b + k₁))) +
        ∑ i ∈ Finset.range q,
          h3CriticalMinimalShellSignedGapIntegral u t δ v ((i + b) + k₁)

/-- Additional condition: every late physical tail has unbounded certified
cubic charges. It is NOT asserted by the sixth/ninth alternative. -/
def h3CriticalMinimalShellEveryTailCubicChargeUnbounded
    (δ : ℕ → ℝ) (v : ℕ → ℕ) (k₁ : ℕ) : Prop :=
  ∀ b : ℕ, ∀ M : ℝ, ∃ q : ℕ,
    M < ∑ i ∈ Finset.range (q + 1),
      h3CriticalMinimalShellCubicWindowCost δ v ((i + b) + k₁)

/-- Additional condition: the genuine positive signed-gap integrals have
bounded partial sums on each selected tail. This does not follow from
compact-interval integrability alone. -/
def h3CriticalMinimalShellEveryTailGapBudget
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k₁ : ℕ) : Prop :=
  ∀ b : ℕ, ∃ B : ℝ, ∀ q : ℕ,
    (∑ i ∈ Finset.range q,
      h3CriticalMinimalShellSignedGapIntegral u t δ v ((i + b) + k₁)) ≤ B

/-- Same physical minimal first-crossing, source, kinetic and signed PDE
witnesses, strengthened to every-tail signed accounting. Under explicit
divergent cubic charges and bounded positive gap transport, infinitely far
Riccati-heavy physical windows are forced on this SAME selector. -/
theorem h3Critical_noL2Trace_minimalShell_everyTailSignedRiccatiOrGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ, ∃ k₁ : ℕ,
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
      (∀ k : ℕ, k₁ ≤ k →
        h3CriticalMinimalShellSignedTransportBudgetAt
          hH3 (t (v k)) (v k) (δ (v k))) ∧
      h3CriticalMinimalShellEveryTailSignedAccounting u t δ v k₁ ∧
      (h3CriticalMinimalShellEveryTailCubicChargeUnbounded δ v k₁ →
        h3CriticalMinimalShellEveryTailGapBudget u t δ v k₁ →
        ∀ b : ℕ, ∃ i : ℕ, b ≤ i ∧
          h3CriticalMinimalShellRiccatiWindowAt u t δ v (i + k₁)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₀, hv, hLimit, hSeparate,
      hWindow, hRates, hEnergyWidth, hShell, hSigned, _hAccounting⟩ :=
    h3Critical_noL2Trace_minimalShell_cumulativeSignedReplenishment
      hH3 hClass hNoTrace
  have hTailTime : ∀ᶠ k : ℕ in atTop, a < t (v k) := by
    have hOpen : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact hLimit.eventually hOpen
  obtain ⟨kTime, hkTime⟩ := Filter.eventually_atTop.1 hTailTime
  let k₁ : ℕ := max k₀ kTime
  have hLate (k : ℕ) (hk : k₁ ≤ k) :
      a < t (v k) ∧
      h3CriticalMinimalShellSignedTransportBudgetAt
        hH3 (t (v k)) (v k) (δ (v k)) := by
    exact ⟨hkTime k ((le_max_right _ _).trans hk),
      hSigned k ((le_max_left _ _).trans hk)⟩
  have hStart (i : ℕ) : t (v (i + k₁)) ∈ Set.Ioo a T := by
    have ha := (hLate (i + k₁) (by omega)).1
    rcases hWindow (i + k₁) with ⟨_, _, _, _, hδ, hEnd, _⟩
    exact ⟨ha, by linarith only [hδ, hEnd]⟩
  let x : ℕ → ℝ := fun i => velocityH3EnergyAt u (t (v (i + k₁)))
  let y : ℕ → ℝ := fun i =>
    velocityH3EnergyAt u (t (v (i + k₁)) + δ (v (i + k₁)))
  let c : ℕ → ℝ := fun i =>
    h3CriticalMinimalShellCubicWindowCost δ v (i + k₁)
  let G : ℕ → ℝ := fun i =>
    h3CriticalMinimalShellSignedGapIntegral u t δ v (i + k₁)
  let P : ℕ → Prop := fun i =>
    h3CriticalMinimalShellRiccatiWindowAt u t δ v (i + k₁)
  have hy (i : ℕ) : 1 ≤ y i := by
    dsimp only [y]
    exact one_le_velocityH3EnergyAt u _
  have hs (i : ℕ) : P i ∨ c i + y i ≤ x i := by
    have hLocal := h3Critical_minimalShellSignedWindow_integratedDrainOrRiccati
      hH3 hClass (t (v (i + k₁))) (hStart i)
      (v (i + k₁)) (N (v (i + k₁))) (m (v (i + k₁)))
      (C (v (i + k₁))) (δ (v (i + k₁)))
      (hWindow (i + k₁)) (hLate (i + k₁) (by omega)).2
    rcases hLocal with hp | hd
    · exact Or.inl hp
    · right
      dsimp only [c, y, x, h3CriticalMinimalShellCubicWindowCost]
      calc
        _ = velocityH3EnergyAt u
              (t (v (i + k₁)) + δ (v (i + k₁))) +
              δ (v (i + k₁)) *
                (((v (i + k₁) : ℝ) + 1) ^ 3 / 2) := add_comm _ _
        _ ≤ velocityH3EnergyAt u (t (v (i + k₁))) := hd
  have hg (i : ℕ) : x (i + 1) - y i ≤ G i := by
    have hx : t (v (i + k₁)) + δ (v (i + k₁)) ∈ Set.Ioo a T := by
      have ht := hStart i
      rcases hWindow (i + k₁) with ⟨_, _, _, _, hδ, hEnd, _⟩
      exact ⟨by linarith only [ht.1, hδ], hEnd⟩
    have he : t (v ((i + 1) + k₁)) ∈ Set.Ioo a T := hStart (i + 1)
    have hSep : t (v (i + k₁)) + δ (v (i + k₁)) <
        t (v ((i + 1) + k₁)) :=
      hSeparate (i + k₁) ((i + 1) + k₁) (by omega)
    dsimp only [x, y, G, h3CriticalMinimalShellSignedGapIntegral]
    have hIndex : i + k₁ + 1 = i + 1 + k₁ := by omega
    simpa only [hIndex] using
      (h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic
        hH3 hClass _ _ hx he hSep)
  have hBlock := h3Critical_scalar_everyTailFiniteDrainOrRiccati
    x y c G P hy hs hg
  have hEvery : h3CriticalMinimalShellEveryTailSignedAccounting u t δ v k₁ := by
    intro b q
    rcases hBlock b q with ⟨i, hi, hp⟩ | hBound
    · exact Or.inl ⟨i, hi, hp⟩
    · right
      simpa only [x, c, G, h3CriticalMinimalShellCubicWindowCost,
        h3CriticalMinimalShellSignedGapIntegral] using hBound
  refine ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
    hWindow, hRates, hEnergyWidth, hShell, ?_, hEvery, ?_⟩
  · intro k hk
    exact (hLate k hk).2
  · intro hCharge hBudget b
    have hCharge' : ∀ p : ℕ, ∀ M : ℝ,
        ∃ q : ℕ, M < ∑ i ∈ Finset.range (q + 1), c (i + p) := by
      intro p M
      simpa only [c] using hCharge p M
    have hBudget' : ∀ p : ℕ, ∃ B : ℝ, ∀ q : ℕ,
        (∑ i ∈ Finset.range q, G (i + p)) ≤ B := by
      intro p
      simpa only [G] using hBudget p
    exact h3Critical_scalar_boundedGap_unboundedTailCharge_forces_cofinalRiccati
      x y c G P hy hs hg hCharge' hBudget' b

end
end PrimeTensor.Bridge.Euclidean
