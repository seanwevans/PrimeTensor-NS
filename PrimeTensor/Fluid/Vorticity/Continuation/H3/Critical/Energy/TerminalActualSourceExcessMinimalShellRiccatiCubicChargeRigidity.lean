import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiSourceHorizonClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostCollapse244
import Mathlib.Tactic

/-!
# Minimal-shell Riccati peaks: a fixed cubic charge or quadratic anchor energy

The inverse-root Riccati inequality gives a quantitative elapsed-time lower
bound for a genuine quadratic H3 peak starting from a small H3 anchor.
Because the peak lies *within the actual quadratic-sharp minimal-shell PDE
window*, this lower bound is on the SAME positive width δ, not merely the
remaining terminal horizon T-t.

At inner radius R=v(k)+1>=1, the small-anchor peak costs δ R>4, hence
its certified cubic dissipation charge δ R³/2 exceeds 2. For a sequence of
nonnegative disjoint charges with bounded finite partial sums, summability
forces the charges to tend to zero. Thus late Riccati-heavy windows with a
bounded total cubic charge MUST carry quadratic energy at their ORIGINAL
anchor. If the anchor is eventually below that threshold, Riccati windows
are eventually absent. All these statements keep the original minimal
cutoffs, physical clocks and signed-gap bookkeeping; no global terminal H3
dissipation integrability is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalCubicRigidity
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalCubicRigidity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- For R >= 1, the inverse-root peak's linear clock immediately costs
more than 2 units of the actual cubic persistence charge d*R³/2.
The bound is independent of any external PDE source ceiling. -/
theorem h3Critical_scalar_inverseRootPeak_anchorOrFixedCubicCharge
    (R K B E0 E1 d : ℝ)
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hBK : 4 * K ^ 2 ≤ B)
    (hE0 : 0 < E0) (hE1 : 0 < E1) (hd : 0 ≤ d)
    (hPeak : R ^ 2 < B * E1)
    (hInverse : (Real.sqrt E0)⁻¹ ≤
      (Real.sqrt E1)⁻¹ + (K / 2) * d) :
    R ^ 2 < 4 * B * E0 ∨ 2 < d * R ^ 3 / 2 := by
  have hRPos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  rcases h3Critical_scalar_inverseRootPeak_anchorOrLinearClock
      R K B E0 E1 d hRPos hK hB hBK hE0 hE1 hd
      hPeak hInverse with hAnchor | hClock
  · exact Or.inl hAnchor
  · right
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
    have hR3 : R ≤ R ^ 3 := by
      calc
        R = R * 1 := by ring
        _ ≤ R * R ^ 2 := mul_le_mul_of_nonneg_left hR2 hRPos.le
        _ = R ^ 3 := by ring
    have hScaled : d * R ≤ d * R ^ 3 :=
      mul_le_mul_of_nonneg_left hR3 hd
    nlinarith only [hClock, hScaled]

/-- The exact physical minimal-shell Riccati witness itself pays either
quadratic original anchor energy or a STRICT fixed cubic window charge >2.
No weakening to an entire terminal clock or new time window is made. -/
theorem h3Critical_minimalShellRiccatiWindow_anchorOrFixedCubicCharge
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (N m : ℕ → ℕ) (C : ℕ → ℝ)
    (k : ℕ)
    (ht : t (v k) ∈ Set.Ioo a T)
    (hWindow : h3CriticalMinimalShellEnergyWindow hH3
      (t (v k)) (v k) (N (v k)) (m (v k))
      (C (v k)) (δ (v k)))
    (hRiccati : h3CriticalMinimalShellRiccatiWindowAt u t δ v k) :
    ((v k : ℝ) + 1) ^ 2 <
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ∨
    2 < h3CriticalMinimalShellCubicWindowCost δ v k := by
  obtain ⟨s, hs, hPeak⟩ :=
    h3Critical_minimalShellRiccatiWindow_forces_quadraticEnergy
      u t δ v k hRiccati
  let R : ℝ := (v k : ℝ) + 1
  let K : ℝ := h3PathSqrtEnergyRiccatiCoefficient
  let B : ℝ := 4 * K ^ 2 + 1
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hK : 0 ≤ K := h3PathSqrtEnergyRiccatiCoefficient_nonneg
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith only [sq_nonneg K]
  have hBK : 4 * K ^ 2 ≤ B := by
    dsimp only [B]
    linarith
  have hE0 : 0 < velocityH3EnergyAt u (t (v k)) :=
    lt_of_lt_of_le (by norm_num) (one_le_velocityH3EnergyAt u _)
  have hE1 : 0 < velocityH3EnergyAt u s :=
    lt_of_lt_of_le (by norm_num) (one_le_velocityH3EnergyAt u s)
  have hEnd : t (v k) + δ (v k) < T := by
    rcases hWindow with ⟨_, _, _, _, _, he, _⟩
    exact he
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hMono := monotoneOn_h3PathInverseSqrtEnergyRiccatiShift
    hH3 hClass ht hsClass hs.1
  have hInverse :
      (Real.sqrt (velocityH3EnergyAt u (t (v k))))⁻¹ ≤
        (Real.sqrt (velocityH3EnergyAt u s))⁻¹ +
          (K / 2) * (s - t (v k)) := by
    change (Real.sqrt (velocityH3EnergyAt u (t (v k))))⁻¹ +
      (K / 2) * t (v k) ≤
      (Real.sqrt (velocityH3EnergyAt u s))⁻¹ + (K / 2) * s at hMono
    linarith only [hMono]
  have hPeak' : R ^ 2 < B * velocityH3EnergyAt u s := by
    simpa only [R, B, K] using hPeak
  have hAlt := h3Critical_scalar_inverseRootPeak_anchorOrFixedCubicCharge
    R K B (velocityH3EnergyAt u (t (v k)))
    (velocityH3EnergyAt u s) (s - t (v k))
    hR hK hB hBK hE0 hE1 (sub_nonneg.mpr hs.1)
    hPeak' hInverse
  rcases hAlt with hAnchor | hElapsed
  · exact Or.inl (by simpa only [R, B, K] using hAnchor)
  · right
    have hSpan : s - t (v k) ≤ δ (v k) := by
      linarith only [hs.2]
    have hR3 : 0 ≤ R ^ 3 := by
      have hR0 : 0 ≤ R := le_trans (by norm_num) hR
      positivity
    have hScaled := mul_le_mul_of_nonneg_right hSpan hR3
    have hDelta : 2 < δ (v k) * R ^ 3 / 2 := by
      nlinarith only [hElapsed, hScaled]
    have hReassociate : δ (v k) * R ^ 3 / 2 =
        δ (v k) * (R ^ 3 / 2) := by ring
    rw [hReassociate] at hDelta
    simpa only [h3CriticalMinimalShellCubicWindowCost, R] using hDelta

/-- The fixed-charge alternative is a property of a Riccati peak on a
*selected* minimal physical PDE window, not a separate PDE selector. -/
def h3CriticalMinimalShellRiccatiAnchorOrCubicChargeAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ) : Prop :=
  ((v k : ℝ) + 1) ^ 2 <
    4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
      velocityH3EnergyAt u (t (v k)) ∨
  2 < h3CriticalMinimalShellCubicWindowCost δ v k

/-- A bounded nonnegative series of certified disjoint cubic window costs
has individual cost <2 at every sufficiently late selected index. -/
theorem h3Critical_scalar_boundedNonnegativeCubicCosts_eventually_below_two
    (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, 0 ≤ c k)
    (B : ℝ)
    (hB : ∀ q : ℕ, (∑ k ∈ Finset.range q, c k) ≤ B) :
    ∀ᶠ k : ℕ in atTop, c k < 2 := by
  have hSum : Summable c := summable_of_sum_range_le hc hB
  have hZero : Tendsto c atTop (𝓝 (0 : ℝ)) := hSum.tendsto_atTop_zero
  exact hZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 2))

/-- Under bounded selected cubic charges, any late actual Riccati-heavy
window must have had quadratic H3 energy ALREADY at its original anchor.
The threshold 2 does not depend on the outer cutoff or source coefficient. -/
theorem h3Critical_minimalShell_boundedCubicCharges_force_lateRiccatiAnchors
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hc : ∀ k : ℕ, 0 ≤ h3CriticalMinimalShellCubicWindowCost δ v k)
    (hLocal : ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        h3CriticalMinimalShellRiccatiAnchorOrCubicChargeAt u t δ v k)
    (B : ℝ) (hB : ∀ q : ℕ,
      (∑ k ∈ Finset.range q,
        h3CriticalMinimalShellCubicWindowCost δ v k) ≤ B) :
    ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        ((v k : ℝ) + 1) ^ 2 <
          4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
            velocityH3EnergyAt u (t (v k)) := by
  have hSmall := h3Critical_scalar_boundedNonnegativeCubicCosts_eventually_below_two
    (h3CriticalMinimalShellCubicWindowCost δ v) hc B hB
  filter_upwards [hSmall, hLocal] with k hk hl
  intro hRic
  rcases hl hRic with hAnchor | hCost
  · exact hAnchor
  · exfalso
    linarith only [hk, hCost]

/-- If the same bounded-charge selector has eventually insufficient
quadratic anchor energy, it cannot have arbitrarily late Riccati peaks. -/
theorem h3Critical_minimalShell_boundedCubicCharges_smallAnchor_excludes_lateRiccati
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hc : ∀ k : ℕ, 0 ≤ h3CriticalMinimalShellCubicWindowCost δ v k)
    (hLocal : ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        h3CriticalMinimalShellRiccatiAnchorOrCubicChargeAt u t δ v k)
    (B : ℝ) (hB : ∀ q : ℕ,
      (∑ k ∈ Finset.range q,
        h3CriticalMinimalShellCubicWindowCost δ v k) ≤ B)
    (hAnchor : ∀ᶠ k : ℕ in atTop,
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ≤ ((v k : ℝ) + 1) ^ 2) :
    ∀ᶠ k : ℕ in atTop,
      ¬ h3CriticalMinimalShellRiccatiWindowAt u t δ v k := by
  have hForced := h3Critical_minimalShell_boundedCubicCharges_force_lateRiccatiAnchors
    u t δ v hc hLocal B hB
  filter_upwards [hForced, hAnchor] with k hk hSmall
  intro hRic
  exact (not_lt_of_ge hSmall) (hk hRic)

/-- Transfer the >2 cubic-cost obligation onto the very same cofinal,
strictly disjoint minimal-shell witnesses with their original source-horizon
and signed-gap alternative. Bounded cubic charges then force all late Riccati
peaks to have quadratic physical H3 energy at the anchor, and exclude them
altogether under an eventual subquadratic anchor bound. -/
theorem h3Critical_noL2Trace_minimalShell_riccatiCubicChargeRigidity
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
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      h3CriticalMinimalShellEveryTailSignedAccounting u t δ v k₁ ∧
      ((∀ M : ℝ, ∃ q : ℕ,
          M < ∑ k ∈ Finset.range q,
            h3CriticalMinimalShellCubicWindowCost δ v k) ∨
        (∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
          ∀ᶠ k : ℕ in atTop,
            h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
              h3CriticalMinimalShellRiccatiCarrierOrSourceHorizonAt
                hH3 t N m v k D L)) ∧
      (∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiAnchorOrCubicChargeAt
            u t δ v k) ∧
      ((∃ B : ℝ, ∀ q : ℕ,
          (∑ k ∈ Finset.range q,
            h3CriticalMinimalShellCubicWindowCost δ v k) ≤ B) →
        ∀ᶠ k : ℕ in atTop,
          h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
            ((v k : ℝ) + 1) ^ 2 <
              4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
                velocityH3EnergyAt u (t (v k))) ∧
      ((∃ B : ℝ, ∀ q : ℕ,
          (∑ k ∈ Finset.range q,
            h3CriticalMinimalShellCubicWindowCost δ v k) ≤ B) →
        (∀ᶠ k : ℕ in atTop,
          4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
            velocityH3EnergyAt u (t (v k)) ≤ ((v k : ℝ) + 1) ^ 2) →
        ∀ᶠ k : ℕ in atTop,
          ¬ h3CriticalMinimalShellRiccatiWindowAt u t δ v k) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁,
      hv, hLimit, hSeparate, hWindows, hRates, hShell, hAccounting,
      hAlt⟩ :=
    h3Critical_noL2Trace_minimalShell_carrierOrSourceHorizonClock
      hH3 hClass hNoTrace
  have hTailTime : ∀ᶠ k : ℕ in atTop, a < t (v k) := by
    have hOpen : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact hLimit.eventually hOpen
  have hLocal : ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        h3CriticalMinimalShellRiccatiAnchorOrCubicChargeAt u t δ v k := by
    filter_upwards [hTailTime] with k hStart
    intro hRic
    have hW := hWindows k
    have ht : t (v k) ∈ Set.Ioo a T := by
      rcases hW with ⟨_, _, _, _, hδ, hEnd, _⟩
      exact ⟨hStart, by linarith only [hδ, hEnd]⟩
    exact h3Critical_minimalShellRiccatiWindow_anchorOrFixedCubicCharge
      hH3 hClass t δ v N m C k ht (hWindows k) hRic
  have hc (k : ℕ) :
      0 ≤ h3CriticalMinimalShellCubicWindowCost δ v k := by
    have hW := hWindows k
    rcases hW with ⟨_, _, _, _, hδ, _⟩
    dsimp only [h3CriticalMinimalShellCubicWindowCost]
    positivity
  refine ⟨t, N, m, C, δ, v, j, k₁,
    hv, hLimit, hSeparate, hWindows, hRates, hShell, hAccounting,
    hAlt, hLocal, ?_, ?_⟩
  · rintro ⟨B, hB⟩
    exact h3Critical_minimalShell_boundedCubicCharges_force_lateRiccatiAnchors
      u t δ v hc hLocal B hB
  · rintro ⟨B, hB⟩ hAnchor
    exact h3Critical_minimalShell_boundedCubicCharges_smallAnchor_excludes_lateRiccati
      u t δ v hc hLocal B hB hAnchor

end
end PrimeTensor.Bridge.Euclidean
