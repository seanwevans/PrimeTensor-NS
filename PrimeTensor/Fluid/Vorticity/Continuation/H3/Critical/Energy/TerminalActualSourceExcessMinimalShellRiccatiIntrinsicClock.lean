import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiIntraWindowTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Lower.Bound
import Mathlib.Tactic

/-!
# Minimal-shell Riccati peaks have an intrinsic physical duration

The inverse-square-root energy Riccati shift is already monotone on every
strict physical H3 energy-class interval. A minimal-shell Riccati peak
satisfies R^2 < B E(s), B=4 K^2+1. If the original anchor satisfies
4 B E(t) <= R^2, then E(s)>4 E(t). Such a fourfold increase must take
more than 4/R units of physical time, independently of any source-time
Lipschitz assumption. The actual quadratic-sharp physical PDE selector
additionally satisfies delta <= (T-t)/4, yielding (T-t) R>16.

These are consequences for each actual peak. Recurrence still needs the
explicit divergent cubic charge and bounded positive gap transport
hypotheses of the accepted every-tail theorem. No terminal H3 budget.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalIntrinsicClock
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalIntrinsicClock :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A quadratic peak produced from a small anchor cannot fit within an
arbitrarily short interval under the exact inverse-root Riccati clock.
The coefficient B>=4K^2 eliminates any division by K. -/
theorem h3Critical_scalar_inverseRootPeak_anchorOrLinearClock
    (R K B E0 E1 d : ℝ)
    (hR : 0 < R) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hBK : 4 * K ^ 2 ≤ B)
    (hE0 : 0 < E0) (hE1 : 0 < E1) (hd : 0 ≤ d)
    (hPeak : R ^ 2 < B * E1)
    (hInverse : (Real.sqrt E0)⁻¹ ≤
      (Real.sqrt E1)⁻¹ + (K / 2) * d) :
    R ^ 2 < 4 * B * E0 ∨ 4 < d * R := by
  by_cases hAnchor : R ^ 2 < 4 * B * E0
  · exact Or.inl hAnchor
  · right
    have hAnchorLe : 4 * B * E0 ≤ R ^ 2 := le_of_not_gt hAnchor
    have hBPos : 0 < B :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hB
    have hScaled : B * (4 * E0) < B * E1 := by
      calc
        B * (4 * E0) = 4 * B * E0 := by ring
        _ ≤ R ^ 2 := hAnchorLe
        _ < B * E1 := hPeak
    have hFourfold : 4 * E0 < E1 := by
      by_contra hn
      have hLe : E1 ≤ 4 * E0 := le_of_not_gt hn
      have hMul := mul_le_mul_of_nonneg_left hLe hBPos.le
      exact (not_lt_of_ge hMul) hScaled
    let S : ℝ := Real.sqrt E0
    let Q : ℝ := Real.sqrt E1
    have hSPos : 0 < S := Real.sqrt_pos.2 hE0
    have hQPos : 0 < Q := Real.sqrt_pos.2 hE1
    have hSSq : S ^ 2 = E0 := Real.sq_sqrt hE0.le
    have hQSq : Q ^ 2 = E1 := Real.sq_sqrt hE1.le
    have hSquare : (2 * S) ^ 2 < Q ^ 2 := by
      nlinarith only [hFourfold, hSSq, hQSq]
    have hDouble : 2 * S < Q :=
      (sq_lt_sq₀ (by positivity : 0 ≤ 2 * S) hQPos.le).1 hSquare
    have hInverseCompare : 2 * Q⁻¹ < S⁻¹ := by
      have hDiv : (2 : ℝ) / Q < 1 / S :=
        (div_lt_div_iff₀ hQPos hSPos).2 (by nlinarith only [hDouble])
      simpa only [div_eq_mul_inv, one_mul] using hDiv
    have hInverse' : S⁻¹ ≤ Q⁻¹ + (K / 2) * d := by
      simpa only [S, Q] using hInverse
    have hGap : S⁻¹ < K * d := by
      linarith only [hInverse', hInverseCompare]
    have hOne : S⁻¹ * S = 1 := inv_mul_cancel₀ (ne_of_gt hSPos)
    have hTime : 1 < K * d * S := by
      calc
        (1 : ℝ) = S⁻¹ * S := hOne.symm
        _ < (K * d) * S := mul_lt_mul_of_pos_right hGap hSPos
    have hKScaled : (4 * K ^ 2) * E0 ≤ B * E0 :=
      mul_le_mul_of_nonneg_right hBK hE0.le
    have hSmallSquare : (4 * K * S) ^ 2 ≤ R ^ 2 := by
      calc
        (4 * K * S) ^ 2 = 4 * ((4 * K ^ 2) * E0) := by
          rw [← hSSq]
          ring
        _ ≤ 4 * (B * E0) :=
          mul_le_mul_of_nonneg_left hKScaled (by norm_num)
        _ = 4 * B * E0 := by ring
        _ ≤ R ^ 2 := hAnchorLe
    have hSmall : 4 * K * S ≤ R :=
      (sq_le_sq₀ (by positivity : 0 ≤ 4 * K * S) hR.le).mp hSmallSquare
    calc
      (4 : ℝ) = 4 * 1 := by ring
      _ < 4 * (K * d * S) :=
        mul_lt_mul_of_pos_left hTime (by norm_num)
      _ = d * (4 * K * S) := by ring
      _ ≤ d * R := mul_le_mul_of_nonneg_left hSmall hd

/-- The literal quadratic-sharp PDE width has a half-budget cap, without
any positivity or derivative premise on the other three selector inputs. -/
theorem h3Critical_scalar_quadraticSharpWidth_le_halfBudget
    (b gap Λ Ξ δ : ℝ)
    (hExact : δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b gap Λ Ξ) :
    δ ≤ b / 2 := by
  rw [hExact]
  exact min_le_left _ _

/-- The same physical minimal first-crossing PDE window either starts
with quadratic H3 energy or must have a linear inner-frequency clock.
The exact PDE selector upgrades the latter to an inverse-terminal-time
frequency obstruction, with NO global transport/dissipation assumption. -/
theorem h3Critical_minimalShellQuadraticPeak_anchorOrTerminalClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (N m : ℕ → ℕ) (C : ℕ → ℝ)
    (k : ℕ)
    (ht : t (v k) ∈ Set.Ioo a T)
    (hWindow : h3CriticalMinimalShellEnergyWindow hH3
      (t (v k)) (v k) (N (v k)) (m (v k)) (C (v k)) (δ (v k)))
    (hQuadratic : h3CriticalMinimalShellQuadraticEnergyWindowAt u t δ v k) :
    ((v k : ℝ) + 1) ^ 2 <
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ∨
    16 < (T - t (v k)) * ((v k : ℝ) + 1) := by
  obtain ⟨s, hs, hPeak⟩ := hQuadratic
  let R : ℝ := (v k : ℝ) + 1
  let K : ℝ := h3PathSqrtEnergyRiccatiCoefficient
  let B : ℝ := 4 * K ^ 2 + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hK : 0 ≤ K := h3PathSqrtEnergyRiccatiCoefficient_nonneg
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    nlinarith only [sq_nonneg K]
  have hBK : 4 * K ^ 2 ≤ B := by dsimp only [B]; linarith
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
  have hAlt := h3Critical_scalar_inverseRootPeak_anchorOrLinearClock
    R K B (velocityH3EnergyAt u (t (v k)))
    (velocityH3EnergyAt u s) (s - t (v k))
    hR hK hB1 hBK hE0 hE1 (sub_nonneg.mpr hs.1) hPeak' hInverse
  rcases hAlt with hAnchor | hDuration
  · exact Or.inl (by simpa only [R, B, K] using hAnchor)
  · right
    have hSpan : s - t (v k) ≤ δ (v k) := by
      linarith only [hs.2]
    have hDelta : 4 < δ (v k) * R :=
      lt_of_lt_of_le hDuration (mul_le_mul_of_nonneg_right hSpan hR.le)
    have hExact : δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - t (v k)) / 2)
        ((h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) -
          ((v k : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) := by
      rcases hWindow with ⟨_, _, _, _, _, _, hexact, _⟩
      exact hexact
    have hCapRaw := h3Critical_scalar_quadraticSharpWidth_le_halfBudget
      _ _ _ _ _ hExact
    have hCap : δ (v k) ≤ (T - t (v k)) / 4 := by
      linarith only [hCapRaw]
    have hScaled := mul_le_mul_of_nonneg_right hCap hR.le
    dsimp only [R] at hDelta hScaled
    nlinarith only [hDelta, hScaled]

/-- A Riccati-heavy actual physical window yields this anchor/clock
alternative at its ORIGINAL inner frequency and anchor time. -/
def h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (t : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ) : Prop :=
  ((v k : ℝ) + 1) ^ 2 <
    4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
      velocityH3EnergyAt u (t (v k)) ∨
  16 < (T - t (v k)) * ((v k : ℝ) + 1)

/-- The established disjoint minimal-shell selector carries an EVENTUAL
pointwise Riccati => anchor/clock implication. Under the TWO explicit
charge/gap hypotheses that force recurring Riccati windows, these same
physical witnesses pay the anchor-or-inverse-terminal-time price cofinally.
No selector, Fourier shell, PDE clock or terminal integrability is changed. -/
theorem h3Critical_noL2Trace_minimalShell_cofinalRiccatiAnchorOrTerminalClock
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
      (∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k) ∧
      (h3CriticalMinimalShellEveryTailCubicChargeUnbounded δ v k₁ →
        h3CriticalMinimalShellEveryTailGapBudget u t δ v k₁ →
        ∀ b : ℕ, ∃ i : ℕ, b ≤ i ∧
          h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt
            u T t v (i + k₁)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
      hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
      hRecurring⟩ :=
    h3Critical_noL2Trace_minimalShell_everyTailSignedRiccatiOrGap
      hH3 hClass hNoTrace
  have hTailTime : ∀ᶠ k : ℕ in atTop, a < t (v k) := by
    have hOpen : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact hLimit.eventually hOpen
  have hLocal : ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k := by
    filter_upwards [hTailTime] with k hStart
    intro hRic
    have hData := hWindow k
    have ht : t (v k) ∈ Set.Ioo a T := by
      rcases hData with ⟨_, _, _, _, hδ, hEnd, _⟩
      exact ⟨hStart, by linarith only [hδ, hEnd]⟩
    have hQuadratic :=
      h3Critical_minimalShellRiccatiWindow_forces_quadraticEnergy
        u t δ v k hRic
    exact h3Critical_minimalShellQuadraticPeak_anchorOrTerminalClock
      hH3 hClass t δ v N m C k ht (hWindow k) hQuadratic
  obtain ⟨k₂, hk₂⟩ := Filter.eventually_atTop.1 hLocal
  refine ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
    hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
    hLocal, ?_⟩
  intro hCharge hBudget b
  obtain ⟨i, hi, hRic⟩ := hRecurring hCharge hBudget (max b k₂)
  have hLower : b ≤ i := le_trans (le_max_left _ _) hi
  have hLate : k₂ ≤ i + k₁ := by omega
  exact ⟨i, hLower, hk₂ (i + k₁) hLate hRic⟩

end
end PrimeTensor.Bridge.Euclidean
