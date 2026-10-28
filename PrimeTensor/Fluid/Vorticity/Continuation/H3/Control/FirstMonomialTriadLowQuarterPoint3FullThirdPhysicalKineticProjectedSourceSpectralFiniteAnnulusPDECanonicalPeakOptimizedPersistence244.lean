import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakOptimizedEighthPower244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakDisjointPersistence244
import Mathlib.Tactic

/-!
# Optimized superquadratic dissipation heights persist on disjoint actual peak windows

The existing unit-increment spectral continuity supplies a positive right
interval at each strict physical spectral peak s. At amplitudes
A = ‖U₃(s)‖ >= 2 and A² >= 32 (E₀(b)+1), optimize the Fourier cutoff for
A/2, not for the instantaneous amplitude at another time. This yields one
fixed frequency ρ for the whole local window, and a positive floor

  H = (ρ² / 8) A² <= D₃(r)       (s <= r <= s+δ),
  A^8 = 16384 (E₀(b)+1) H³,
  A²/8 <= H.

Hence H grows at least quadratically with the peak amplitude, and has the
exact eighth-power/cubic normalization. Select disjoint right-hand windows
from a cofinal sequence of the SAME original source peaks, and charge their
heights to finite time-integrated physical H³ dissipation:

  Summable (fun k => δ_k H_k),   δ_k H_k -> 0.

No quantitative *lower bound* for δ_k or divergent total cost is proved.
Thus the theorem is compatible with finite terminal H³ dissipation and does
not resolve Navier--Stokes global regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A strict-time spectral peak carries a positive right-hand window whose
FULL physical dissipation is bounded below by an explicitly optimized
height, not merely a fixed-radius Fourier mass. The same radius works
throughout that window. -/
theorem h3Path_strictPeak_optimizedDissipationWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℝ) (hs : s ∈ Set.Ioo b T)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hLarge : 32 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ∃ (δ H : ℝ), 0 < δ ∧ s + δ < T ∧ 0 ≤ H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 ≤ H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      (∀ r : ℝ, r ∈ Set.Icc s (s + δ) →
        H ≤ velocityH3DissipationAt u r) := by
  let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 s‖
  let E : ℝ := velocityH3Energy0At u b
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hHalfLarge : 8 * (E + 1) ≤ (A / 2) ^ 2 := by
    dsimp only [A, E] at hLarge ⊢
    nlinarith only [hLarge]
  obtain ⟨ρ, hρ, hRoot, hThreshold⟩ :=
    h3Path_optimizedSixthRootRadius244 (A / 2) E hE hHalfLarge
  let H : ℝ := (ρ ^ 2 / 8) * A ^ 2
  have hρSq : (1 : ℝ) ≤ ρ ^ 2 := by nlinarith only [hρ]
  have hHNonneg : 0 ≤ H := by dsimp only [H]; positivity
  have hHLower : A ^ 2 / 8 ≤ H := by
    have hMult := mul_le_mul_of_nonneg_right hρSq (sq_nonneg A)
    dsimp only [H]
    nlinarith only [hMult]
  have hRoot' : 32 * (E + 1) * ρ ^ 6 = A ^ 2 := by
    nlinarith only [hRoot]
  have hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3 := by
    calc
      A ^ 8 = A ^ 2 * A ^ 6 := by ring
      _ = (32 * (E + 1) * ρ ^ 6) * A ^ 6 := by rw [← hRoot']
      _ = 16384 * (E + 1) * H ^ 3 := by dsimp only [H]; ring
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hs.1), hs.2⟩
  obtain ⟨δ, hδ, hEnd, hUnit⟩ :=
    h3Path_strictSpectralPeak_unitIncrementWindow244 hH3 s hsAbs
  refine ⟨δ, H, hδ, hEnd, hHNonneg, ?_, ?_, ?_⟩
  · simpa only [A] using hHLower
  · simpa only [A, E] using hIdentity
  · intro r hr
    let P : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 s
    let G : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 r
    have hrClass : r ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
    have hNear : ‖G - P‖ < 1 := hUnit r hr
    have hTriangle : ‖P‖ ≤ ‖G‖ + ‖G - P‖ := by
      calc
        ‖P‖ = ‖G + (P - G)‖ := by congr 1; abel
        _ ≤ ‖G‖ + ‖P - G‖ := norm_add_le _ _
        _ = ‖G‖ + ‖G - P‖ := by rw [norm_sub_rev]
    have hHalf : A / 2 ≤ ‖G‖ := by
      have h2A : 2 ≤ A := hTwo
      have hTriangleA : A ≤ ‖G‖ + ‖G - P‖ := hTriangle
      linarith only [h2A, hTriangleA, hNear]
    have hHalfNonneg : 0 ≤ A / 2 := by
      dsimp only [A]
      positivity
    have hSquare : (A / 2) ^ 2 ≤ ‖G‖ ^ 2 :=
      pow_le_pow_left₀ hHalfNonneg hHalf 2
    have hCost := h3Path_physicalPeak_sixthThreshold_forces_dissipation244
      hH3 hClass b hb r hrClass ρ hρ hE
        (hThreshold.trans hSquare)
    have hScaled := mul_le_mul_of_nonneg_left hSquare
      (by positivity : 0 ≤ ρ ^ 2 / 2)
    calc
      H = (ρ ^ 2 / 2) * (A / 2) ^ 2 := by dsimp only [H]; ring
      _ ≤ (ρ ^ 2 / 2) * ‖G‖ ^ 2 := hScaled
      _ ≤ velocityH3DissipationAt u r := by simpa only [G] using hCost

/-- The eighth-power-normalized heights on a diverging cofinal peak
sequence can be selected on NEW pairwise-disjoint physical time windows.
Finite terminal H³ dissipation forces the optimized height-width charges
to be genuinely summable and hence individually vanishing. -/
theorem h3Path_cofinalPeaks_disjointOptimizedDissipationCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ k, s k ∈ Set.Ioo b T)
    (hCofinal : Tendsto s atTop (𝓝 T))
    (hPeak : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop)
    (hTwo : ∀ k, 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖)
    (hLarge : ∀ k, 32 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2) :
    ∃ (δ H : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => s (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → s (v k) + δ (v k) < s (v l)) ∧
      (∀ k, 0 < δ (v k) ∧ s (v k) + δ (v k) < T) ∧
      (∀ k, 0 ≤ H (v k) ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (s (v k))‖ ^ 2 / 8 ≤ H (v k) ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (s (v k))‖ ^ 8 =
          16384 * (velocityH3Energy0At u b + 1) * (H (v k)) ^ 3) ∧
      (∀ k r, r ∈ Set.Icc (s (v k)) (s (v k) + δ (v k)) →
        H (v k) ≤ velocityH3DissipationAt u r) ∧
      Tendsto (fun k => H (v k)) atTop atTop ∧
      Summable (fun k => δ (v k) * H (v k)) ∧
      Tendsto (fun k => δ (v k) * H (v k)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m, (∑ k ∈ Finset.range m, δ (v k) * H (v k)) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) := by
  have hWindow (k : ℕ) : ∃ δ H : ℝ, 0 < δ ∧ s k + δ < T ∧
      0 ≤ H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 / 8 ≤ H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      (∀ r : ℝ, r ∈ Set.Icc (s k) (s k + δ) →
        H ≤ velocityH3DissipationAt u r) :=
    h3Path_strictPeak_optimizedDissipationWindow244
      hH3 hClass b hb (s k) (hs k) (hTwo k) (hLarge k)
  choose δ H hδ hEnd hHnonneg hHLower hIdentity hFloor using hWindow
  obtain ⟨v, hv, hVcofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      s δ T hCofinal hδ hEnd
  have hPeakV : Tendsto (fun k : ℕ =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s (v k))‖)
      atTop atTop := by
    have hComposed : Tendsto
        ((fun k : ℕ => ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) ∘ v)
          atTop atTop := hPeak.comp hv.tendsto_atTop
    have hEq :
        ((fun k : ℕ => ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) ∘ v) =
        (fun k : ℕ => ‖h3AuditActualSpectralVelocityTotal hH3 (s (v k))‖) := by
      funext k
      rfl
    rw [hEq] at hComposed
    exact hComposed
  have hHEscape : Tendsto (fun k => H (v k)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro M
    have hLate := hPeakV.eventually (eventually_ge_atTop (max (8 * M) 1))
    filter_upwards [hLate] with k hk
    let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 (s (v k))‖
    have hOne : 1 ≤ A := (le_max_right _ _).trans hk
    have hBig : 8 * M ≤ A := (le_max_left _ _).trans hk
    have hSq : A ≤ A ^ 2 := by
      have hMul : 0 ≤ A * (A - 1) :=
        mul_nonneg (by dsimp only [A]; exact norm_nonneg _) (by linarith only [hOne])
      nlinarith only [hMul]
    have hFloor' : A ^ 2 / 8 ≤ H (v k) := (hHLower (v k))
    linarith only [hBig, hSq, hFloor']
  have hStart (k : ℕ) : a ≤ s (v k) :=
    (lt_trans hb.1 (hs (v k)).1).le
  have hWidth (k : ℕ) : 0 ≤ δ (v k) := (hδ (v k)).le
  have hEnds (k : ℕ) : s (v k) + δ (v k) ≤ T := (hEnd (v k)).le
  have hAdjacent (k : ℕ) :
      s (v k) + δ (v k) ≤ s (v (k + 1)) :=
    (hSeparate k (k + 1) (Nat.lt_succ_self k)).le
  have hBudget : ∀ m, (∑ k ∈ Finset.range m, δ (v k) * H (v k)) ≤
      ∫ r in a..T, velocityH3DissipationAt u r :=
    h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      (velocityH3DissipationAt u) a T
      (fun k => s (v k)) (fun k => δ (v k)) (fun k => H (v k))
      hClass.terminal_start.2.le
      (velocityH3DissipationAt_nonneg u)
      hDInt hStart hWidth hEnds hAdjacent
      (fun k r hr => hFloor (v k) r hr)
  have hSummable : Summable (fun k => δ (v k) * H (v k)) :=
    h3Path_nonnegativeBoundedRangeSums_summable244
      (fun k => δ (v k) * H (v k))
      (∫ r in a..T, velocityH3DissipationAt u r)
      (fun k => mul_nonneg (hδ (v k)).le (hHnonneg (v k))) hBudget
  exact ⟨δ, H, v, hv, hVcofinal, hSeparate,
    (fun k => ⟨hδ (v k), hEnd (v k)⟩),
    (fun k => ⟨hHnonneg (v k), hHLower (v k), hIdentity (v k)⟩),
    (fun k r hr => hFloor (v k) r hr),
    hHEscape, hSummable, hSummable.tendsto_atTop_zero, hBudget⟩

/-- A finite-prefix discard makes the actual diverging spectral-peak
sequence satisfy the explicit optimal-radius threshold and remain after
any fixed kinetic anchor. The resulting windows select only from the
original peak times and are disjoint on a further cofinal subsequence. -/
theorem h3Path_eventuallyCofinalPeaks_disjointOptimizedDissipationCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hCofinal : Tendsto s atTop (𝓝 T))
    (hPeak : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop) :
    ∃ (w : ℕ → ℕ) (d H : ℕ → ℝ),
      StrictMono w ∧
      Tendsto (fun k => s (w k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → s (w k) + d k < s (w l)) ∧
      (∀ k, 0 < d k ∧ s (w k) + d k < T) ∧
      (∀ k, 0 ≤ H k ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 2 / 8 ≤ H k ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 8 =
          16384 * (velocityH3Energy0At u b + 1) * (H k) ^ 3) ∧
      (∀ k r, r ∈ Set.Icc (s (w k)) (s (w k) + d k) →
        H k ≤ velocityH3DissipationAt u r) ∧
      Tendsto H atTop atTop ∧
      Summable (fun k => d k * H k) ∧
      Tendsto (fun k => d k * H k) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m, (∑ k ∈ Finset.range m, d k * H k) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) := by
  let B : ℝ := 32 * (velocityH3Energy0At u b + 1)
  have hNormLate : ∀ᶠ k : ℕ in atTop,
      max B 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hPeak.eventually (eventually_ge_atTop (max B 2))
  have hValid : ∀ᶠ k : ℕ in atTop,
      s k ∈ Set.Ioo b T ∧
      2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ∧
      32 * (velocityH3Energy0At u b + 1) ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 := by
    filter_upwards [hs, hNormLate] with k ht hk
    let A : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖
    have hTwo : 2 ≤ A := (le_max_right _ _).trans hk
    have hBound : B ≤ A := (le_max_left _ _).trans hk
    have hSq : A ≤ A ^ 2 := by
      have hMul : 0 ≤ A * (A - 1) :=
        mul_nonneg (by dsimp only [A]; exact norm_nonneg _)
          (by linarith only [hTwo])
      nlinarith only [hMul]
    exact ⟨ht, hTwo, le_trans (by simpa only [B] using hBound) hSq⟩
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hValid
  let σ : ℕ → ℝ := fun k => s (k₀ + k)
  have hShift : Tendsto (fun k : ℕ => k₀ + k) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with k hk
    omega
  have hσ (k : ℕ) : σ k ∈ Set.Ioo b T :=
    (hk₀ (k₀ + k) (by omega)).1
  have hσTwo (k : ℕ) : 2 ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 (σ k)‖ :=
    (hk₀ (k₀ + k) (by omega)).2.1
  have hσLarge (k : ℕ) :
      32 * (velocityH3Energy0At u b + 1) ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 (σ k)‖ ^ 2 :=
    (hk₀ (k₀ + k) (by omega)).2.2
  have hσLimit : Tendsto σ atTop (𝓝 T) := by
    have hComposed : Tendsto (s ∘ (fun k : ℕ => k₀ + k))
        atTop (𝓝 T) := hCofinal.comp hShift
    have hEq : (s ∘ (fun k : ℕ => k₀ + k)) = σ := by
      funext k
      rfl
    rw [hEq] at hComposed
    exact hComposed
  have hσPeak : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (σ k)‖) atTop atTop := by
    have hComposed : Tendsto
        ((fun k : ℕ => ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) ∘
          (fun k : ℕ => k₀ + k)) atTop atTop := hPeak.comp hShift
    have hEq :
        ((fun k : ℕ => ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) ∘
          (fun k : ℕ => k₀ + k)) =
        (fun k : ℕ => ‖h3AuditActualSpectralVelocityTotal hH3 (σ k)‖) := by
      funext k
      rfl
    rw [hEq] at hComposed
    exact hComposed
  obtain ⟨δ, Q, v, hv, hLimit, hSeparate, hPositive, hHeight,
    hFloor, hEscape, hSummable, hZero, hCosts⟩ :=
    h3Path_cofinalPeaks_disjointOptimizedDissipationCost244
      hH3 hClass hDInt b hb σ hσ hσLimit hσPeak hσTwo hσLarge
  let w : ℕ → ℕ := fun k => k₀ + v k
  let d : ℕ → ℝ := fun k => δ (v k)
  let H : ℕ → ℝ := fun k => Q (v k)
  have hw : StrictMono w := by
    intro k l hkl
    dsimp only [w]
    have hlt := hv hkl
    omega
  refine ⟨w, d, H, hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [w, σ] using hLimit
  · intro k l hkl
    simpa only [w, d, σ] using hSeparate k l hkl
  · intro k
    simpa only [w, d, σ] using hPositive k
  · intro k
    simpa only [w, H, σ] using hHeight k
  · intro k r hr
    have hr' : r ∈ Set.Icc (σ (v k)) (σ (v k) + δ (v k)) := by
      simpa only [w, d, σ] using hr
    exact hFloor k r hr'
  · simpa only [H] using hEscape
  · simpa only [d, H] using hSummable
  · simpa only [d, H] using hZero
  · simpa only [d, H] using hCosts

/-- End-to-end transfer to the exact canonical physical projected-source
maximizers. In the existing explicit critical-width regime they admit a
cofinal subsequence of NEW pairwise-disjoint, superquadratically expensive
persistence windows. Finite terminal dissipation forces their optimized
charges to be summable, not divergent. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakOptimizedPersistence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        ∀ b : ℝ, b ∈ Set.Ioo a T →
        ∃ (w : ℕ → ℕ) (d H : ℕ → ℝ),
          StrictMono w ∧
          Tendsto (fun k => s (w k)) atTop (𝓝 T) ∧
          (∀ k l, k < l → s (w k) + d k < s (w l)) ∧
          (∀ k, 0 < d k ∧ s (w k) + d k < T) ∧
          (∀ k, 0 ≤ H k ∧
            ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 2 / 8 ≤ H k ∧
            ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 8 =
              16384 * (velocityH3Energy0At u b + 1) * (H k) ^ 3) ∧
          (∀ k r, r ∈ Set.Icc (s (w k)) (s (w k) + d k) →
            H k ≤ velocityH3DissipationAt u r) ∧
          Tendsto H atTop atTop ∧
          Summable (fun k => d k * H k) ∧
          Tendsto (fun k => d k * H k) atTop (𝓝 (0 : ℝ)) ∧
          (∀ m, (∑ k ∈ Finset.range m, d k * H k) ≤
            ∫ r in a..T, velocityH3DissipationAt u r)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hTerminalMass hNoTrace hDInt
  have hsBefore (k : ℕ) : s k < T := by
    have hτT := (hTime (v k)).2
    have hMid : τ (v k) + (T - τ (v k)) / 2 < T := by
      linarith only [hτT]
    exact lt_of_le_of_lt (hPeak k).1.2 hMid
  have hsTendsto : Tendsto s atTop (𝓝 T) := by
    have hGap : Tendsto (fun k : ℕ => T - τ (v k))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hCofinal :
        Tendsto (fun k : ℕ => T - τ (v k)) atTop (𝓝 (T - T)))
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    have hBound (k : ℕ) : ‖s k - T‖ ≤ T - τ (v k) := by
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hsBefore k).le)]
      linarith only [(hPeak k).1.1]
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun k => norm_nonneg (s k - T)))
      (Filter.Eventually.of_forall hBound) hGap
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η B D hη hB hD hRegime b hb
  have hPeakEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop :=
    (hJoint η B D hη hB hD hRegime).2
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  have hsEventually : ∀ᶠ k : ℕ in atTop,
      s k ∈ Set.Ioo b T := by
    filter_upwards [hLate] with k hk
    exact ⟨lt_of_lt_of_le hk (hPeak k).1.1, hsBefore k⟩
  exact h3Path_eventuallyCofinalPeaks_disjointOptimizedDissipationCost244
    hH3 hClass hDInt b hb s hsEventually hsTendsto hPeakEscape

end
end PrimeTensor.FirstMonomialTriad
