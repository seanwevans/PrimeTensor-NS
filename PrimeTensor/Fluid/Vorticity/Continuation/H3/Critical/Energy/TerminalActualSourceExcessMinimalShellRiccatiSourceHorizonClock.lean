import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiCarrierPDEExcursion
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceH3EnergyEscape244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Lower.Bound
import Mathlib.Tactic

/-!
# Short physical terminal horizons constrain actual projected source peaks

The already verified inverse-square-root H³ Riccati shift supplies a
quantitative no-fourfold-growth estimate on a sufficiently short physical
time interval. Combined with the exact physical projected-source/H³ majorant,
this gives a terminal-clock obstruction to source peaks on the canonical
half-terminal interval. We apply it to the SAME minimal first-crossing kinetic
carrier/source-peak alternative as the previous committed module.

There is no source-time Lipschitz assumption, terminal H³ integrability,
uniform fractional last-shell overshoot, or new selection of physical shells.
The no-terminal-L²-trace output still has a separate cubic-charge branch.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalSourceHorizon
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalSourceHorizon :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- An inverse-square-root Riccati comparison rules out a fourfold energy
increase if the elapsed time is at most one inverse-root Riccati unit.
The strict comparison is crucial at the exact fourfold threshold. -/
theorem h3Critical_scalar_inverseRoot_shortHorizon_fourfoldEnergyCeiling
    (K E₀ E₁ d : ℝ) (_hK : 0 ≤ K)
    (hE₀ : 0 < E₀) (hE₁ : 0 < E₁)
    (hInverse : (Real.sqrt E₀)⁻¹ ≤
      (Real.sqrt E₁)⁻¹ + (K / 2) * d)
    (hShort : K * d * Real.sqrt E₀ ≤ 1) :
    E₁ ≤ 4 * E₀ := by
  by_contra hNot
  have hFourfold : 4 * E₀ < E₁ := lt_of_not_ge hNot
  let S : ℝ := Real.sqrt E₀
  let Q : ℝ := Real.sqrt E₁
  have hSPos : 0 < S := Real.sqrt_pos.2 hE₀
  have hQPos : 0 < Q := Real.sqrt_pos.2 hE₁
  have hSSq : S ^ 2 = E₀ := Real.sq_sqrt hE₀.le
  have hQSq : Q ^ 2 = E₁ := Real.sq_sqrt hE₁.le
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
  have hShort' : K * d * S ≤ 1 := by
    simpa only [S] using hShort
  exact (not_lt_of_ge hShort') hTime

/-- If the actual normalized H³ energy at an original anchor is too small
for a Riccati fourfold jump on the remaining half-terminal interval, then
EVERY time in that interval has at most four times the anchor energy.
No bound on the physical projected source derivative is assumed. -/
theorem h3Critical_minimalShell_halfTerminal_inverseRoot_energyCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s : ℝ) (ht : t ∈ Set.Ioo a T)
    (hs : s ∈ Set.Icc t (t + (T - t) / 2))
    (hShort : h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
      Real.sqrt (velocityH3EnergyAt u t) ≤ 2) :
    velocityH3EnergyAt u s ≤ 4 * velocityH3EnergyAt u t := by
  let K : ℝ := h3PathSqrtEnergyRiccatiCoefficient
  let E₀ : ℝ := velocityH3EnergyAt u t
  let E₁ : ℝ := velocityH3EnergyAt u s
  have hK : 0 ≤ K := h3PathSqrtEnergyRiccatiCoefficient_nonneg
  have hE₀ : 0 < E₀ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u t)
  have hE₁ : 0 < E₁ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  have hHalfEnd : t + (T - t) / 2 < T := by
    linarith only [ht.2]
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hHalfEnd⟩
  have hMono := monotoneOn_h3PathInverseSqrtEnergyRiccatiShift
    hH3 hClass ht hsClass hs.1
  have hInverse : (Real.sqrt E₀)⁻¹ ≤
      (Real.sqrt E₁)⁻¹ + (K / 2) * (s - t) := by
    change (Real.sqrt E₀)⁻¹ + (K / 2) * t ≤
      (Real.sqrt E₁)⁻¹ + (K / 2) * s at hMono
    linarith only [hMono]
  have hHalf : s - t ≤ (T - t) / 2 := by
    linarith only [hs.2]
  have hKS : 0 ≤ K * Real.sqrt E₀ :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  have hScaled := mul_le_mul_of_nonneg_left hHalf hKS
  have hShort' : K * (T - t) * Real.sqrt E₀ ≤ 2 := by
    simpa only [K, E₀] using hShort
  have hClock : K * (s - t) * Real.sqrt E₀ ≤ 1 := by
    nlinarith only [hScaled, hShort']
  have hEnergy := h3Critical_scalar_inverseRoot_shortHorizon_fourfoldEnergyCeiling
    K E₀ E₁ (s - t) hK hE₀ hE₁ hInverse hClock
  simpa only [E₀, E₁] using hEnergy

/-- An actual physical projected-source observation on the original
half-terminal interval either costs H³ energy already at the anchor, or
forces the dimensionless inverse-root Riccati terminal clock beyond two.
This controls a temporal source PEAK without assuming a source-time modulus. -/
theorem h3Critical_minimalShell_halfTerminal_sourcePeak_forces_anchorOrFastClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s L : ℝ) (ht : t ∈ Set.Ioo a T)
    (hs : s ∈ Set.Icc t (t + (T - t) / 2))
    (hSource : L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖) :
    L < 4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
      velocityH3EnergyAt u t ∨
    2 < h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
      Real.sqrt (velocityH3EnergyAt u t) := by
  by_cases hFast : 2 < h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
      Real.sqrt (velocityH3EnergyAt u t)
  · exact Or.inr hFast
  · left
    have hShort : h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
        Real.sqrt (velocityH3EnergyAt u t) ≤ 2 := le_of_not_gt hFast
    have hE := h3Critical_minimalShell_halfTerminal_inverseRoot_energyCeiling
      hH3 hClass t s ht hs hShort
    have hHalfEnd : t + (T - t) / 2 < T := by
      linarith only [ht.2]
    have hs0 : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_of_lt_of_le ht.1 hs.1),
        lt_of_le_of_lt hs.2 hHalfEnd⟩
    have hP := h3Path_physicalProjectedSource_norm_le_H3Energy244
      hH3 s hs0
    have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
      have hCL := h3AuditInitialLerayEnergyCoefficient_nonneg
      linarith only [hCL]
    have hScaled := mul_le_mul_of_nonneg_left hE hCoeff
    have hUpper : ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
        4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
          velocityH3EnergyAt u t := by
      calc
        _ ≤ (3 + h3AuditInitialLerayEnergyCoefficient) *
          velocityH3EnergyAt u s := hP
        _ ≤ (3 + h3AuditInitialLerayEnergyCoefficient) *
          (4 * velocityH3EnergyAt u t) := hScaled
        _ = 4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
          velocityH3EnergyAt u t := by ring
    exact lt_of_lt_of_le hSource hUpper

/-- The intrinsic (attained) projected physical source envelope itself is
controlled by four times the original H³ anchor majorant whenever the
remaining terminal interval satisfies the short inverse-root clock. -/
theorem h3Critical_minimalShell_shortHorizon_canonicalSourceEnvelopeCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (hShort : h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
      Real.sqrt (velocityH3EnergyAt u t) ≤ 2) :
    h3PathActualProjectedSourceWindowEnvelope244 hH3
        t (t + (T - t) / 2) ≤
      4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
        velocityH3EnergyAt u t := by
  have ht0 : 0 < t := lt_trans hClass.terminal_start.1 ht.1
  have hMid : t < t + (T - t) / 2 := by
    linarith only [ht.2]
  have hHalfEnd : t + (T - t) / 2 < T := by
    linarith only [ht.2]
  obtain ⟨s, hs, _hMax, hAttained⟩ :=
    h3Path_actualSourceWindowEnvelope_attained244
      hH3 ht0 hMid hHalfEnd
  by_contra hNot
  have hLarge : 4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
      velocityH3EnergyAt u t <
      h3PathActualProjectedSourceWindowEnvelope244 hH3
        t (t + (T - t) / 2) := lt_of_not_ge hNot
  rw [hAttained] at hLarge
  obtain hAnchor | hFast :=
    h3Critical_minimalShell_halfTerminal_sourcePeak_forces_anchorOrFastClock
      hH3 hClass t s
      (4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
        velocityH3EnergyAt u t) ht hs hLarge
  · exact (lt_irrefl _) hAnchor
  · exact (not_lt_of_ge hShort) hFast

/-- The fast-horizon branch forces a *quantitative* inverse-square terminal
H³ anchor-energy concentration. No existence of a terminal H³ trace is
assumed or concluded. -/
theorem h3Critical_scalar_fastInverseRootClock_forces_terminalEnergyRate
    (K d E : ℝ) (hK : 0 ≤ K) (hd : 0 ≤ d) (hE : 0 ≤ E)
    (hFast : 2 < K * d * Real.sqrt E) :
    4 < K ^ 2 * d ^ 2 * E := by
  have hTerm : 0 ≤ K * d * Real.sqrt E := by
    exact mul_nonneg (mul_nonneg hK hd) (Real.sqrt_nonneg _)
  have hSquare : (2 : ℝ) ^ 2 < (K * d * Real.sqrt E) ^ 2 :=
    (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 2) hTerm).2 hFast
  have hRoot : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  calc
    (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    _ < (K * d * Real.sqrt E) ^ 2 := hSquare
    _ = K ^ 2 * d ^ 2 * (Real.sqrt E) ^ 2 := by ring
    _ = K ^ 2 * d ^ 2 * E := by rw [hRoot]

/-- The physical version of the short-horizon obstruction records the
inverse-square terminal energy rate directly, rather than leaving the
Riccati-clock product to be expanded by later proofs. -/
theorem h3Critical_minimalShell_halfTerminal_sourcePeak_forces_anchorOrTerminalRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t s L : ℝ) (ht : t ∈ Set.Ioo a T)
    (hs : s ∈ Set.Icc t (t + (T - t) / 2))
    (hSource : L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖) :
    L < 4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
      velocityH3EnergyAt u t ∨
    4 < h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (T - t) ^ 2 * velocityH3EnergyAt u t := by
  rcases h3Critical_minimalShell_halfTerminal_sourcePeak_forces_anchorOrFastClock
      hH3 hClass t s L ht hs hSource with hAnchor | hFast
  · exact Or.inl hAnchor
  · right
    exact h3Critical_scalar_fastInverseRootClock_forces_terminalEnergyRate
      h3PathSqrtEnergyRiccatiCoefficient (T - t)
      (velocityH3EnergyAt u t)
      h3PathSqrtEnergyRiccatiCoefficient_nonneg
      (sub_nonneg.mpr ht.2.le)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_velocityH3EnergyAt u t)) hFast

/-- The pressure branch's actual occupied carrier or attained source peak
can now be paid by a physical H³ anchor or an explicitly long inverse-root
Riccati clock. The source excursion is NOT silently assumed Lipschitz. -/
def h3CriticalMinimalShellRiccatiCarrierOrSourceHorizonAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℕ → ℝ) (N m : ℕ → ℕ) (v : ℕ → ℕ)
    (k : ℕ) (D L : ℝ) : Prop :=
  ((v k : ℝ) + 1) ^ 2 <
    4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
      velocityH3EnergyAt u (t (v k)) ∨
  (D * ((v k : ℝ) + 1) < (m (v k) : ℝ) + 2 ∧
    0 < h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k)) ∧
    0 < h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k)) ∧
    h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k)) /
      (4 * (((N (v k) : ℝ) + 2) ^ 8)) ≤
    h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k))) ∨
  L < 4 * (3 + h3AuditInitialLerayEnergyCoefficient) *
    velocityH3EnergyAt u (t (v k)) ∨
  4 < h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
    (T - t (v k)) ^ 2 * velocityH3EnergyAt u (t (v k))

/-- The existing SAME-carrier and physical-source witness alternative
sharpens to an explicit source/energy terminal-clock alternative, at each
prescribed pair of outer-frequency and source thresholds. -/
theorem h3Critical_minimalShell_actualCarrierSource_refine_sourceHorizonClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ) (N m : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hWindows : ∀ k : ℕ,
      h3CriticalMinimalShellEnergyWindow hH3
        (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k)))
    (hTime : ∀ᶠ k : ℕ in atTop, t (v k) ∈ Set.Ioo a T)
    (hActual : ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          (((v k : ℝ) + 1) ^ 2 <
            4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
              velocityH3EnergyAt u (t (v k))) ∨
          ((D * ((v k : ℝ) + 1) < (m (v k) : ℝ) + 2) ∧
            0 < h3PathActualBandRawKineticMass244
              ((m (v k) : ℝ) + 1) ((m (v k) : ℝ) + 2)
              (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∨
          (∃ s : ℝ,
            s ∈ Set.Icc (t (v k))
              (t (v k) + (T - t (v k)) / 2) ∧
            L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖)) :
    ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiCarrierOrSourceHorizonAt
            hH3 t N m v k D L := by
  intro D L hD hL
  have hAt := hActual D L hD hL
  filter_upwards [hAt, hTime] with k hk ht
  intro hRic
  rcases hk hRic with hEnergy | hCarrier | hSource
  · exact Or.inl hEnergy
  · right
    left
    have hMass := h3Critical_minimalShell_lastCarrier_pays_exactOvershootMass
      hH3 (t (v k)) (v k) (N (v k)) (m (v k))
      (C (v k)) (δ (v k)) (hWindows k)
    exact ⟨hCarrier.1, hMass.1, hMass.2.1, hMass.2.2⟩
  · right
    right
    obtain ⟨s, hs, hPeak⟩ := hSource
    exact h3Critical_minimalShell_halfTerminal_sourcePeak_forces_anchorOrTerminalRate
      hH3 hClass (t (v k)) s L ht hs hPeak

/-- No-physical-L²-trace minimal-shell selectors: either the original
certified cubic window charges diverge, or every late Riccati-heavy
window has quadratic anchor energy, a genuinely occupied overshoot-charged
high Fourier shell, a large physical anchor H³ energy relative to the
source threshold, or a fast terminal inverse-root clock. -/
theorem h3Critical_noL2Trace_minimalShell_carrierOrSourceHorizonClock
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
                hH3 t N m v k D L)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁,
      hv, hLimit, hSeparate, hWindows, hRates, hShell, hAccounting,
      hAlt⟩ :=
    h3Critical_noL2Trace_minimalShell_actualCarrierOrPhysicalSourcePeak
      hH3 hClass hNoTrace
  have hTailTime : ∀ᶠ k : ℕ in atTop, a < t (v k) := by
    have hOpen : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact hLimit.eventually hOpen
  have hTime : ∀ᶠ k : ℕ in atTop,
      t (v k) ∈ Set.Ioo a T := by
    filter_upwards [hTailTime] with k hStart
    have hW := hWindows k
    rcases hW with ⟨_, _, _, _, hδ, hEnd, _⟩
    exact ⟨hStart, by linarith only [hδ, hEnd]⟩
  refine ⟨t, N, m, C, δ, v, j, k₁,
    hv, hLimit, hSeparate, hWindows, hRates, hShell, hAccounting, ?_⟩
  rcases hAlt with hDivergent | hActual
  · exact Or.inl hDivergent
  · exact Or.inr
      (h3Critical_minimalShell_actualCarrierSource_refine_sourceHorizonClock
        hH3 hClass t N m C δ v hWindows hTime hActual)

end
end PrimeTensor.Bridge.Euclidean
