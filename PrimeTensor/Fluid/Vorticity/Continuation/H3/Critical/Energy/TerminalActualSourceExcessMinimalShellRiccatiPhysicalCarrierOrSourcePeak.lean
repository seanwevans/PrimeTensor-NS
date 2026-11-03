import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiOuterOrSourceEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceWindowEnvelope244
import Mathlib.Tactic

/-!
# Actual physical source peaks or occupied minimal Fourier carrier shells

The preceding all-multiplier theorem distinguishes a quadratic H3 anchor,
escape of the actual minimal outer cutoff, and escape of the canonical
source-window envelope. Neither an arbitrary source ceiling nor a new outer
cutoff is needed: the canonical envelope is the attained norm of the actual
projected momentum source, while the minimal crossing gives N = m+1 and
strictly positive raw velocity Fourier mass in its last integer shell.

We transport the outer-frequency/source-envelope obstruction to these
literal physical witnesses on the SAME selected minimal PDE windows.
The multiplier thresholds retain their proper eventually-for-each ordering.
No terminal H3 dissipation budget, fixed last-shell mass floor, or source
upper bound is postulated.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalPhysicalCarrier
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalPhysicalCarrier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- An escape of the canonical source envelope actually occurs at some
physical time on the original strict half-terminal source interval. -/
theorem h3Critical_minimalShell_canonicalEnvelopeEscape_attains_physicalSource
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℕ → ℝ) (C : ℕ → ℝ) (v : ℕ → ℕ)
    (k : ℕ) (L : ℝ)
    (ht : 0 < t (v k) ∧ t (v k) < T)
    (hEnvelope : C (v k) =
      h3PathActualProjectedSourceWindowEnvelope244 hH3
        (t (v k)) (t (v k) + (T - t (v k)) / 2))
    (hLarge : L < C (v k)) :
    ∃ s : ℝ,
      s ∈ Set.Icc (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
      L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖ := by
  have hMid : t (v k) < t (v k) + (T - t (v k)) / 2 := by
    linarith only [ht.2]
  have hMidEnd : t (v k) + (T - t (v k)) / 2 < T := by
    linarith only [ht.2]
  obtain ⟨s, hs, _hMax, hAttained⟩ :=
    h3Path_actualSourceWindowEnvelope_attained244 hH3
      ht.1 hMid hMidEnd
  refine ⟨s, hs, ?_⟩
  have hPhysical : C (v k) =
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ :=
    hEnvelope.trans hAttained
  rw [hPhysical] at hLarge
  exact hLarge

/-- The outer cutoff of the genuinely MINIMAL first crossing is just one
integer above the carrier's lower shell index. An escaped shifted outer
cutoff forces escape of this occupied last-shell upper frequency itself. -/
theorem h3Critical_scalar_minimalOuterEscape_forces_lastShellCarrier
    (R Q S D : ℝ)
    (hR : 1 ≤ R)
    (hMinimal : Q = S + 1)
    (hFar : (D + 1) * R < Q + 2) :
    D * R < S + 2 := by
  nlinarith only [hR, hMinimal, hFar]

/-- At each sufficiently late Riccati peak, the quadratic anchor cost is
paid, OR a frequency beyond any fixed relative threshold carries strictly
positive ACTUAL last-shell raw kinetic mass, OR the actual projected
physical momentum source exceeds any fixed norm threshold on the original
half-terminal interval. The conclusion preserves the same minimal N,m and
canonical source C; no replacement witnesses are selected. -/
theorem h3Critical_minimalShell_quantifiedPressure_forces_actualCarrierOrSourcePeak
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℕ → ℝ) (N m : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hWindow : ∀ k : ℕ,
      h3CriticalMinimalShellEnergyWindow hH3
        (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k)))
    (hTime : ∀ᶠ k : ℕ in atTop, 0 < t (v k) ∧ t (v k) < T)
    (hPressure : ∀ M : ℝ, 0 ≤ M →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
            u t N C v k M) :
    ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
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
            L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖) := by
  have hCNonneg (k : ℕ) : 0 ≤ C (v k) := by
    rcases hWindow k with ⟨_, _, hC, _⟩
    exact hC
  intro D L hD hL
  have hDPlus : 0 ≤ D + 1 := by linarith only [hD]
  have hThree :=
    h3Critical_minimalShell_quantifiedPressure_forces_anchorOrOuterOrEnvelope
      u t N C δ v hCNonneg hPressure (D + 1) L hDPlus hL
  filter_upwards [hThree, hTime] with k hk ht
  intro hRic
  rcases hk hRic with hAnchor | hFar | hSource
  · exact Or.inl hAnchor
  · right
    left
    rcases hWindow k with ⟨hNm, _, _, _, _, _, _, _, _, _, _, _, _, hMass, _⟩
    have hNmCast : (N (v k) : ℝ) = (m (v k) : ℝ) + 1 := by
      exact_mod_cast hNm
    have hR : 1 ≤ (v k : ℝ) + 1 := by
      have hn : 0 ≤ (v k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hCarrier : D * ((v k : ℝ) + 1) < (m (v k) : ℝ) + 2 :=
      h3Critical_scalar_minimalOuterEscape_forces_lastShellCarrier
        ((v k : ℝ) + 1) (N (v k) : ℝ) (m (v k) : ℝ)
        D hR hNmCast hFar
    have hUpper : (N (v k) : ℝ) + 1 = (m (v k) : ℝ) + 2 := by
      linarith only [hNmCast]
    rw [hUpper] at hMass
    exact ⟨hCarrier, hMass⟩
  · right
    right
    have hEnvelope : C (v k) =
        h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2) := by
      rcases hWindow k with ⟨_, _, _, hEq, _⟩
      exact hEq
    exact h3Critical_minimalShell_canonicalEnvelopeEscape_attains_physicalSource
      hH3 t C v k L ht hEnvelope hSource

/-- On the no-terminal-physical-L2-trace selector, the unbounded actual
cubic-charge arm remains separate. In the other arm, the original positive
last Fourier shell or an observed actual projected momentum source peak
now replaces the abstract outer-radius/envelope escape on every late
Riccati-heavy window. This is conditional on the Riccati window existing;
neither source divergence nor a nonzero last-shell mass floor is asserted. -/
theorem h3Critical_noL2Trace_minimalShell_actualCarrierOrPhysicalSourcePeak
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
                L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖))) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
      hWindows, hRates, _hEnergyWidth, hShell, _hSigned, hAccounting,
      _hLocal, hAlternative⟩ :=
    h3Critical_noL2Trace_minimalShell_outerOrSourceEnvelopeEscape
      hH3 hClass hNoTrace
  have hPositive : ∀ᶠ k : ℕ in atTop, 0 < t (v k) := by
    have hT : 0 < T :=
      lt_trans hClass.terminal_start.1 hClass.terminal_start.2
    have hOpen : Set.Ioi (0 : ℝ) ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hT
    exact hLimit.eventually hOpen
  have hTime : ∀ᶠ k : ℕ in atTop,
      0 < t (v k) ∧ t (v k) < T := by
    filter_upwards [hPositive] with k hk
    have hW := hWindows k
    rcases hW with ⟨_, _, _, _, hδ, hEnd, _⟩
    exact ⟨hk, by linarith only [hδ, hEnd]⟩
  refine ⟨t, N, m, C, δ, v, j, k₁,
    hv, hLimit, hSeparate, hWindows, hRates, hShell, hAccounting, ?_⟩
  rcases hAlternative with hDivergent | ⟨hPressure, _, _⟩
  · exact Or.inl hDivergent
  · exact Or.inr
      (h3Critical_minimalShell_quantifiedPressure_forces_actualCarrierOrSourcePeak
        hH3 t N m C δ v hWindows hTime hPressure)

end
end PrimeTensor.Bridge.Euclidean
