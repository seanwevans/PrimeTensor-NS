import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFirstCrossingShellPigeonhole244
import Mathlib.Tactic

/-!
# Physical width-averaged shell mass and ninth/eighth separation on one witness

The predecessor's annular concentration witness did not export strict-time
membership, so a separate existential shell witness could not legitimately be
identified with it. We reconstruct the original quadratic-sharp selector,
retain the physical strict-time witnesses, and transport the shell pigeonhole
through exactly the same disjoint windows, H³ full-dissipation summability,
and ninth/eighth three-scale barrier.

Neither an upper bound on N-n nor uniform positivity of shell raw L² mass is
inferred. The selected shell is allowed to move through the full annulus.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Cofinal disjoint exact-PDE-clock witnesses with the local physical shell
kinetic cost and three-scale PDE alternative on precisely the same times. -/
theorem h3Path_noL2Trace_finiteDissipation_minimalShellThreeScale244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k m : ℕ, v k ≤ m → m < N (v k) →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
            3 * (((v k : ℝ) + 1) ^ 3) / 4) ∧
      (∀ k m : ℕ, v k ≤ m → m < N (v k) →
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ k : ℕ,
        3 * (((v k : ℝ) + 1) ^ 3) <
          16 * (((N (v k) : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ k : ℕ, ∃ m : ℕ, v k ≤ m ∧ m < N (v k) ∧
        3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          ((N (v k) - v k : ℕ) : ℝ) *
            (h3PathActualLowRadialDissipation244 ((m : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
              h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
        0 < h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ∧
        3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          ((N (v k) - v k : ℕ) : ℝ) *
            (4 * (((m : ℝ) + 3) ^ 8) *
              h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((m : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 6 ≤
          16 * ε * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1) ∨
        ((v k : ℝ) + 1) ^ 9 ≤
          16 * ε ^ 2 *
            (h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_minimalQuadraticSharpClocks_retain_quarterHighTail244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, hp, _, _, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, he, _, _, _, _, _⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  let M : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hBound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤ M := by
    have hFloor (k : ℕ) (r : ℝ)
        (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
        ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
      rcases hAll (v k) with ⟨_, _, _, _, hb, _, hAnnulus, _, _, _⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
          lt_of_le_of_lt hr.2 hb⟩
      exact (hAnnulus r hr).le.trans
        (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
          hH3 hClass r hrClass ((v k : ℝ) + 1)
            ((N (v k) : ℝ) + 1))
    have hSum := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      (fun k => ((v k : ℝ) + 1) ^ 3 / 2)
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt
      (fun k => (hTime (v k)).1.le)
      (fun k => (hδ (v k)).le)
      (fun k => (hEnd (v k)).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
      hFloor
    simpa only [M] using hSum
  have hΛ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C n := by
    unfold h3PathCubicAnnulusActualLinearRate244
    rcases hAll n with ⟨_, hK, hC, _, _, _, _, _, _, _⟩
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) hK hC
  have hΞ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C n := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    exact (hAll (v k)).2.2.2.2.2.1
  let f : ℕ → ℝ := fun k =>
    δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ (v k)).le (by positivity)
  have hSummable : Summable f :=
    h3Path_nonnegativeBoundedRangeSums_summable244 f M hf
      (by simpa only [f] using hBound)
  have hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) := by
    have hTwice := hSummable.tendsto_atTop_zero.const_mul (2 : ℝ)
    have hEq : (fun k : ℕ =>
        δ (v k) * ((v k : ℝ) + 1) ^ 3) =
        (fun k : ℕ => 2 * f k) := by
      funext k
      dsimp only [f]
      ring
    rw [hEq]
    simpa only [mul_zero] using hTwice
  have hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤
        h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    apply Filter.Eventually.of_forall
    intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg, _, _⟩
    exact hg.le
  have hΛEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C (v k) :=
    Filter.Eventually.of_forall (fun k => hΛ (v k))
  have hΞEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C (v k) :=
    Filter.Eventually.of_forall (fun k => hΞ (v k))
  have hBarrier := h3Path_exactQuadraticSharpClocks_threeScaleBarrier244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    hv hExact hCollapse hQuarter hΛEv hΞEv
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime, hSeparate, ?_, ?_, ?_, ?_, ?_, ?_, hBarrier⟩
  · intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg, _, _⟩
    exact hg
  · simpa only [f] using hSummable
  · intro k m hnm hmN
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, _, hMin, _⟩
    exact hMin m hnm hmN
  · intro k m hnm hmN
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, _, _, hTail⟩
    exact hTail m hnm hmN
  · intro k
    rcases hAll (v k) with ⟨hnN, _, _, _, _, _, _, hg, _, _⟩
    have hCross :
        3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
      dsimp only [h3PathCubicAnnulusActualGap244] at hg
      linarith only [hg]
    exact h3Path_firstCrossing_forces_bandKineticMass244
      hH3 hClass (τ (v k)) (hTime (v k))
      (v k) (N (v k)) hnN hCross
  · intro k
    rcases hAll (v k) with ⟨hnN, _, _, _, _, _, _, hGap, hMinimal, _⟩
    have hCross : 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
      dsimp only [h3PathCubicAnnulusActualGap244] at hGap
      linarith only [hGap]
    exact h3Path_physicalFirstCrossing_exists_widthAveragedKineticShell244
      hH3 hClass (τ (v k)) (hTime (v k))
      (v k) (N (v k)) hnN hCross hMinimal



/-- The selected physical shell, last-crossing whole band, retained high tail,
and conditional ninth/eighth separation belong to the SAME disjoint-window
first-crossing sequence. No width ceiling is imposed on the kinetic shell. -/
theorem h3Path_noL2Trace_finiteDissipation_minimalShellNinthEighth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v m : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k m : ℕ, v k ≤ m → m < N (v k) →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
            3 * (((v k : ℝ) + 1) ^ 3) / 4) ∧
      (∀ k m : ℕ, v k ≤ m → m < N (v k) →
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
                    (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ k : ℕ,
        3 * (((v k : ℝ) + 1) ^ 3) <
          16 * (((N (v k) : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244
              ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ k : ℕ, v k ≤ m k ∧ m k < N (v k) ∧
        3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          ((N (v k) - v k : ℕ) : ℝ) *
            (h3PathActualLowRadialDissipation244 ((m k : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
              h3PathActualLowRadialDissipation244 ((m k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
        0 < h3PathActualBandRawKineticMass244 ((m k : ℝ) + 1) ((m k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ∧
        3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          ((N (v k) - v k : ℕ) : ℝ) *
            (4 * (((m k : ℝ) + 3) ^ 8) *
              h3PathActualBandRawKineticMass244 ((m k : ℝ) + 1) ((m k : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))) ∧
      (∀ k : ℕ, ∃ j : ℕ, N (v k) = j + 1 ∧
        0 < h3PathActualBandRawKineticMass244 ((j : ℝ) + 1)
          ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ∧
        (h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) -
          3 * (((v k : ℝ) + 1) ^ 3) / 4 ≤
          4 * (((N (v k) : ℝ) + 2) ^ 8) *
            h3PathActualBandRawKineticMass244 ((j : ℝ) + 1)
              ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η B S M : ℝ, 0 < η → 0 ≤ B → 0 ≤ M →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6 →
            C (v k) ^ 2 ≤ S ^ 2 →
              M * ((v k : ℝ) + 1) ^ 9 <
                (((N (v k) : ℝ) + 1) + 1) ^ 8 ∧
              ∀ m : ℕ, v k ≤ m →
                ((m : ℝ) + 2) ^ 8 ≤ M * ((v k : ℝ) + 1) ^ 9 →
                ((v k : ℝ) + 1) ^ 3 / 4 <
                  h3PathActualHighRadialDissipation244 ((m : ℝ) + 1)
                    (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime, hSeparate,
      hGap, hSummable, hMinimal, hTail, hBand, hShell, hThree⟩ :=
    h3Path_noL2Trace_finiteDissipation_minimalShellThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  classical
  choose m hShellAll using hShell
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let Q : ℕ → ℝ := fun k => ((N (v k) : ℝ) + 1)
  let G : ℕ → ℝ := fun k =>
    ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)
  let L : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualLinearRate244 N K C (v k)
  let X : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualQuadraticRate244 N C (v k)
  let Src : ℕ → ℝ := fun k => C (v k)
  have hR : ∀ k : ℕ, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hCast : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hCast]
  have hQ : ∀ k : ℕ, 0 ≤ Q k := by
    intro k
    dsimp only [Q]
    positivity
  have hThree' : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      G k ≤ ε ∨ R k ^ 6 ≤ 16 * ε * (L k + 1) ∨
        R k ^ 9 ≤ 16 * ε ^ 2 * (X k + 1) := by
    intro ε hε
    simpa only [R, G, L, X] using hThree ε hε
  have hQuadratic : ∀ k : ℕ,
      X k = h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
        (R k) (Q k) (Src k) := by
    intro k
    rfl
  have hEighth (η B D S : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k → L k + 1 ≤ B * R k ^ 6 →
          Src k ^ 2 ≤ S ^ 2 →
            D * R k ^ 9 <
              36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1 :=
    h3Path_minimalQuadraticSharp_threeScale_forces_eighthGain244
      R Q G L X Src hR hQ hThree' hQuadratic η B D S hη hB hD
  have hOuter (η B S M : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hM : 0 ≤ M) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k → L k + 1 ≤ B * R k ^ 6 →
          Src k ^ 2 ≤ S ^ 2 →
            M * R k ^ 9 < (Q k + 1) ^ 8 :=
    h3Path_ninthEighthCutoff_intermit_forces_outerSeparation244
      R Q G L Src hR hEighth η B S M hη hB hM
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime, hSeparate, hGap,
    hSummable, hMinimal, hTail, hBand, hShellAll, ?_, ?_⟩
  · intro k
    have hN : v k ≤ N (v k) :=
      (hShellAll k).1.trans ((hShellAll k).2.1.le)
    have hCross : 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
      have hG := hGap k
      dsimp only [h3PathCubicAnnulusActualGap244] at hG
      linarith only [hG]
    obtain ⟨j, hjN, _, _, hPos, hOver⟩ :=
      h3Path_physicalFirstCrossing_lastShellKineticOvershoot244
        hH3 hClass (τ (v k)) (hTime (v k))
        (v k) (N (v k)) hN hCross (hMinimal k)
    exact ⟨j, hjN, hPos, hOver⟩
  · intro η B S M hη hB hM
    filter_upwards [hOuter η B S M hη hB hM] with k hk
    intro hkGeom hkLinear hkSource
    have hSep : M * R k ^ 9 < (Q k + 1) ^ 8 :=
      hk hkGeom hkLinear hkSource
    constructor
    · simpa only [R, Q] using hSep
    · intro m hvm hmCandidate
      have hSep' : M * R k ^ 9 < (((N (v k) : ℝ) + 1) + 1) ^ 8 := by
        simpa only [Q] using hSep
      have hCandidate : ((m : ℝ) + 2) ^ 8 ≤ M * R k ^ 9 := by
        simpa only [R] using hmCandidate
      have hmN : m < N (v k) :=
        h3Path_eighthSeparation_forces_preFirstCrossing244
          (N (v k)) m (R k) M hCandidate hSep'
      exact hTail k m hvm hmN
end
end PrimeTensor.FirstMonomialTriad
