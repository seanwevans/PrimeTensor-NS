import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessCofinalActiveAnnulusDiagonal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointWindows244
import Mathlib.Tactic

/-!
# Pairwise disjoint cofinal physical H³ cubic annulus persistence intervals

The committed active-annulus diagonal has exact finite-radius projected-PDE
persistence intervals and annular integral costs for all integer frequencies.
The existing terminal-window selection lemma extracts a strictly increasing
subsequence with nonoverlapping CLOSED time intervals. Neither endpoint PDE
clocks nor original cutoff witnesses are replaced or shortened.

The new sequence has growing inner frequencies, cofinal sample times, and a
strictly positive physical annular integral at each separated interval.
No finite terminal H³ dissipation hypothesis or global charge summability
is introduced. Positive individual costs do not imply a divergent sum.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Pairwise separation of the EXACT physical PDE-certified windows.
The original diagonal certificate is preserved at *every* index, and the
selected inner-frequency indices satisfy `k ≤ v k`. -/
theorem h3Critical_noL2Trace_disjointCofinalActiveCubicAnnuli
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ C δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      (∀ n : ℕ, t n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (t n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto t atTop (𝓝 T) ∧
      (∀ n : ℕ,
        n ≤ N n ∧ 0 ≤ C n ∧
        C n = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t n) (t n + (T - t n) / 2) ∧
        0 < δ n ∧ t n + δ n < T ∧
        δ n = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - t n) / 2)
          ((h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t n))) -
            ((n : ℝ) + 1) ^ 3 / 2)
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖ (C n))
          (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)) ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖ ^ 2 ≤
          velocityH3EnergyAt u (t n) ∧
        (∀ r : ℝ, r ∈ Set.Icc (t n) (t n + δ n) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ∧
          h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ≤
            velocityH3DissipationAt u r) ∧
        δ n * (((n : ℝ) + 1) ^ 3 / 2) ≤
          ∫ r in t n..(t n + δ n),
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, k ≤ v k) := by
  obtain ⟨t, N, C, δ, hTime, hDist, hLimit, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalActiveCubicAnnulusDiagonal
      hH3 hClass hNoTrace
  have hPositive (n : ℕ) : 0 < δ n := by
    obtain ⟨_, _, _, hδ, _, _, _, _, _⟩ := hWindows n
    exact hδ
  have hEnd (n : ℕ) : t n + δ n < T := by
    obtain ⟨_, _, _, _, hBefore, _, _, _, _⟩ := hWindows n
    exact hBefore
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      t δ T hLimit hPositive hEnd
  have hIndex (k : ℕ) : k ≤ v k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        exact Nat.succ_le_of_lt
          (lt_of_le_of_lt ih (hMono (Nat.lt_succ_self k)))
  exact ⟨t, N, C, δ, v, hTime, hDist, hLimit, hWindows,
    hMono, hCofinal, hSeparated, hIndex⟩

/-- Every selected interval has a strictly positive real annular integral,
with pairwise separated physical time supports and cofinal inner cutoffs.
This is NOT a claim that the infinite sum of charges diverges. -/
theorem h3Critical_noL2Trace_disjointCofinalActiveCubicAnnuli_positiveIntegrals
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ 0 < δ (v k) ∧
        0 < ∫ r in t (v k)..(t (v k) + δ (v k)),
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r)) := by
  obtain ⟨t, N, C, δ, v, _hTimes, _hDist, _hOriginalLimit,
    hWindows, hMono, hCofinal, hSeparated, hIndex⟩ :=
    h3Critical_noL2Trace_disjointCofinalActiveCubicAnnuli
      hH3 hClass hNoTrace
  refine ⟨t, N, δ, v, hMono, hCofinal, hSeparated, ?_⟩
  intro k
  obtain ⟨_, _, _, hδ, _, _, _, _, hCost⟩ := hWindows (v k)
  have hHeight : 0 < (((v k : ℝ) + 1) ^ 3 / 2) := by positivity
  have hIntegral :
      0 < ∫ r in t (v k)..(t (v k) + δ (v k)),
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) :=
    lt_of_lt_of_le (mul_pos hδ hHeight) hCost
  exact ⟨hIndex k, hδ, hIntegral⟩

end
end PrimeTensor.Bridge.Euclidean
