import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointWindows244
import Mathlib.Tactic

/-!
# Disjoint cubic-annulus windows: finite costs versus full physical H³ dissipation

Disjoint PDE-persistent annular windows have genuine positive integrated costs.
The missing summability step is not a claim of divergent costs: a hypothetical
finite L¹ integral of the full physical H³ dissipation bounds every partial sum.

This file proves a generic, exact finite-interval summation lemma by telescoping
nonnegative interval integrals, then transfers actual annular pointwise floors
to the full H³ dissipation via the already-proved radial partition identity.
Finally it applies the lemma to the no-strong-physical-L²-terminal-trace
cubic witnesses. Full terminal dissipation interval integrability is an
EXPLICIT EXTRA HYPOTHESIS, not inferred from preterminal H³ admissibility.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A nonnegative time-density pays for the entire sum of its integrals over
non-overlapping ordered intervals. This is a finite-sum inequality, requiring
only integrability on the encompassing interval, not any infinite summation
or measure-theoretic disjoint-union machinery. -/
theorem h3Path_disjointNonnegativeWindows_finiteIntegralSum_le244
    (f : ℝ → ℝ) (a T : ℝ) (τ δ : ℕ → ℝ)
    (haT : a ≤ T)
    (hf : ∀ r : ℝ, 0 ≤ f r)
    (hInt : IntervalIntegrable f volume a T)
    (hStart : ∀ k : ℕ, a ≤ τ k)
    (hWidth : ∀ k : ℕ, 0 ≤ δ k)
    (hEnd : ∀ k : ℕ, τ k + δ k ≤ T)
    (hSeparate : ∀ k : ℕ, τ k + δ k ≤ τ (k + 1)) :
    ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        ∫ r in τ k..(τ k + δ k), f r) ≤
      ∫ r in a..T, f r := by
  have hTimeT (k : ℕ) : τ k ≤ T :=
    (le_add_of_nonneg_right (hWidth k)).trans (hEnd k)
  have hSubInt (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y)
      (hyT : y ≤ T) : IntervalIntegrable f volume x y := by
    apply hInt.mono_set
    rw [Set.uIcc_of_le hxy, Set.uIcc_of_le haT]
    exact Set.Icc_subset_Icc hax hyT
  have hPosOn (x y : ℝ) :
      0 ≤ᵐ[volume.restrict (Set.Ioc x y)] f :=
    Filter.Eventually.of_forall (fun r => hf r)
  have hPrefix : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        ∫ r in τ k..(τ k + δ k), f r) ≤
      ∫ r in a..τ m, f r := by
    intro m
    induction m with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        exact intervalIntegral.integral_nonneg (hStart 0)
          (fun r _ => hf r)
    | succ m ih =>
        have hWindow : τ m ≤ τ m + δ m :=
          le_add_of_nonneg_right (hWidth m)
        have hJoin :
            (∫ r in a..τ m, f r) +
              (∫ r in τ m..(τ m + δ m), f r) =
                ∫ r in a..(τ m + δ m), f r :=
          intervalIntegral.integral_add_adjacent_intervals
            (hSubInt a (τ m) le_rfl (hStart m) (hTimeT m))
            (hSubInt (τ m) (τ m + δ m)
              (hStart m) hWindow (hEnd m))
        have hGapBound :
            (∫ r in a..(τ m + δ m), f r) ≤
              ∫ r in a..τ (m + 1), f r :=
          intervalIntegral.integral_mono_interval
            le_rfl (le_trans (hStart m) hWindow)
            (hSeparate m) (hPosOn a (τ (m + 1)))
            (hSubInt a (τ (m + 1)) le_rfl
              (hStart (m + 1)) (hTimeT (m + 1)))
        calc
          (∑ k ∈ Finset.range (m + 1),
              ∫ r in τ k..(τ k + δ k), f r) =
              (∑ k ∈ Finset.range m,
                  ∫ r in τ k..(τ k + δ k), f r) +
                (∫ r in τ m..(τ m + δ m), f r) := by
                  rw [Finset.sum_range_succ]
          _ ≤ (∫ r in a..τ m, f r) +
                (∫ r in τ m..(τ m + δ m), f r) :=
            add_le_add ih le_rfl
          _ = ∫ r in a..(τ m + δ m), f r := hJoin
          _ ≤ ∫ r in a..τ (m + 1), f r := hGapBound
  intro m
  calc
    (∑ k ∈ Finset.range m,
        ∫ r in τ k..(τ k + δ k), f r) ≤
      ∫ r in a..τ m, f r := hPrefix m
    _ ≤ ∫ r in a..T, f r :=
      intervalIntegral.integral_mono_interval le_rfl
        (hStart m) (hTimeT m) (hPosOn a T) hInt

/-- If the density is bounded below by a constant A_k on its kth window,
its full time integral bounds the finite sum of A_k times window widths. -/
theorem h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
    (f : ℝ → ℝ) (a T : ℝ) (τ δ A : ℕ → ℝ)
    (haT : a ≤ T)
    (hf : ∀ r : ℝ, 0 ≤ f r)
    (hInt : IntervalIntegrable f volume a T)
    (hStart : ∀ k : ℕ, a ≤ τ k)
    (hWidth : ∀ k : ℕ, 0 ≤ δ k)
    (hEnd : ∀ k : ℕ, τ k + δ k ≤ T)
    (hSeparate : ∀ k : ℕ, τ k + δ k ≤ τ (k + 1))
    (hFloor : ∀ k : ℕ, ∀ r : ℝ,
      r ∈ Set.Icc (τ k) (τ k + δ k) → A k ≤ f r) :
    ∀ m : ℕ,
      (∑ k ∈ Finset.range m, δ k * A k) ≤
        ∫ r in a..T, f r := by
  have hIntSub (k : ℕ) :
      IntervalIntegrable f volume (τ k) (τ k + δ k) := by
    apply hInt.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (hWidth k)),
      Set.uIcc_of_le haT]
    exact Set.Icc_subset_Icc (hStart k) (hEnd k)
  have hIndividual (k : ℕ) :
      δ k * A k ≤ ∫ r in τ k..(τ k + δ k), f r := by
    have hCompare :
        (∫ _r in τ k..(τ k + δ k), A k) ≤
          ∫ r in τ k..(τ k + δ k), f r :=
      intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right (hWidth k))
        intervalIntegrable_const (hIntSub k) (hFloor k)
    have hConst :
        (∫ _r in τ k..(τ k + δ k), A k) = δ k * A k := by
      simp
    exact hConst ▸ hCompare
  intro m
  calc
    (∑ k ∈ Finset.range m, δ k * A k) ≤
      (∑ k ∈ Finset.range m,
        ∫ r in τ k..(τ k + δ k), f r) :=
      Finset.sum_le_sum (fun k _ => hIndividual k)
    _ ≤ ∫ r in a..T, f r :=
      h3Path_disjointNonnegativeWindows_finiteIntegralSum_le244
        f a T τ δ haT hf hInt hStart hWidth hEnd hSeparate m

/-- At any genuine strict-time Navier–Stokes slice, an arbitrary
finite-annulus dissipation quadratic lies below the full physical H³
viscous dissipation. The Fourier partition supplies the identity;
nonnegative low and high radial pieces supply the inequality. -/
theorem h3Path_actualFiniteAnnulusDissipation_le_fullAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (R Q : ℝ) :
    h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      velocityH3DissipationAt u t := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hLow : 0 ≤ h3PathActualLowRadialDissipation244 R G := by
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hHigh : 0 ≤ h3PathActualHighRadialDissipation244 Q G := by
    unfold h3PathActualHighRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hPartition :
      h3PathActualLowRadialDissipation244 Q G +
        h3PathActualHighRadialDissipation244 Q G =
          velocityH3DissipationAt u t :=
    h3Path_actualRadialDissipation_partition244 hH3 hClass t ht Q
  change h3PathActualLowRadialDissipation244 Q G -
    h3PathActualLowRadialDissipation244 R G ≤
      velocityH3DissipationAt u t
  linarith only [hLow, hHigh, hPartition]

/-- Necessary terminal L¹ cost constraint for the cofinal no-L²-trace cubic
branch: assuming the ACTUAL full H³ dissipation is interval-integrable up
to T, a pairwise-separated selection of cubic PDE windows has uniformly
bounded finite partial height sums. The constructed source and H³ spectral
ceilings are inherited from the unconditioned witness theorem.

This does NOT give a lower bound for the widths nor a contradiction; it
identifies the exact finite-summability obligation imposed by terminal L¹. -/
theorem h3Path_noL2Trace_cubicDisjointCost_finiteSums_le_fullDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, 0 < δ (v k)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) := by
  obtain ⟨τ, N, _K, _C, δ, hTime, hLimit, hWindows⟩ :=
    h3Path_noL2Trace_forces_cubicAnchoredPDEWindows244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hWindows n with
      ⟨_, _, _, hp, _, _, _, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hWindows n with
      ⟨_, _, _, _, _, hb, _, _, _, _, _⟩
    exact hb
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  have hFloor (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
    rcases hWindows (v k) with
      ⟨_, _, _, _, _, hb, _, _, _, hAnnulus, _⟩
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
        lt_of_le_of_lt hr.2 hb⟩
    exact (hAnnulus r hr).le.trans
      (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r hrClass ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1))
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
    (fun k => (hSeparated k (k + 1) (Nat.lt_succ_self k)).le)
    hFloor
  exact ⟨τ, δ, v, hMono, hCofinal, hSeparated,
    (fun k => hδ (v k)), hSum⟩

end
end PrimeTensor.FirstMonomialTriad
