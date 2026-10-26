import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECofinalWindows244
import Mathlib.Tactic

/-!
# Disjoint cofinal cubic finite-annulus PDE windows

Positive PDE-controlled annular windows may overlap, so their individual
integrated costs cannot simply be added. The terminal convergence of the
witness times supplies a distinct, purely geometric mechanism: every
chosen window ends strictly before T, and later witness times eventually
lie beyond that endpoint. Recursively selecting those later witnesses
produces a cofinal strictly increasing subsequence with pairwise separated
closed windows.

The extraction preserves the previously proved actual projected-source
ceilings, initial spectral coordinate bounds, polynomial width budgets,
pointwise cubic annular floors, and integrated costs. It does not assert
that the sum of costs diverges: the selected widths may shrink arbitrarily.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A sequence of positive intervals with each right endpoint before its
terminal accumulation point admits a strictly increasing, cofinal sequence
of pairwise separated intervals. No monotonicity of the original witness
times is required. -/
theorem h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
    (τ δ : ℕ → ℝ) (T : ℝ)
    (hτ : Tendsto τ atTop (𝓝 T))
    (hδ : ∀ n : ℕ, 0 < δ n)
    (hEnd : ∀ n : ℕ, τ n + δ n < T) :
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) := by
  classical
  have hPick : ∀ n : ℕ,
      ∃ m : ℕ, n < m ∧ τ n + δ n < τ m := by
    intro n
    have hNear : ∀ᶠ m : ℕ in atTop, τ n + δ n < τ m :=
      hτ.eventually (Ioi_mem_nhds (hEnd n))
    have hLater : ∀ᶠ m : ℕ in atTop, n + 1 ≤ m :=
      eventually_ge_atTop (n + 1)
    obtain ⟨m, hm, htm⟩ := (hLater.and hNear).exists
    exact ⟨m, lt_of_lt_of_le (Nat.lt_succ_self n) hm, htm⟩
  choose f hf using hPick
  let v : ℕ → ℕ := Nat.rec 0 (fun _ previous => f previous)
  have hvSucc (k : ℕ) : v (k + 1) = f (v k) := rfl
  have hMono : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hvSucc]
    exact (hf (v k)).1
  have hStep (k : ℕ) :
      τ (v k) + δ (v k) < τ (v (k + 1)) := by
    rw [hvSucc]
    exact (hf (v k)).2
  have hTimeMono : StrictMono (fun k : ℕ => τ (v k)) := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hpos := hδ (v k)
    have hsep := hStep k
    linarith only [hpos, hsep]
  refine ⟨v, hMono, hτ.comp hMono.tendsto_atTop, ?_⟩
  intro k l hkl
  have hkl' : k + 1 ≤ l := by omega
  exact lt_of_lt_of_le (hStep k) (hTimeMono.monotone hkl')

/-- Without strong terminal physical L² trace and with positive terminal
kinetic mass, the actual PDE-budgeted cubic annular windows can be selected
pairwise disjoint. Every selected window retains the same source ceiling,
initial H³ coordinate bound, polynomial persistence budget, cubic floor and
positive integrated cost as the original indexed witness.

This is an *unconditional geometric subsequence extraction relative to the
original no-trace hypotheses*, not a terminal divergence theorem. -/
theorem h3Path_noL2Trace_forces_disjointCubicAnchoredPDEWindows244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        v k ≤ N (v k) ∧
        0 ≤ K (v k) ∧ 0 ≤ C (v k) ∧
        0 < δ (v k) ∧ δ (v k) ≤ 1 ∧
        τ (v k) + δ (v k) < T ∧
        (∀ j : Fin 3,
          ‖(h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) j‖ ≤
            K (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C (v k)) ∧
        (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (K (v k)) (C (v k)) * δ (v k) +
          h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (C (v k)) * (δ (v k)) ^ 2 <
          (h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) -
              ((v k : ℝ) + 1) ^ 3 / 2) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          ((v k : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        (δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
          ∫ s in τ (v k)..(τ (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hWindows⟩ :=
    h3Path_noL2Trace_forces_cubicAnchoredPDEWindows244
      hH3 hClass hMass hNoTrace
  have hδ : ∀ n : ℕ, 0 < δ n := by
    intro n
    rcases hWindows n with
      ⟨_, _, _, hPositive, _, _, _, _, _, _, _⟩
    exact hPositive
  have hEnd : ∀ n : ℕ, τ n + δ n < T := by
    intro n
    rcases hWindows n with
      ⟨_, _, _, _, _, hBefore, _, _, _, _, _⟩
    exact hBefore
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  refine ⟨τ, N, K, C, δ, v, hMono, hCofinal, hSeparated, ?_⟩
  intro k
  rcases hWindows (v k) with
    ⟨hN, hK, hC, hPositive, hAtMostOne, hBefore,
      hBase, hSource, hBudget, hFloor, hCost⟩
  exact ⟨hN, hK, hC, hPositive, hAtMostOne, hBefore,
    hBase, hSource, hBudget, hFloor, hCost⟩

end
end PrimeTensor.FirstMonomialTriad
