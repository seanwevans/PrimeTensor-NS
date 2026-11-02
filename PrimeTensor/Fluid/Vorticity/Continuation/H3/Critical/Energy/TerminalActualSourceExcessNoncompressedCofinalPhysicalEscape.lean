import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessRelativeOuterFrequencyEscape
import Mathlib.Tactic

/-!
# Cofinal noncompression forces actual physical source or outer-frequency escape

This is the logical converse to the committed conditional cubic-terminal-clock
compression theorem. Its branch is the actual no-terminal-L²-trace sequence of
pairwise disjoint, strictly preterminal, exact PDE-certified cubic annuli.

On the bounded-certified-charge branch, if geometric cubic slack remains above
some fixed positive number arbitrarily late, then for EVERY proposed pair of
finite bounds B (energy-source and source-square) and D (relative outer radius),
arbitrarily late selected windows violate at least one bound.

An aggregate OR is essential: the proof does not pick a particular unbounded
quantity. None of the physical bounds is assumed, and no finite full terminal
H³ dissipation integral is introduced.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A universal conditional clock-collapse estimate has the cofinal
contrapositive: positive geometric excursions arbitrarily far out force
failure of at least one proposed finite source/source-square/relative-radius
bound arbitrarily far out. No limit existence is assumed for the burdens. -/
theorem h3Critical_scalar_cofinalNoncompression_forces_jointPhysicalEscape
    (G ES CS O R : ℕ → ℝ)
    (hClock : ∀ B D : ℝ, 0 ≤ B → 1 ≤ D →
      (∀ᶠ k : ℕ in atTop, ES k ≤ B) →
      (∀ᶠ k : ℕ in atTop, CS k ≤ B) →
      (∀ᶠ k : ℕ in atTop, O k ≤ D * R k) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, G k ≤ ε)
    (η : ℝ) (hη : 0 < η)
    (hNoncompression : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧ η < G k)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 1 ≤ D) (n : ℕ) :
    ∃ k : ℕ, n ≤ k ∧
      (B < ES k ∨ B < CS k ∨ D * R k < O k) := by
  classical
  by_contra hNone
  have hBound (k : ℕ) (hk : n ≤ k) :
      ES k ≤ B ∧ CS k ≤ B ∧ O k ≤ D * R k := by
    have hNoK : ¬ (B < ES k ∨ B < CS k ∨ D * R k < O k) := by
      intro hBad
      exact hNone ⟨k, hk, hBad⟩
    constructor
    · exact le_of_not_gt (fun hBad => hNoK (Or.inl hBad))
    constructor
    · exact le_of_not_gt (fun hBad => hNoK (Or.inr (Or.inl hBad)))
    · exact le_of_not_gt (fun hBad => hNoK (Or.inr (Or.inr hBad)))
  have hES : ∀ᶠ k : ℕ in atTop, ES k ≤ B :=
    Filter.eventually_atTop.2 ⟨n, fun k hk => (hBound k hk).1⟩
  have hCS : ∀ᶠ k : ℕ in atTop, CS k ≤ B :=
    Filter.eventually_atTop.2 ⟨n, fun k hk => (hBound k hk).2.1⟩
  have hOuter : ∀ᶠ k : ℕ in atTop, O k ≤ D * R k :=
    Filter.eventually_atTop.2 ⟨n, fun k hk => (hBound k hk).2.2⟩
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1
    (hClock B D hB hD hES hCS hOuter η hη)
  obtain ⟨k, hk, hg⟩ := hNoncompression (max n m)
  have hmk : m ≤ k := (le_max_right n m).trans hk
  exact (not_lt_of_ge (hm k hmk)) hg

/-- If BOTH source burdens really are eventually bounded, cofinal
noncompression forces arbitrarily large *relative outer cutoff*. This is
an implication of the joint-escape certificate, not a PDE assumption. -/
theorem h3Critical_scalar_boundedSource_noncompression_forces_outerEscape
    (G ES CS O R : ℕ → ℝ)
    (hEscape : ∀ η : ℝ, 0 < η →
      (∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧ η < G k) →
      ∀ B D : ℝ, 0 ≤ B → 1 ≤ D → ∀ n : ℕ,
        ∃ k : ℕ, n ≤ k ∧
          (B < ES k ∨ B < CS k ∨ D * R k < O k))
    (η : ℝ) (hη : 0 < η)
    (hNoncompression : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧ η < G k)
    (B : ℝ) (hB : 0 ≤ B)
    (hES : ∀ᶠ k : ℕ in atTop, ES k ≤ B)
    (hCS : ∀ᶠ k : ℕ in atTop, CS k ≤ B)
    (D : ℝ) (hD : 1 ≤ D) (n : ℕ) :
    ∃ k : ℕ, n ≤ k ∧ D * R k < O k := by
  obtain ⟨nES, hnES⟩ := Filter.eventually_atTop.1 hES
  obtain ⟨nCS, hnCS⟩ := Filter.eventually_atTop.1 hCS
  obtain ⟨k, hk, hBad⟩ := hEscape η hη hNoncompression
    B D hB hD (max n (max nES nCS))
  have hnk : n ≤ k := (le_max_left _ _).trans hk
  have hkES : nES ≤ k := (le_max_left nES nCS).trans
    ((le_max_right n (max nES nCS)).trans hk)
  have hkCS : nCS ≤ k := (le_max_right nES nCS).trans
    ((le_max_right n (max nES nCS)).trans hk)
  rcases hBad with he | hc | ho
  · exact False.elim ((not_lt_of_ge (hnES k hkES)) he)
  · exact False.elim ((not_lt_of_ge (hnCS k hkCS)) hc)
  · exact ⟨k, hnk, ho⟩

/-- In the genuine no-L²-trace physical H³ branch, either certified
positive disjoint annular charge sums are unbounded, or an arbitrarily
late noncompressed cubic terminal clock forces an arbitrarily late
violation of EVERY proposed pair of actual physical source and relative
outer-frequency bounds. This selects neither a single escaping burden nor
a Navier–Stokes continuation theorem. -/
theorem h3Critical_noL2Trace_disjointAnnuli_noncompression_forces_cofinalSourceOuterEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ C δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        v k ≤ N (v k) ∧ 0 ≤ C (v k) ∧ 0 < δ (v k) ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ ^ 2 ≤
          velocityH3EnergyAt u (t (v k)) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2)) ∧
      ((∀ M : ℝ, ∃ m : ℕ,
        M < ∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
       (∀ η : ℝ, 0 < η →
         (∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
           η < ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4)) →
         ∀ B D : ℝ, 0 ≤ B → 1 ≤ D → ∀ n : ℕ,
           ∃ k : ℕ, n ≤ k ∧
             (B < velocityH3EnergyAt u (t (v k)) * (C (v k)) ^ 2 ∨
              B < (C (v k)) ^ 2 ∨
              D * ((v k : ℝ) + 1) < ((N (v k) : ℝ) + 2)))) := by
  obtain ⟨t, N, C, δ, v, hv, hCofinal, hSeparated, hPhysical, hAlternative⟩ :=
    h3Critical_noL2Trace_disjointActiveAnnuli_boundedSourceRelativeOuter_forces_compression
      hH3 hClass hNoTrace
  refine ⟨t, N, C, δ, v, hv, hCofinal, hSeparated, hPhysical, ?_⟩
  rcases hAlternative with hUnbounded | hClock
  · exact Or.inl hUnbounded
  · right
    let G : ℕ → ℝ := fun k =>
      ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4)
    let ES : ℕ → ℝ := fun k =>
      velocityH3EnergyAt u (t (v k)) * (C (v k)) ^ 2
    let CS : ℕ → ℝ := fun k => (C (v k)) ^ 2
    let O : ℕ → ℝ := fun k => (N (v k) : ℝ) + 2
    let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
    have hGate : ∀ B D : ℝ, 0 ≤ B → 1 ≤ D →
        (∀ᶠ k : ℕ in atTop, ES k ≤ B) →
        (∀ᶠ k : ℕ in atTop, CS k ≤ B) →
        (∀ᶠ k : ℕ in atTop, O k ≤ D * R k) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, G k ≤ ε := by
      intro B D hB hD hES hCS hO ε hε
      have hES' : ∀ᶠ k : ℕ in atTop,
          velocityH3EnergyAt u (t (v k)) * (C (v k)) ^ 2 ≤ B := by
        simpa only [ES] using hES
      have hCS' : ∀ᶠ k : ℕ in atTop, (C (v k)) ^ 2 ≤ B := by
        simpa only [CS] using hCS
      have hO' : ∀ᶠ k : ℕ in atTop,
          ((N (v k) : ℝ) + 2) ≤ D * ((v k : ℝ) + 1) := by
        simpa only [O, R] using hO
      simpa only [G] using (hClock B D hB hD hES' hCS' hO' ε hε)
    intro η hη hNoncompression B D hB hD n
    have hCo : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧ η < G k := by
      simpa only [G] using hNoncompression
    have hEscape :=
      h3Critical_scalar_cofinalNoncompression_forces_jointPhysicalEscape
        G ES CS O R hGate η hη hCo B D hB hD n
    simpa only [ES, CS, O, R] using hEscape

end
end PrimeTensor.Bridge.Euclidean
