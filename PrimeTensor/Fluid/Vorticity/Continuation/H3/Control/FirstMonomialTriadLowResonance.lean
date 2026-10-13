import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadCyclicIntegral

/-!
# No unintended resonances among the six sharp low-normal frequency centers

The sharp example uses p=(1,0,0), q=(t,t,0), r=(-1-t,-t,0) and their
negatives.  For t != 0 these six points are the image of the integer
lattice centers (1,0), (0,1), (-1,-1) and their negatives under the
injective plane embedding (a,b) |-> (a+tb,tb,0).

Every zero-sum triple drawn from the six centers is a permutation of
(p,q,r) or of (-p,-q,-r); there are no extra center resonances.
This is the finite-support combinatorial step toward Fourier bump
localization.  No Schwartz field or integrated lower bound is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Labels 0,1,2 denote p,q,r; labels 3,4,5 denote their negatives. -/
def lowNormalSignedLatticeCenter (k : Fin 6) : Fin 2 → ℤ :=
  match k.val with
  | 0 => ![1, 0]
  | 1 => ![0, 1]
  | 2 => ![-1, -1]
  | 3 => ![-1, 0]
  | 4 => ![0, -1]
  | _ => ![1, 1]

/-- The two allowed orientation classes, with all three distinct labels. -/
def lowNormalCoherentCenters (i j k : Fin 6) : Prop :=
  (i.val < 3 ∧ j.val < 3 ∧ k.val < 3 ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k) ∨
  (3 ≤ i.val ∧ 3 ≤ j.val ∧ 3 ≤ k.val ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k)

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

/-- Exhaustive, kernel-checked enumeration of the 216 labeled triples.
Only the six positive permutations and six reflected permutations vanish. -/
theorem lowNormalSignedLatticeCenter_zero_iff
    (i j k : Fin 6) :
    (∀ d : Fin 2,
      lowNormalSignedLatticeCenter i d +
        lowNormalSignedLatticeCenter j d +
          lowNormalSignedLatticeCenter k d = 0) ↔
      lowNormalCoherentCenters i j k := by
  -- Eliminate the quantified finite index before computing the 216 cases.
  -- Directly normalize the concrete integer coordinates in each of the 216 cases.
  have hFinite :
      (∀ d : Fin 2,
        lowNormalSignedLatticeCenter i d +
          lowNormalSignedLatticeCenter j d +
            lowNormalSignedLatticeCenter k d = 0) ↔
        (lowNormalSignedLatticeCenter i 0 +
            lowNormalSignedLatticeCenter j 0 +
              lowNormalSignedLatticeCenter k 0 = 0 ∧
         lowNormalSignedLatticeCenter i 1 +
            lowNormalSignedLatticeCenter j 1 +
              lowNormalSignedLatticeCenter k 1 = 0) := by
    constructor
    · intro h
      exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ d
      fin_cases d
      · exact h0
      · exact h1
  refine hFinite.trans ?_
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [lowNormalCoherentCenters, lowNormalSignedLatticeCenter]

/-- Any noncoherent triple has a nonzero lattice sum in one coordinate. -/
theorem lowNormalSignedLatticeCenter_noncoherent
    (i j k : Fin 6) (h : ¬ lowNormalCoherentCenters i j k) :
    ∃ d : Fin 2,
      lowNormalSignedLatticeCenter i d +
        lowNormalSignedLatticeCenter j d +
          lowNormalSignedLatticeCenter k d ≠ 0 := by
  have hz : ¬ (∀ d : Fin 2,
      lowNormalSignedLatticeCenter i d +
        lowNormalSignedLatticeCenter j d +
          lowNormalSignedLatticeCenter k d = 0) := by
    intro hv
    exact h ((lowNormalSignedLatticeCenter_zero_iff i j k).mp hv)
  push_neg at hz
  exact hz

/-- The t-dependent embedding into physical three-dimensional frequency. -/
def lowNormalLatticeEmbedding (t : ℝ) (a : Fin 2 → ℤ) : Fin 3 → ℝ :=
  ![(a 0 : ℝ) + t * (a 1 : ℝ), t * (a 1 : ℝ), 0]

@[simp] theorem lowNormalLatticeEmbedding_zero (t : ℝ) (a : Fin 2 → ℤ) :
    lowNormalLatticeEmbedding t a 0 = (a 0 : ℝ) + t * (a 1 : ℝ) := rfl

@[simp] theorem lowNormalLatticeEmbedding_one (t : ℝ) (a : Fin 2 → ℤ) :
    lowNormalLatticeEmbedding t a 1 = t * (a 1 : ℝ) := rfl

@[simp] theorem lowNormalLatticeEmbedding_two (t : ℝ) (a : Fin 2 → ℤ) :
    lowNormalLatticeEmbedding t a 2 = 0 := rfl

/-- A sum of three embedded lattice vectors vanishes precisely when the
integer lattice sum vanishes.  The only nondegeneracy required is t != 0. -/
theorem lowNormalLatticeEmbedding_three_zero_iff
    (t : ℝ) (ht : t ≠ 0) (a b c : Fin 2 → ℤ) :
    (∀ d : Fin 3,
      lowNormalLatticeEmbedding t a d +
        lowNormalLatticeEmbedding t b d +
          lowNormalLatticeEmbedding t c d = 0) ↔
      (∀ d : Fin 2, a d + b d + c d = 0) := by
  constructor
  · intro h
    have hBmul : t * (((a 1 + b 1 + c 1 : ℤ) : ℝ)) = 0 := by
      calc
        _ = t * (a 1 : ℝ) + t * (b 1 : ℝ) + t * (c 1 : ℝ) := by
          push_cast
          ring
        _ = 0 := by
          simpa only [lowNormalLatticeEmbedding_one] using h 1
    have hBreal : (((a 1 + b 1 + c 1 : ℤ) : ℝ)) = 0 :=
      (mul_eq_zero.mp hBmul).resolve_left ht
    have hB : a 1 + b 1 + c 1 = 0 := by exact_mod_cast hBreal
    have hAplus :
        (((a 0 + b 0 + c 0 : ℤ) : ℝ)) +
          t * (((a 1 + b 1 + c 1 : ℤ) : ℝ)) = 0 := by
      calc
        _ = lowNormalLatticeEmbedding t a 0 +
            lowNormalLatticeEmbedding t b 0 +
              lowNormalLatticeEmbedding t c 0 := by
          simp only [lowNormalLatticeEmbedding_zero]
          push_cast
          ring
        _ = 0 := h 0
    rw [hBreal] at hAplus
    have hAreal : (((a 0 + b 0 + c 0 : ℤ) : ℝ)) = 0 := by
      simpa using hAplus
    have hA : a 0 + b 0 + c 0 = 0 := by exact_mod_cast hAreal
    intro d
    fin_cases d
    · exact hA
    · exact hB
  · intro h
    have hA : a 0 + b 0 + c 0 = 0 := h 0
    have hB : a 1 + b 1 + c 1 = 0 := h 1
    have hAreal : (((a 0 + b 0 + c 0 : ℤ) : ℝ)) = 0 := by exact_mod_cast hA
    have hBreal : (((a 1 + b 1 + c 1 : ℤ) : ℝ)) = 0 := by exact_mod_cast hB
    intro d
    fin_cases d
    · calc
        _ = (((a 0 + b 0 + c 0 : ℤ) : ℝ)) +
            t * (((a 1 + b 1 + c 1 : ℤ) : ℝ)) := by
          change ((a 0 : ℝ) + t * (a 1 : ℝ)) +
              ((b 0 : ℝ) + t * (b 1 : ℝ)) +
              ((c 0 : ℝ) + t * (c 1 : ℝ)) = _
          push_cast
          ring
        _ = 0 := by rw [hAreal, hBreal]; ring
    · calc
        _ = t * (((a 1 + b 1 + c 1 : ℤ) : ℝ)) := by
          change t * (a 1 : ℝ) + t * (b 1 : ℝ) + t * (c 1 : ℝ) = _
          push_cast
          ring
        _ = 0 := by rw [hBreal]; ring
    · simp

/-- The physical frequency of one of the six labeled lattice centers. -/
def lowNormalSixCenter (t : ℝ) (k : Fin 6) : Fin 3 → ℝ :=
  lowNormalLatticeEmbedding t (lowNormalSignedLatticeCenter k)

/-- The first three labeled centers are exactly the sharpness family's p,q,r. -/
theorem lowNormalSixCenter_primary (t : ℝ) :
    lowNormalSixCenter t 0 = lowNormalAuditP ∧
    lowNormalSixCenter t 1 = lowNormalAuditQ t ∧
    lowNormalSixCenter t 2 = lowNormalAuditR t := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext d
    fin_cases d <;>
      norm_num [lowNormalSixCenter, lowNormalLatticeEmbedding,
        lowNormalSignedLatticeCenter, lowNormalAuditP,
        lowNormalAuditQ, lowNormalAuditR] <;> ring

/-- The remaining three centers are their opposite-frequency reality partners. -/
theorem lowNormalSixCenter_reflected (t : ℝ) :
    lowNormalSixCenter t 3 = (fun d => -lowNormalAuditP d) ∧
    lowNormalSixCenter t 4 = (fun d => -lowNormalAuditQ t d) ∧
    lowNormalSixCenter t 5 = (fun d => -lowNormalAuditR t d) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext d
    fin_cases d <;>
      norm_num [lowNormalSixCenter, lowNormalLatticeEmbedding,
        lowNormalSignedLatticeCenter, lowNormalAuditP,
        lowNormalAuditQ, lowNormalAuditR] <;> ring

/-- No spurious exact three-wave resonances survive the physical embedding:
there are exactly twelve ordered zero-momentum triples of centers. -/
theorem lowNormalSixCenter_zero_iff_coherent
    (t : ℝ) (ht : t ≠ 0) (i j k : Fin 6) :
    (∀ d : Fin 3,
      lowNormalSixCenter t i d + lowNormalSixCenter t j d +
        lowNormalSixCenter t k d = 0) ↔
      lowNormalCoherentCenters i j k := by
  exact (lowNormalLatticeEmbedding_three_zero_iff t ht
      (lowNormalSignedLatticeCenter i)
      (lowNormalSignedLatticeCenter j)
      (lowNormalSignedLatticeCenter k)).trans
    (lowNormalSignedLatticeCenter_zero_iff i j k)

/-- An excluded triple has a nonzero physical momentum sum.  This is the
strict separation needed to start constructing disjoint Fourier bumps. -/
theorem lowNormalSixCenter_noncoherent
    (t : ℝ) (ht : t ≠ 0) (i j k : Fin 6)
    (h : ¬ lowNormalCoherentCenters i j k) :
    ∃ d : Fin 3,
      lowNormalSixCenter t i d + lowNormalSixCenter t j d +
        lowNormalSixCenter t k d ≠ 0 := by
  have hn := (lowNormalSixCenter_zero_iff_coherent t ht i j k)
  by_contra hn0
  push_neg at hn0
  exact h (hn.mp hn0)

end
end PrimeTensor.FirstMonomialTriad
