import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzDifferenceEnergyBridge244
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# H³ energy differences force Cauchy convergence of all signed transport slots

This module closes the analytical bridge from the actual Schwartz order-two and
order-three quadratic energies of a difference to the mixed L²/L⁴ jet Cauchy
criterion. The genuine 27-slot quartic Gagliardo--Nirenberg estimate is used
without postulating separate L⁴ convergence or bounded jet factors.

For a Schwartz sequence `f`, simultaneous tail smallness of E₂(f_m-f_n) and
E₃(f_m-f_n) implies that each third-order L² difference and each second-order
L⁴ difference is small. The previously proved 243-slot strong-jet completion
therefore constructs a unique scalar limit of the entire signed monomial.

This is an H³ *energy Cauchy* statement. It does not construct a Schwartz
approximation to a specified non-Schwartz physical slice or identify the
resulting scalar with that slice's physical transport pairing.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeH3EnergyCauchy244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- One common late-tail bound on both genuine second- and third-order
Schwartz H³ quadratic energies. Their nonnegativity is already proved. -/
def SchwartzH3DifferenceEnergyCauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
      lowNormalRealSchwartzH3Energy2
        (schwartzVelocityDifference244 (f m) (f n)) < η ∧
      lowNormalRealSchwartzH3Energy3
        (schwartzVelocityDifference244 (f m) (f n)) < η

/-- Select any nonnegative integrand from its complete 81-slot mass. -/
private theorem fourfold_mass_select244
    (F : A3 → A3 → A3 → A3 → ℝ)
    (hF : ∀ j i k l, 0 ≤ F j i k l)
    (j i k l : A3) :
    F j i k l ≤ ∑ j' : A3, ∑ i' : A3, ∑ k' : A3,
      ∑ l' : A3, F j' i' k' l' := by
  classical
  have hL : F j i k l ≤ ∑ l' : A3, F j i k l' :=
    Finset.single_le_sum (fun l' _ => hF j i k l') (Finset.mem_univ l)
  have hK : (∑ l' : A3, F j i k l') ≤
      ∑ k' : A3, ∑ l' : A3, F j i k' l' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun k' : A3 => ∑ l' : A3, F j i k' l')
    · intro k' _
      apply Finset.sum_nonneg
      intro l' _
      exact hF j i k' l'
    · exact Finset.mem_univ k
  have hI : (∑ k' : A3, ∑ l' : A3, F j i k' l') ≤
      ∑ i' : A3, ∑ k' : A3, ∑ l' : A3, F j i' k' l' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun i' : A3 => ∑ k' : A3, ∑ l' : A3, F j i' k' l')
    · intro i' _
      apply Finset.sum_nonneg
      intro k' _
      apply Finset.sum_nonneg
      intro l' _
      exact hF j i' k' l'
    · exact Finset.mem_univ i
  have hJ : (∑ i' : A3, ∑ k' : A3, ∑ l' : A3, F j i' k' l') ≤
      ∑ j' : A3, ∑ i' : A3, ∑ k' : A3, ∑ l' : A3,
        F j' i' k' l' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun j' : A3 => ∑ i' : A3, ∑ k' : A3, ∑ l' : A3, F j' i' k' l')
    · intro j' _
      apply Finset.sum_nonneg
      intro i' _
      apply Finset.sum_nonneg
      intro k' _
      apply Finset.sum_nonneg
      intro l' _
      exact hF j' i' k' l'
    · exact Finset.mem_univ j
  exact (hL.trans hK).trans (hI.trans hJ)

/-- Select any nonnegative integrand from its complete 27-slot mass. -/
private theorem threefold_mass_select244
    (F : A3 → A3 → A3 → ℝ)
    (hF : ∀ j i k, 0 ≤ F j i k)
    (j i k : A3) :
    F j i k ≤ ∑ j' : A3, ∑ i' : A3, ∑ k' : A3,
      F j' i' k' := by
  classical
  have hK : F j i k ≤ ∑ k' : A3, F j i k' :=
    Finset.single_le_sum (fun k' _ => hF j i k') (Finset.mem_univ k)
  have hI : (∑ k' : A3, F j i k') ≤
      ∑ i' : A3, ∑ k' : A3, F j i' k' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun i' : A3 => ∑ k' : A3, F j i' k')
    · intro i' _
      apply Finset.sum_nonneg
      intro k' _
      exact hF j i' k'
    · exact Finset.mem_univ i
  have hJ : (∑ i' : A3, ∑ k' : A3, F j i' k') ≤
      ∑ j' : A3, ∑ i' : A3, ∑ k' : A3, F j' i' k' := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset A3))
      (f := fun j' : A3 => ∑ i' : A3, ∑ k' : A3, F j' i' k')
    · intro j' _
      apply Finset.sum_nonneg
      intro i' _
      apply Finset.sum_nonneg
      intro k' _
      exact hF j' i' k'
    · exact Finset.mem_univ j
  exact (hK.trans hI).trans hJ

/-- An individual genuine third-derivative difference root has square at
most the complete order-three energy of the velocity difference. -/
theorem schwartzThirdJetDifferenceRoot_sq_le_E3244
    (f g : A3 → SchwartzMap V3 ℝ) (j i k l : A3) :
    (schwartzThirdJetDifferenceRoot244 f g j i k l) ^ 2 ≤
      lowNormalRealSchwartzH3Energy3 (schwartzVelocityDifference244 f g) := by
  have hInt :
      0 ≤ ∫ x : V3,
        (((∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k}
               (∂_{h3FourierAxisDirection l} (f j)))) -
           (∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k}
               (∂_{h3FourierAxisDirection l} (g j))))) x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have hRoot :
      (schwartzThirdJetDifferenceRoot244 f g j i k l) ^ 2 =
        ∫ x : V3,
          (((∂_{h3FourierAxisDirection i}
               (∂_{h3FourierAxisDirection k}
                 (∂_{h3FourierAxisDirection l} (f j)))) -
             (∂_{h3FourierAxisDirection i}
               (∂_{h3FourierAxisDirection k}
                 (∂_{h3FourierAxisDirection l} (g j))))) x) ^ 2 := by
    unfold schwartzThirdJetDifferenceRoot244 schwartzIntegralL2Root244
    exact Real.sq_sqrt hInt
  rw [hRoot, ← schwartzThirdJetDifference_squareMass_eq_energy3244]
  let F : A3 → A3 → A3 → A3 → ℝ := fun a b c d =>
    ∫ x : V3,
      (((∂_{h3FourierAxisDirection b}
           (∂_{h3FourierAxisDirection c}
             (∂_{h3FourierAxisDirection d} (f a)))) -
         (∂_{h3FourierAxisDirection b}
           (∂_{h3FourierAxisDirection c}
             (∂_{h3FourierAxisDirection d} (g a))))) x) ^ 2
  change F j i k l ≤ ∑ a : A3, ∑ b : A3, ∑ c : A3,
    ∑ d : A3, F a b c d
  exact fourfold_mass_select244 F
    (fun a b c d => integral_nonneg (fun x => sq_nonneg _)) j i k l

/-- An individual fourth-power second-derivative difference integral is
bounded by the total quartic mass of the velocity difference. -/
private theorem second_jet_integral_le_quarticMass244
    (f g : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    (∫ x : V3,
      (((∂_{h3FourierAxisDirection i}
           (∂_{h3FourierAxisDirection k} (f j))) -
         (∂_{h3FourierAxisDirection i}
           (∂_{h3FourierAxisDirection k} (g j)))) x) ^ 4) ≤
      lowNormalRealSchwartzSecondJetsQuarticMass
        (schwartzVelocityDifference244 f g) := by
  rw [← schwartzSecondJetDifference_quarticMass_eq244]
  let F : A3 → A3 → A3 → ℝ := fun a b c =>
    ∫ x : V3,
      (((∂_{h3FourierAxisDirection b}
           (∂_{h3FourierAxisDirection c} (f a))) -
         (∂_{h3FourierAxisDirection b}
           (∂_{h3FourierAxisDirection c} (g a)))) x) ^ 4
  change F j i k ≤ ∑ a : A3, ∑ b : A3, ∑ c : A3, F a b c
  exact threefold_mass_select244 F
    (fun a b c => integral_nonneg (fun x => by positivity)) j i k

/-- One genuine second-derivative L⁴ root, raised to the eighth power,
obeys the exact 27-slot Gagliardo--Nirenberg energy bound. -/
theorem schwartzSecondJetDifferenceRoot_pow_eight_le_E2E3244
    (f g : A3 → SchwartzMap V3 ℝ) (j i k : A3) :
    (schwartzSecondJetDifferenceRoot244 f g j i k) ^ 8 ≤
      lowNormalSecondJetSobolevRealConstant ^ 6 *
        (lowNormalRealSchwartzH3Energy2 (schwartzVelocityDifference244 f g) *
          (((Fintype.card A3 : ℝ) *
              lowNormalRealSchwartzH3Energy3
                (schwartzVelocityDifference244 f g)) ^ 3)) := by
  let I : ℝ := ∫ x : V3,
    (((∂_{h3FourierAxisDirection i}
         (∂_{h3FourierAxisDirection k} (f j))) -
       (∂_{h3FourierAxisDirection i}
         (∂_{h3FourierAxisDirection k} (g j)))) x) ^ 4
  have hI : 0 ≤ I := integral_nonneg (fun x => by positivity)
  have hPow :
      (schwartzSecondJetDifferenceRoot244 f g j i k) ^ 4 = I := by
    unfold schwartzSecondJetDifferenceRoot244 schwartzIntegralL4Root244
    change (Real.sqrt (Real.sqrt I)) ^ 4 = I
    calc
      (Real.sqrt (Real.sqrt I)) ^ 4 =
          ((Real.sqrt (Real.sqrt I)) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt I) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg I)]
      _ = I := Real.sq_sqrt hI
  have hSelected : I ≤
      lowNormalRealSchwartzSecondJetsQuarticMass
        (schwartzVelocityDifference244 f g) := by
    exact second_jet_integral_le_quarticMass244 f g j i k
  calc
    (schwartzSecondJetDifferenceRoot244 f g j i k) ^ 8 = I ^ 2 := by
      rw [show (schwartzSecondJetDifferenceRoot244 f g j i k) ^ 8 =
        ((schwartzSecondJetDifferenceRoot244 f g j i k) ^ 4) ^ 2 by ring,
        hPow]
    _ ≤ (lowNormalRealSchwartzSecondJetsQuarticMass
        (schwartzVelocityDifference244 f g)) ^ 2 :=
      pow_le_pow_left₀ hI hSelected 2
    _ ≤ _ :=
      lowNormalRealSchwartz_secondJets_quarticGN_real_normalized
        (schwartzVelocityDifference244 f g)

/-- Basic small-power transfer; positive comparison radii do not require
any extra nonzero hypothesis on a Schwartz derivative root. -/
private theorem nonneg_root_lt_of_pow_lt244
    {r δ : ℝ} (_hr : 0 ≤ r) (hδ : 0 < δ)
    (k : ℕ) (_hk : 0 < k) (hpow : r ^ k < δ ^ k) : r < δ := by
  by_contra hnot
  have hle : δ ≤ r := le_of_not_gt hnot
  have hp : δ ^ k ≤ r ^ k := pow_le_pow_left₀ (le_of_lt hδ) hle k
  exact (not_lt_of_ge hp) hpow

/-- Ordinary H³ energy Cauchy control forces the exact three difference
jet norms in each of the 243 physical transport slots to be Cauchy-small.
The 27-slot quartic Gagliardo--Nirenberg estimate supplies the L⁴ step. -/
theorem SchwartzH3DifferenceEnergyCauchy244.toStrongJets
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    (hEnergy : SchwartzH3DifferenceEnergyCauchy244 f) :
    Schwartz243StrongJetCauchy244 f := by
  intro p δ hδ
  let C : ℝ := lowNormalSecondJetSobolevRealConstant ^ 6 *
    (Fintype.card A3 : ℝ) ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hDen : 0 < C + 1 := by linarith
  let η : ℝ := min 1 (min (δ ^ 2) (δ ^ 8 / (C + 1)))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by norm_num) (lt_min (pow_pos hδ 2)
      (div_pos (pow_pos hδ 8) hDen))
  have hηone : η ≤ 1 := by dsimp [η]; exact min_le_left _ _
  have hηsq : η ≤ δ ^ 2 := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hηpow : η ≤ δ ^ 8 / (C + 1) := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hTail⟩ := hEnergy η hη
  refine ⟨N, ?_⟩
  intro m hm n hn
  let E2 : ℝ := lowNormalRealSchwartzH3Energy2
    (schwartzVelocityDifference244 (f m) (f n))
  let E3 : ℝ := lowNormalRealSchwartzH3Energy3
    (schwartzVelocityDifference244 (f m) (f n))
  have hE2nonneg : 0 ≤ E2 := lowNormalRealSchwartzH3Energy2_nonneg _
  have hE3nonneg : 0 ≤ E3 := lowNormalRealSchwartzH3Energy3_nonneg _
  obtain ⟨hE2small, hE3small⟩ := hTail m hm n hn
  have hE2one : E2 ≤ 1 := (le_of_lt hE2small).trans hηone
  have hE3one : E3 ≤ 1 := (le_of_lt hE3small).trans hηone
  have hE3sq : E3 < δ ^ 2 := lt_of_lt_of_le hE3small hηsq
  have hE3pow : E3 < δ ^ 8 / (C + 1) :=
    lt_of_lt_of_le hE3small hηpow
  have hE3sqOne : E3 ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ hE3nonneg hE3one 2)
  have hE3cub : E3 ^ 3 ≤ E3 := by
    have hp := mul_le_mul_of_nonneg_left hE3sqOne hE3nonneg
    nlinarith only [hp]
  have hProduct : E2 * E3 ^ 3 ≤ E3 := by
    calc
      E2 * E3 ^ 3 ≤ 1 * E3 ^ 3 :=
        mul_le_mul_of_nonneg_right hE2one (pow_nonneg hE3nonneg 3)
      _ = E3 ^ 3 := by ring
      _ ≤ E3 := hE3cub
  have hBound : C * (E2 * E3 ^ 3) < δ ^ 8 := by
    have hCbound : C * (E2 * E3 ^ 3) ≤ C * E3 :=
      mul_le_mul_of_nonneg_left hProduct hC
    have hEnlarged : C * E3 ≤ C * (δ ^ 8 / (C + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hE3pow) hC
    have hSmaller : C * (δ ^ 8 / (C + 1)) < δ ^ 8 := by
      have hCancel : (δ ^ 8 / (C + 1)) * (C + 1) = δ ^ 8 :=
        div_mul_cancel₀ _ (ne_of_gt hDen)
      have hPos : 0 < δ ^ 8 / (C + 1) :=
        div_pos (pow_pos hδ 8) hDen
      nlinarith only [hCancel, hPos]
    exact lt_of_le_of_lt (le_trans hCbound hEnlarged) hSmaller
  have hThird (j i k l : A3) :
      schwartzThirdJetDifferenceRoot244 (f m) (f n) j i k l < δ := by
    have hSq := schwartzThirdJetDifferenceRoot_sq_le_E3244
      (f m) (f n) j i k l
    change (schwartzThirdJetDifferenceRoot244 (f m) (f n) j i k l) ^ 2 ≤ E3
      at hSq
    have hPow : (schwartzThirdJetDifferenceRoot244
        (f m) (f n) j i k l) ^ 2 < δ ^ 2 :=
      lt_of_le_of_lt hSq hE3sq
    exact nonneg_root_lt_of_pow_lt244
      (schwartzIntegralL2Root244_nonneg _) hδ 2 (by norm_num) hPow
  have hSecond (j i k : A3) :
      schwartzSecondJetDifferenceRoot244 (f m) (f n) j i k < δ := by
    have hRoot := schwartzSecondJetDifferenceRoot_pow_eight_le_E2E3244
      (f m) (f n) j i k
    change (schwartzSecondJetDifferenceRoot244 (f m) (f n) j i k) ^ 8 ≤
      lowNormalSecondJetSobolevRealConstant ^ 6 *
        (E2 * (((Fintype.card A3 : ℝ) * E3) ^ 3)) at hRoot
    have hRearranged :
        lowNormalSecondJetSobolevRealConstant ^ 6 *
          (E2 * (((Fintype.card A3 : ℝ) * E3) ^ 3)) =
            C * (E2 * E3 ^ 3) := by
      dsimp [C]
      ring
    rw [hRearranged] at hRoot
    exact nonneg_root_lt_of_pow_lt244
      (schwartzIntegralL4Root244_nonneg _) hδ 8 (by norm_num)
      (lt_of_le_of_lt hRoot hBound)
  change
    schwartzThirdJetDifferenceRoot244 (f m) (f n)
        p.2.2.2.2 p.1 p.2.1 p.2.2.1 < δ ∧
    schwartzSecondJetDifferenceRoot244 (f m) (f n)
        p.2.2.2.1 p.2.1 p.2.2.1 < δ ∧
    schwartzSecondJetDifferenceRoot244 (f m) (f n)
        p.2.2.2.2 p.1 p.2.2.2.1 < δ
  exact ⟨hThird _ _ _ _, hSecond _ _ _, hSecond _ _ _⟩

/-- Finitely many individually Cauchy-small real discrepancies have a
uniformly small complete sum on one common late index pair. -/
private theorem finite_energy_jet_sum_small244
    {J : Type*} [Fintype J]
    (E : ℕ → ℕ → J → ℝ)
    (hE : ∀ p : J, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n → E m n p < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        (∑ p : J, E m n p) < ε := by
  classical
  have hs (s : Finset J) :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
          (∑ p ∈ s, E m n p) < ε := by
    induction s using Finset.induction_on with
    | empty =>
        intro ε hε
        refine ⟨0, ?_⟩
        intro m hm n hn
        simpa using hε
    | @insert p s hp ih =>
        intro ε hε
        have hHalf : 0 < ε / 2 := by positivity
        obtain ⟨N1, h1⟩ := hE p (ε / 2) hHalf
        obtain ⟨N2, h2⟩ := ih (ε / 2) hHalf
        refine ⟨max N1 N2, ?_⟩
        intro m hm n hn
        have hm1 : N1 ≤ m := le_trans (le_max_left N1 N2) hm
        have hn1 : N1 ≤ n := le_trans (le_max_left N1 N2) hn
        have hm2 : N2 ≤ m := le_trans (le_max_right N1 N2) hm
        have hn2 : N2 ≤ n := le_trans (le_max_right N1 N2) hn
        have hpSmall := h1 m hm1 n hn1
        have hsSmall := h2 m hm2 n hn2
        rw [Finset.sum_insert hp]
        linarith
  exact hs (Finset.univ : Finset J)

/-- The ordinary order-two and order-three Schwartz difference energies
control the COMPLETE 81+27 mixed L²/L⁴ graph, not only selected slots. -/
theorem SchwartzH3DifferenceEnergyCauchy244.toMixedGraph
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    (hEnergy : SchwartzH3DifferenceEnergyCauchy244 f) :
    SchwartzMixedJetGraphCauchy244 f := by
  have hStrong := hEnergy.toStrongJets
  have hThirdPoint (j i k l : A3) :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
          schwartzThirdJetDifferenceRoot244 (f m) (f n) j i k l < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hStrong (i, (k, (l, (j, j)))) ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    exact (hN m hm n hn).1
  have hSecondPoint (j i k : A3) :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
          schwartzSecondJetDifferenceRoot244 (f m) (f n) j i k < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hStrong (j, (i, (k, (j, j)))) ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    exact (hN m hm n hn).2.1
  let E3 : ℕ → ℕ → (A3 × (A3 × (A3 × A3))) → ℝ :=
    fun m n p => schwartzThirdJetDifferenceRoot244
      (f m) (f n) p.1 p.2.1 p.2.2.1 p.2.2.2
  let E2 : ℕ → ℕ → (A3 × (A3 × A3)) → ℝ :=
    fun m n p => schwartzSecondJetDifferenceRoot244
      (f m) (f n) p.1 p.2.1 p.2.2
  have hE3 : ∀ p, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        E3 m n p < ε := by
    rintro ⟨j, i, k, l⟩ ε hε
    exact hThirdPoint j i k l ε hε
  have hE2 : ∀ p, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        E2 m n p < ε := by
    rintro ⟨j, i, k⟩ ε hε
    exact hSecondPoint j i k ε hε
  intro δ hδ
  have hHalf : 0 < δ / 2 := by positivity
  obtain ⟨N3, hN3⟩ := finite_energy_jet_sum_small244
    E3 hE3 (δ / 2) hHalf
  obtain ⟨N2, hN2⟩ := finite_energy_jet_sum_small244
    E2 hE2 (δ / 2) hHalf
  refine ⟨max N3 N2, ?_⟩
  intro m hm n hn
  have hm3 : N3 ≤ m := le_trans (le_max_left N3 N2) hm
  have hn3 : N3 ≤ n := le_trans (le_max_left N3 N2) hn
  have hm2 : N2 ≤ m := le_trans (le_max_right N3 N2) hm
  have hn2 : N2 ≤ n := le_trans (le_max_right N3 N2) hn
  have hThird : schwartzThirdJetGraphDistance244 (f m) (f n) < δ / 2 := by
    simpa only [schwartzThirdJetGraphDistance244, E3,
      Fintype.sum_prod_type] using hN3 m hm3 n hn3
  have hSecond : schwartzSecondJetGraphDistance244 (f m) (f n) < δ / 2 := by
    simpa only [schwartzSecondJetGraphDistance244, E2,
      Fintype.sum_prod_type] using hN2 m hm2 n hn2
  unfold schwartzMixedJetGraphDistance244
  linarith

/-- The signed, complete 243-slot nonlinear Schwartz first monomial has a
real limit whenever its genuine quadratic E₂/E₃ difference energies are
Cauchy-small. No separate L⁴ input or uniform jet bound is assumed. -/
theorem lowNormalRealSchwartz_firstMonomial_existsLimit_of_H3EnergyCauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hEnergy : SchwartzH3DifferenceEnergyCauchy244 f) :
    ∃ M : ℝ,
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n))
        atTop (𝓝 M) :=
  lowNormalRealSchwartz_firstMonomial_existsLimit_of_mixedJetGraph244
    f hEnergy.toMixedGraph

end
end PrimeTensor.FirstMonomialTriad
