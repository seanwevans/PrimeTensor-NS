import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientJetContinuity244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentSlotCauchy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAutomaticJetBounds244
import Mathlib.Tactic

/-!
# Natural L²–L²–L∞ continuity of the full signed 3–3–1 gradient transport

The previous gradient proof requires third-order derivative L⁴ convergence,
which is not implied by the natural H³ graph norm. Here both third-order
factors require only L² convergence. The first-order factor requires uniform
pointwise control and pointwise difference convergence (in a common L∞ gauge).

The core is the real Schwarz Cauchy–Schwarz inequality combined with a
pointwise bound for the low derivative. We then use exact three-factor
integral telescoping and the existing L² reverse triangle inequality.
The four gradient triples at each five-index slot are retained exactly.

Still open: deriving the required first-derivative uniform bounds and their
vanishing difference gauges from *physical* H³ Sobolev approximation, and
identifying the limit with a general physical NS slice. No unconditional
Navier–Stokes regularity or arbitrary-Schwartz realization is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullGradientL2L2Linf244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine L²–L²–L∞ Hölder inequality on the real Schwartz carrier.
The infinity bound is pointwise; no abstract measure-space supremum or
unverified normalization is used. -/
theorem schwartzTripleIntegral_abs_le_L2L2Linf244
    (a b c : SchwartzMap V3 ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hc : ∀ x : V3, |c x| ≤ K) :
    |schwartzTripleIntegral244 a b c| ≤
      K * (schwartzIntegralL2Root244 a * schwartzIntegralL2Root244 b) := by
  have hAB : Integrable (fun x : V3 => a x * b x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a b).integrable
  have hABC : Integrable (fun x : V3 => a x * (b x * c x)) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) b c)).integrable
  have hAbsAB : Integrable (fun x : V3 => |a x| * |b x|) := by
    simpa only [Real.norm_eq_abs, abs_mul] using hAB.norm
  have hAbsABC : Integrable (fun x : V3 => |a x| * (|b x| * |c x|)) := by
    simpa only [Real.norm_eq_abs, abs_mul] using hABC.norm
  have hUpper : Integrable (fun x : V3 => K * (|a x| * |b x|)) :=
    hAbsAB.const_mul K
  have hTwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
    norm_num
  have ha : MemLp (fun x : V3 => |a x|)
      (ENNReal.ofReal (2 : ℝ)) volume := by
    have h := (a.memLp 2 volume).norm
    simpa [Real.norm_eq_abs, hTwo] using h
  have hb : MemLp (fun x : V3 => |b x|)
      (ENNReal.ofReal (2 : ℝ)) volume := by
    have h := (b.memLp 2 volume).norm
    simpa [Real.norm_eq_abs, hTwo] using h
  have hHolder :
      (∫ x : V3, |a x| * |b x|) ≤
        (∫ x : V3, |a x| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : V3, |b x| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall (fun x : V3 => abs_nonneg (a x)))
      (Filter.Eventually.of_forall (fun x : V3 => abs_nonneg (b x))) ha hb
  have hRoots :
      (∫ x : V3, |a x| * |b x|) ≤
        schwartzIntegralL2Root244 a * schwartzIntegralL2Root244 b := by
    simp only [Real.rpow_two, sq_abs] at hHolder
    simpa only [schwartzIntegralL2Root244, ← Real.sqrt_eq_rpow] using hHolder
  have hPointwise : ∀ x : V3,
      |a x| * (|b x| * |c x|) ≤ K * (|a x| * |b x|) := by
    intro x
    calc
      |a x| * (|b x| * |c x|) =
          (|a x| * |b x|) * |c x| := by ring
      _ ≤ (|a x| * |b x|) * K :=
        mul_le_mul_of_nonneg_left (hc x)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = K * (|a x| * |b x|) := by ring
  unfold schwartzTripleIntegral244
  calc
    |∫ x : V3, a x * (b x * c x)| ≤
        ∫ x : V3, |a x * (b x * c x)| := abs_integral_le_integral_abs
    _ = ∫ x : V3, |a x| * (|b x| * |c x|) := by simp only [abs_mul]
    _ ≤ ∫ x : V3, K * (|a x| * |b x|) :=
      integral_mono hAbsABC hUpper hPointwise
    _ = K * (∫ x : V3, |a x| * |b x|) := by rw [integral_const_mul]
    _ ≤ K * (schwartzIntegralL2Root244 a *
          schwartzIntegralL2Root244 b) :=
      mul_le_mul_of_nonneg_left hRoots hK

/-- A third-order L² difference implies convergence of the undifferenced
L² root, including when the limit is zero. -/
theorem schwartzIntegralL2Root_tendsto_of_difference244
    (A : ℕ → SchwartzMap V3 ℝ) (a : SchwartzMap V3 ℝ)
    (hDiff : Tendsto (fun n => schwartzIntegralL2Root244 (A n - a))
      atTop (𝓝 0)) :
    Tendsto (fun n => schwartzIntegralL2Root244 (A n))
      atTop (𝓝 (schwartzIntegralL2Root244 a)) := by
  have hAbs : Tendsto
      (fun n => |schwartzIntegralL2Root244 (A n) -
        schwartzIntegralL2Root244 a|) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact schwartzIntegralL2Root_abs_sub_le_difference244 (A n) a
    · exact hDiff
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hAbs

/-- Two L² difference-jet limits, one bounded first jet, and one vanishing
L∞ first-jet error suffice for signed 3–3–1 triple continuity. The formerly
assumed L⁴ third-jet difference is gone. -/
def SchwartzGradientTripleL2L2LinfJets244
    (A B C : ℕ → SchwartzMap V3 ℝ)
    (a b c : SchwartzMap V3 ℝ) : Prop :=
  Tendsto (fun n => schwartzIntegralL2Root244 (A n - a)) atTop (𝓝 0) ∧
  Tendsto (fun n => schwartzIntegralL2Root244 (B n - b)) atTop (𝓝 0) ∧
  ∃ (K : ℝ) (δ : ℕ → ℝ), 0 ≤ K ∧
    (∀ n x, |C n x| ≤ K) ∧
    (∀ n x, |(C n - c) x| ≤ δ n) ∧
    Tendsto δ atTop (𝓝 0)

/-- Signed triple continuity in the Sobolev-compatible 2–2–infinity
exponents, retaining the canonical factor two. -/
theorem fullGradientTriple_tendsto_of_L2L2LinfJets244
    (A B C : ℕ → SchwartzMap V3 ℝ)
    (a b c : SchwartzMap V3 ℝ)
    (hJets : SchwartzGradientTripleL2L2LinfJets244 A B C a b c) :
    Tendsto (fun n => fullGradientTriple244 (A n) (B n) (C n)) atTop
      (𝓝 (fullGradientTriple244 a b c)) := by
  obtain ⟨hA, hB, K, δ, hK, hC, hDiffC, hδ⟩ := hJets
  have hBNorm := schwartzIntegralL2Root_tendsto_of_difference244 B b hB
  have hFirst : Tendsto (fun n =>
      K * (schwartzIntegralL2Root244 (A n - a) *
        schwartzIntegralL2Root244 (B n))) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K)).mul
        (hA.mul hBNorm)
  have hSecond : Tendsto (fun n =>
      K * (schwartzIntegralL2Root244 a *
        schwartzIntegralL2Root244 (B n - b))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K)).mul
        ((tendsto_const_nhds : Tendsto
          (fun _ : ℕ => schwartzIntegralL2Root244 a)
          atTop (𝓝 (schwartzIntegralL2Root244 a))).mul hB)
  have hThird : Tendsto (fun n =>
      δ n * (schwartzIntegralL2Root244 a *
        schwartzIntegralL2Root244 b)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hδ.mul
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => schwartzIntegralL2Root244 a *
          schwartzIntegralL2Root244 b)
        atTop (𝓝 (schwartzIntegralL2Root244 a *
          schwartzIntegralL2Root244 b)))
  have hBound : Tendsto (fun n =>
      K * (schwartzIntegralL2Root244 (A n - a) *
        schwartzIntegralL2Root244 (B n)) +
      K * (schwartzIntegralL2Root244 a *
        schwartzIntegralL2Root244 (B n - b)) +
      δ n * (schwartzIntegralL2Root244 a *
        schwartzIntegralL2Root244 b)) atTop (𝓝 0) := by
    simpa only [zero_add] using (hFirst.add hSecond).add hThird
  have hDeltaNonneg (n : ℕ) : 0 ≤ δ n := by
    have h := hDiffC n 0
    exact le_trans (abs_nonneg _) h
  have hAbs : Tendsto (fun n =>
      |schwartzTripleIntegral244 (A n) (B n) (C n) -
        schwartzTripleIntegral244 a b c|) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      show |schwartzTripleIntegral244 (A n) (B n) (C n) -
          schwartzTripleIntegral244 a b c| ≤
        K * (schwartzIntegralL2Root244 (A n - a) *
          schwartzIntegralL2Root244 (B n)) +
        K * (schwartzIntegralL2Root244 a *
          schwartzIntegralL2Root244 (B n - b)) +
        δ n * (schwartzIntegralL2Root244 a *
          schwartzIntegralL2Root244 b)
      have hTerm1 := schwartzTripleIntegral_abs_le_L2L2Linf244
        (A n - a) (B n) (C n) K hK (hC n)
      have hTerm2 := schwartzTripleIntegral_abs_le_L2L2Linf244
        a (B n - b) (C n) K hK (hC n)
      have hTerm3 := schwartzTripleIntegral_abs_le_L2L2Linf244
        a b (C n - c) (δ n) (hDeltaNonneg n) (hDiffC n)
      rw [schwartzTripleIntegral_telescoping244]
      calc
        |schwartzTripleIntegral244 (A n - a) (B n) (C n) +
          schwartzTripleIntegral244 a (B n - b) (C n) +
          schwartzTripleIntegral244 a b (C n - c)| ≤
            (|schwartzTripleIntegral244 (A n - a) (B n) (C n)| +
             |schwartzTripleIntegral244 a (B n - b) (C n)|) +
             |schwartzTripleIntegral244 a b (C n - c)| := by
               exact (abs_add_le _ _).trans
                 (add_le_add (abs_add_le _ _) (le_refl _))
        _ ≤ _ := by linarith only [hTerm1, hTerm2, hTerm3]
    · exact hBound
  have hIntegral : Tendsto (fun n =>
      schwartzTripleIntegral244 (A n) (B n) (C n)) atTop
      (𝓝 (schwartzTripleIntegral244 a b c)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using hAbs
  change Tendsto
    (fun n => 2 * schwartzTripleIntegral244 (A n) (B n) (C n))
    atTop (𝓝 (2 * schwartzTripleIntegral244 a b c))
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
    atTop (𝓝 2)).mul hIntegral

private abbrev l2GradientFirst244 (f : A3 → SchwartzMap V3 ℝ)
    (j r : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection r} (f j)

private abbrev l2GradientThird244 (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))
/-- All four real gradient transport triples use only the two third-jet
L² difference roots and first-jet uniform convergence in each slot. -/
def SchwartzFullGradientL2L2LinfJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ j i k l r : A3,
    SchwartzGradientTripleL2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) r i k l)
      (fun n => l2GradientFirst244 (f n) j r)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g r i k l)
      (l2GradientFirst244 g j r) ∧
    SchwartzGradientTripleL2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) j i k r)
      (fun n => l2GradientFirst244 (f n) r l)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g j i k r)
      (l2GradientFirst244 g r l) ∧
    SchwartzGradientTripleL2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) j i r l)
      (fun n => l2GradientFirst244 (f n) r k)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g j i r l)
      (l2GradientFirst244 g r k) ∧
    SchwartzGradientTripleL2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) j r k l)
      (fun n => l2GradientFirst244 (f n) r i)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g j r k l)
      (l2GradientFirst244 g r i)
private theorem l2Gradient_finiteSum_tendsto244
    {J : Type*} [Fintype J]
    (F : ℕ → J → ℝ) (G : J → ℝ)
    (h : ∀ p : J, Tendsto (fun n => F n p) atTop (𝓝 (G p))) :
    Tendsto (fun n => ∑ p : J, F n p) atTop (𝓝 (∑ p : J, G p)) := by
  classical
  have hs (S : Finset J) :
      Tendsto (fun n => Finset.sum S (F n)) atTop
        (𝓝 (Finset.sum S G)) := by
    induction S using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert p S hp ih =>
        simpa only [Finset.sum_insert hp] using (h p).add ih
  exact hs (Finset.univ : Finset J)

private theorem l2Gradient_fivefold_tendsto244
    (F : ℕ → A3 → A3 → A3 → A3 → A3 → ℝ)
    (G : A3 → A3 → A3 → A3 → A3 → ℝ)
    (h : ∀ j i k l r : A3,
      Tendsto (fun n => F n j i k l r) atTop (𝓝 (G j i k l r))) :
    Tendsto (fun n => ∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∑ l : A3, ∑ r : A3, F n j i k l r) atTop
      (𝓝 (∑ j : A3, ∑ i : A3, ∑ k : A3,
        ∑ l : A3, ∑ r : A3, G j i k l r)) := by
  have hR (j i k l : A3) :=
    l2Gradient_finiteSum_tendsto244
      (fun n r => F n j i k l r) (fun r => G j i k l r)
      (fun r => h j i k l r)
  have hL (j i k : A3) :=
    l2Gradient_finiteSum_tendsto244
      (fun n l => ∑ r : A3, F n j i k l r)
      (fun l => ∑ r : A3, G j i k l r) (hR j i k)
  have hK (j i : A3) :=
    l2Gradient_finiteSum_tendsto244
      (fun n k => ∑ l : A3, ∑ r : A3, F n j i k l r)
      (fun k => ∑ l : A3, ∑ r : A3, G j i k l r) (hL j i)
  have hI (j : A3) :=
    l2Gradient_finiteSum_tendsto244
      (fun n i => ∑ k : A3, ∑ l : A3, ∑ r : A3, F n j i k l r)
      (fun i => ∑ k : A3, ∑ l : A3, ∑ r : A3, G j i k l r) (hK j)
  exact l2Gradient_finiteSum_tendsto244
    (fun n j => ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      F n j i k l r)
    (fun j => ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      G j i k l r) hI

/-- All 12 gradient channels and 243 five-axis slots converge from
natural two-two-infinity jet data. No third derivative L⁴ convergence is used. -/
theorem fullSchwartzGradientTransport_tendsto_of_L2L2LinfJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzFullGradientL2L2LinfJets244 f g) :
    Tendsto (fun n => fullSchwartzGradientTransport244 (f n)) atTop
      (𝓝 (fullSchwartzGradientTransport244 g)) := by
  have hAxis (j i k l r : A3) :
      Tendsto (fun n => fullSchwartzGradientAxis244 (f n) j i k l r)
        atTop (𝓝 (fullSchwartzGradientAxis244 g j i k l r)) := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hJets j i k l r
    have hTerm1 := fullGradientTriple_tendsto_of_L2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) r i k l)
      (fun n => l2GradientFirst244 (f n) j r)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g r i k l)
      (l2GradientFirst244 g j r) h₁
    have hTerm2 := fullGradientTriple_tendsto_of_L2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) j i k r)
      (fun n => l2GradientFirst244 (f n) r l)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g j i k r)
      (l2GradientFirst244 g r l) h₂
    have hTerm3 := fullGradientTriple_tendsto_of_L2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) j i r l)
      (fun n => l2GradientFirst244 (f n) r k)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g j i r l)
      (l2GradientFirst244 g r k) h₃
    have hTerm4 := fullGradientTriple_tendsto_of_L2L2LinfJets244
      (fun n => l2GradientThird244 (f n) j i k l)
      (fun n => l2GradientThird244 (f n) j r k l)
      (fun n => l2GradientFirst244 (f n) r i)
      (l2GradientThird244 g j i k l)
      (l2GradientThird244 g j r k l)
      (l2GradientFirst244 g r i) h₄
    change Tendsto (fun n =>
      fullGradientTriple244 (l2GradientThird244 (f n) j i k l) (l2GradientThird244 (f n) r i k l) (l2GradientFirst244 (f n) j r) +
      fullGradientTriple244 (l2GradientThird244 (f n) j i k l) (l2GradientThird244 (f n) j i k r) (l2GradientFirst244 (f n) r l) +
      fullGradientTriple244 (l2GradientThird244 (f n) j i k l) (l2GradientThird244 (f n) j i r l) (l2GradientFirst244 (f n) r k) +
      fullGradientTriple244 (l2GradientThird244 (f n) j i k l) (l2GradientThird244 (f n) j r k l) (l2GradientFirst244 (f n) r i)) atTop
      (𝓝 (fullGradientTriple244 (l2GradientThird244 g j i k l) (l2GradientThird244 g r i k l) (l2GradientFirst244 g j r) +
        fullGradientTriple244 (l2GradientThird244 g j i k l) (l2GradientThird244 g j i k r) (l2GradientFirst244 g r l) +
        fullGradientTriple244 (l2GradientThird244 g j i k l) (l2GradientThird244 g j i r l) (l2GradientFirst244 g r k) +
        fullGradientTriple244 (l2GradientThird244 g j i k l) (l2GradientThird244 g j r k l) (l2GradientFirst244 g r i)))
    exact ((hTerm1.add hTerm2).add hTerm3).add hTerm4
  change Tendsto (fun n => ∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∑ l : A3, ∑ r : A3, fullSchwartzGradientAxis244 (f n) j i k l r)
    atTop (𝓝 (∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∑ l : A3, ∑ r : A3, fullSchwartzGradientAxis244 g j i k l r))
  exact l2Gradient_fivefold_tendsto244
    (fun n j i k l r => fullSchwartzGradientAxis244 (f n) j i k l r)
    (fun j i k l r => fullSchwartzGradientAxis244 g j i k l r) hAxis
/-- Derive the previous split-jet observable bridge with only L²
third derivatives and uniform convergence of first derivatives. -/
structure H3FullThirdSchwartzNaturalGradientApproximation244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ) : Prop where
  monomialJets : SchwartzStrongJetConvergence244 f g
  gradientJets : SchwartzFullGradientL2L2LinfJets244 f g
  physical : fullSchwartzGradientTransport244 g +
      3 * lowNormalRealSchwartzPoint3Monomial g =
    velocityH3TransportDerivative3At u t
  energy0 : Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
    (𝓝 (velocityH3Energy0At u t))
  energy1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
    (𝓝 (velocityH3Energy1At u t))
  energy2 : Tendsto (fun n => lowNormalRealSchwartzH3Energy2 (f n)) atTop
    (𝓝 (velocityH3Energy2At u t))
  energy3 : Tendsto (fun n => lowNormalRealSchwartzH3Energy3 (f n)) atTop
    (𝓝 (velocityH3Energy3At u t))
  top : Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
    (𝓝 (velocityH3Dissipation3At u t))

/-- The full signed transport limit follows from proven 3–3–1 continuity,
not from an assumed convergence of its entire nonlinear integral. -/
theorem H3FullThirdSchwartzNaturalGradientApproximation244.toSplitJet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    (h : H3FullThirdSchwartzNaturalGradientApproximation244 u t f g) :
    H3FullThirdSchwartzSplitJetApproximation244 u t f g :=
  { jets := h.monomialJets
    gradient := fullSchwartzGradientTransport_tendsto_of_L2L2LinfJets244
      f g h.gradientJets
    physical := h.physical
    energy0 := h.energy0
    energy1 := h.energy1
    energy2 := h.energy2
    energy3 := h.energy3
    top := h.top }

/-- The previous five-observable closure is now discharged by natural
third-jet L² and first-jet L∞ difference control. -/
theorem H3FullThirdSchwartzNaturalGradientApproximation244.toObservable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    (h : H3FullThirdSchwartzNaturalGradientApproximation244 u t f g) :
    H3FullThirdSchwartzObservableApproximation244 u t f :=
  h.toSplitJet.toObservable

/-- No arbitrary physical slice is claimed to have the above density data. -/
def H3FullThirdSchwartzNaturalGradientApproximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : Prop :=
  ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
    ∃ g : A3 → SchwartzMap V3 ℝ,
      H3FullThirdSchwartzNaturalGradientApproximation244 u t f g

/-- The new natural-gradient density contract suffices for the old
five-observable approximation premise. -/
theorem h3Path_naturalGradient_implies_observableApproximable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    (h : H3FullThirdSchwartzNaturalGradientApproximable244 u t) :
    H3FullThirdSchwartzObservableApproximable244 u t := by
  obtain ⟨f, g, hf⟩ := h
  exact ⟨f, hf.toObservable⟩

/-- Conditional nonextension obstruction using the natural-gradient jet
interface, without postulating convergence of the full signed cubic. -/
theorem h3Path_noExtension_naturalGradientSignedWitness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      H3FullThirdSchwartzNaturalGradientApproximable244 u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        H3FullThirdSchwartzObservableApproximation244 u t f ∧
        ∃ n : ℕ,
          M * lowNormalRealSchwartzH3Energy (f n) +
            lowNormalRealSchwartzH3FullDissipation244 (f n) <
          -fullSchwartzThirdCommutator244 (f n) := by
  exact h3Path_noExtension_fullThirdApproxSignedWitness244
    hH3 hNoExtension hClass hb hd hM
    (fun t ht => h3Path_naturalGradient_implies_observableApproximable244
      (hTail t ht))

/-- Conditional H³ continuation from a uniform signed-cubic envelope
verified on natural-gradient Schwartz approximants on a strict tail. -/
theorem h3Path_extension_of_naturalGradientSignedEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hB : 0 ≤ B)
    (hTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        ∃ g : A3 → SchwartzMap V3 ℝ,
          H3FullThirdSchwartzNaturalGradientApproximation244 u t f g ∧
          (∀ᶠ n : ℕ in atTop,
            -fullSchwartzThirdCommutator244 (f n) ≤
              B * lowNormalRealSchwartzH3Energy (f n) +
                lowNormalRealSchwartzH3FullDissipation244 (f n))) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3Path_extension_of_fullThirdApproxSignedEnvelope244
    hH3 hClass hb hd hB
  intro t ht
  obtain ⟨f, g, h, hBound⟩ := hTail t ht
  exact ⟨f, h.toObservable, hBound⟩

end
end PrimeTensor.FirstMonomialTriad
