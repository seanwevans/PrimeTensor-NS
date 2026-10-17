import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzCauchyCompletion244

/-!
# Strong jet Cauchy control implies the signed 243-slot Cauchy criterion

The completed signed first monomial previously required the *integrated*
243-slot trilinear perturbation envelopes to vanish on a common tail. This
file derives those error estimates from the actual three difference norms:
third jets in real L² and both second jets in real L⁴.

One uniform finite K bounds all undifferenced jet roots of every approximant.
The proof uses the coefficient-one 2-4-4 perturbation estimate and a common
quantitative cutoff δ = ε / (3 K² + 1), without postulating convergence
of the nonlinear signed monomial. Thus the scalar monomial Cauchy property
and a unique real limit follow from strong jet Cauchy control.

Uniform root bounds and strong Cauchy control are explicit analytic inputs;
this does not prove Schwartz density for an arbitrary physical Sobolev slice,
nor identify the resulting real limit with a physical H³ transport pairing.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeUniformJet244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual third-derivative factor of one of the 243 physical slots. -/
private abbrev cauchyThird244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2)))

/-- The actual middle second-derivative factor. -/
private abbrev cauchyMiddle244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.2.1}
    (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1))

/-- The actual cross second-derivative factor. -/
private abbrev cauchyCross244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SchwartzStrongJetSlots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2))

/-- One common positive bound on the actual real jet-root norms of all
approximants, uniformly over the entire five-coordinate index set. -/
def Schwartz243UniformJetRoots244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ n : ℕ, ∀ p : SchwartzStrongJetSlots244,
    schwartzIntegralL2Root244 (cauchyThird244 (f n) p) ≤ K ∧
    schwartzIntegralL4Root244 (cauchyMiddle244 (f n) p) ≤ K ∧
    schwartzIntegralL4Root244 (cauchyCross244 (f n) p) ≤ K

/-- On every late index pair, all three strong differences in each ordered
physical slot become arbitrarily small with a common index for that slot. -/
def Schwartz243StrongJetCauchy244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ p : SchwartzStrongJetSlots244, ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
      schwartzIntegralL2Root244
        (cauchyThird244 (f m) p - cauchyThird244 (f n) p) < δ ∧
      schwartzIntegralL4Root244
        (cauchyMiddle244 (f m) p - cauchyMiddle244 (f n) p) < δ ∧
      schwartzIntegralL4Root244
        (cauchyCross244 (f m) p - cauchyCross244 (f n) p) < δ

/-- A difference factor bounded by δ and two nonnegative jet-root factors
bounded by K have product at most δK², even at zero norm. -/
private theorem two_root_factors_le244
    (K δ x r s : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hx : x ≤ δ)
    (hr : 0 ≤ r) (hrK : r ≤ K)
    (hs : 0 ≤ s) (hsK : s ≤ K) :
    x * (r * s) ≤ δ * (K * K) := by
  have hProduct : r * s ≤ K * K := by
    calc
      r * s ≤ K * s := mul_le_mul_of_nonneg_right hrK hs
      _ ≤ K * K := mul_le_mul_of_nonneg_left hsK hK
  calc
    x * (r * s) ≤ δ * (r * s) :=
      mul_le_mul_of_nonneg_right hx (mul_nonneg hr hs)
    _ ≤ δ * (K * K) := mul_le_mul_of_nonneg_left hProduct hδ

/-- Exactly three coefficient-one products constitute the real 2-4-4
perturbation envelope. Rearranging factors does not change their signs. -/
private theorem three_root_error_products_le244
    (K δ x y z a b c d : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hx : x ≤ δ) (hy : y ≤ δ) (hz : z ≤ δ)
    (ha : 0 ≤ a) (haK : a ≤ K)
    (hb : 0 ≤ b) (hbK : b ≤ K)
    (hc : 0 ≤ c) (hcK : c ≤ K)
    (hd : 0 ≤ d) (hdK : d ≤ K) :
    x * (a * b) + c * (y * b) + c * (d * z) ≤
      3 * (δ * (K * K)) := by
  have hFirst := two_root_factors_le244 K δ x a b
    hK hδ hx ha haK hb hbK
  have hSecond := two_root_factors_le244 K δ y c b
    hK hδ hy hc hcK hb hbK
  have hThird := two_root_factors_le244 K δ z c d
    hK hδ hz hc hcK hd hdK
  calc
    x * (a * b) + c * (y * b) + c * (d * z) =
        x * (a * b) + y * (c * b) + z * (c * d) := by ring
    _ ≤ δ * (K * K) + δ * (K * K) + δ * (K * K) :=
      add_le_add (add_le_add hFirst hSecond) hThird
    _ = 3 * (δ * (K * K)) := by ring

/-- The three actual strong Cauchy derivative differences make each
integrated 2-4-4 physical slot error uniformly Cauchy-small. The common
uniform root bound prevents an uncontrolled factor from amplifying a small
difference; no limit field in Schwartz space is assumed. -/
theorem schwartz243_slotErrors_of_uniformStrongJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) (K : ℝ)
    (hBound : Schwartz243UniformJetRoots244 f K)
    (hJets : Schwartz243StrongJetCauchy244 f) :
    Schwartz243SlotErrorCauchy244 f := by
  obtain ⟨hK, hRoots⟩ := hBound
  have hK0 : 0 ≤ K := le_trans (by norm_num : (0 : ℝ) ≤ 1) hK
  intro p ε hε
  let δ : ℝ := ε / (3 * (K * K) + 1)
  have hDen : 0 < 3 * (K * K) + 1 := by positivity
  have hδPos : 0 < δ := div_pos hε hDen
  have hδ : 0 ≤ δ := le_of_lt hδPos
  have hScale : 3 * (δ * (K * K)) < ε := by
    have hCancel : δ * (3 * (K * K) + 1) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (ne_of_gt hDen)
    nlinarith
  obtain ⟨N, hTail⟩ := hJets p δ hδPos
  refine ⟨N, ?_⟩
  intro m hm n hn
  obtain ⟨hxTail, hyTail, hzTail⟩ := hTail m hm n hn
  let x : ℝ := schwartzIntegralL2Root244
    (cauchyThird244 (f m) p - cauchyThird244 (f n) p)
  let y : ℝ := schwartzIntegralL4Root244
    (cauchyMiddle244 (f m) p - cauchyMiddle244 (f n) p)
  let z : ℝ := schwartzIntegralL4Root244
    (cauchyCross244 (f m) p - cauchyCross244 (f n) p)
  let a : ℝ := schwartzIntegralL4Root244 (cauchyMiddle244 (f m) p)
  let b : ℝ := schwartzIntegralL4Root244 (cauchyCross244 (f m) p)
  let c : ℝ := schwartzIntegralL2Root244 (cauchyThird244 (f n) p)
  let d : ℝ := schwartzIntegralL4Root244 (cauchyMiddle244 (f n) p)
  have hx : x ≤ δ := le_of_lt hxTail
  have hy : y ≤ δ := le_of_lt hyTail
  have hz : z ≤ δ := le_of_lt hzTail
  have ha : 0 ≤ a := schwartzIntegralL4Root244_nonneg _
  have hb : 0 ≤ b := schwartzIntegralL4Root244_nonneg _
  have hc : 0 ≤ c := schwartzIntegralL2Root244_nonneg _
  have hd : 0 ≤ d := schwartzIntegralL4Root244_nonneg _
  have haK : a ≤ K := (hRoots m p).2.1
  have hbK : b ≤ K := (hRoots m p).2.2
  have hcK : c ≤ K := (hRoots n p).1
  have hdK : d ≤ K := (hRoots n p).2.1
  have hError :
      schwartzPhysicalSlotPerturbation244 (f m) (f n) p =
        x * (a * b) + c * (y * b) + c * (d * z) := by
    rfl
  rw [hError]
  exact lt_of_le_of_lt
    (three_root_error_products_le244 K δ x y z a b c d
      hK0 hδ hx hy hz ha haK hb hbK hc hcK hd hdK)
    hScale

/-- The complete signed monomial becomes Cauchy under strong jet Cauchy
control plus a common finite bound on all relevant undifferenced roots. -/
theorem lowNormalRealSchwartz_firstMonomial_cauchy_of_uniformStrongJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) (K : ℝ)
    (hBound : Schwartz243UniformJetRoots244 f K)
    (hJets : Schwartz243StrongJetCauchy244 f) :
    CauchySeq (fun n => lowNormalRealSchwartzPoint3Monomial (f n)) :=
  lowNormalRealSchwartz_firstMonomial_cauchy_of_slotErrors244 f
    (schwartz243_slotErrors_of_uniformStrongJets244 f K hBound hJets)

/-- Reference-free existence of the completed signed real 243-slot monomial.
The strong Cauchy hypotheses are only jet norms, not trilinear integrals. -/
theorem lowNormalRealSchwartz_firstMonomial_existsLimit_of_uniformStrongJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ) (K : ℝ)
    (hBound : Schwartz243UniformJetRoots244 f K)
    (hJets : Schwartz243StrongJetCauchy244 f) :
    ∃ M : ℝ,
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n))
        atTop (𝓝 M) :=
  lowNormalRealSchwartz_firstMonomial_existsLimit_of_slotErrors244 f
    (schwartz243_slotErrors_of_uniformStrongJets244 f K hBound hJets)

end
end PrimeTensor.FirstMonomialTriad
