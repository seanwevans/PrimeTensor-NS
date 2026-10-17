import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FixedKineticFullH3Obstruction244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationMonomial
import Mathlib.Tactic

/-!
# Exact physical Schwartz gradient block and concentration sign frontier

The third-order Navier--Stokes commutator separates into twelve D³u · Du
contributions and nine D²u · D²u contributions for each triple of spatial
indices. Previous fixed-kinetic concentration results treated the resulting
signed first interpolation monomial M but did not compute the actual scaling
of the gradient block G.

This file builds G directly from the four real Schwartz 3+3+1 trilinear
integrals, summed over the original five physical axis indices. The physical
spatial energy pairing has factor TWO; it is retained in each term.

Both G and M have spatial homogeneity four, amplitude homogeneity three,
and coupled fixed-kinetic concentration homogeneity seventeen. Consequently
G+3M is a single cubic shape coefficient: concentration alone cannot show
that the gradient block cancels M, or that it fails to cancel M.

Under the explicitly stated condition G(f)+3M(f) != 0, velocity reversal
selects a positive sign and gives a genuine counterexample to uniform
full-third-commutator static absorption (with the entire normalized H³
energy on the right). Establishing that nonvanishing for the explicit
quarter packet, or proving a PDE-specific cancellation, is the new hard
analytical obligation. No Navier--Stokes path realization is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullGradient244 (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev firstJet244 (f : A3 → SchwartzMap V3 ℝ) (j r : A3) :
    SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection r} (f j)

private abbrev thirdJet244 (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- Real physical triple-product integral including the original factor two. -/
noncomputable def fullGradientTriple244 (F G H : SchwartzMap V3 ℝ) : ℝ :=
  2 * ∫ x : V3, F x * (G x * H x)

/-- Every 3+3+1 triple has seven spatial derivatives and one dimension-three
Jacobian. Thus the integral scales with spatial degree four. -/
theorem fullGradientTriple_dilation244
    (s : ℝ) (hs : 0 < s) (F G H : SchwartzMap V3 ℝ) :
    fullGradientTriple244
      (s ^ 3 • lowNormalSchwartzDilation s hs F)
      (s ^ 3 • lowNormalSchwartzDilation s hs G)
      (s • lowNormalSchwartzDilation s hs H) =
    s ^ 4 * fullGradientTriple244 F G H := by
  have hCoeff : s ^ 7 * (s ^ 3)⁻¹ = s ^ 4 := by
    field_simp [ne_of_gt hs]
  unfold fullGradientTriple244
  calc
    2 * (∫ x : V3,
      (s ^ 3 • lowNormalSchwartzDilation s hs F) x *
        ((s ^ 3 • lowNormalSchwartzDilation s hs G) x *
          (s • lowNormalSchwartzDilation s hs H) x)) =
      2 * (∫ x : V3,
        s ^ 7 * (F (s • x) * (G (s • x) * H (s • x)))) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          simp only [smul_apply, smul_eq_mul, lowNormalSchwartzDilation_apply]
          ring
    _ = 2 * (s ^ 7 * ∫ x : V3,
        F (s • x) * (G (s • x) * H (s • x))) := by
          rw [integral_const_mul]
    _ = 2 * (s ^ 7 * ((s ^ 3)⁻¹ *
        ∫ x : V3, F x * (G x * H x))) := by
          rw [lowNormalH3Fourier_integral_comp_positive_smul s hs
            (fun x : V3 => F x * (G x * H x))]
    _ = s ^ 4 * (2 * ∫ x : V3, F x * (G x * H x)) := by
          calc
            _ = 2 * ((s ^ 7 * (s ^ 3)⁻¹) *
                  ∫ x : V3, F x * (G x * H x)) := by ring
            _ = _ := by rw [hCoeff]; ring

/-- Every real triple product is exactly cubic under velocity amplitude. -/
theorem fullGradientTriple_real_smul244
    (a : ℝ) (F G H : SchwartzMap V3 ℝ) :
    fullGradientTriple244 (a • F) (a • G) (a • H) =
      a ^ 3 * fullGradientTriple244 F G H := by
  unfold fullGradientTriple244
  simp only [smul_apply, smul_eq_mul]
  have hTerm (x : V3) :
      (a * F x) * ((a * G x) * (a * H x)) =
        a ^ 3 * (F x * (G x * H x)) := by ring
  simp_rw [hTerm]
  rw [integral_const_mul]
  ring

private theorem firstJet244_dilation
    (s : ℝ) (hs : 0 < s) (f : A3 → SchwartzMap V3 ℝ)
    (j r : A3) :
    firstJet244 (lowNormalSchwartzVelocityDilation s hs f) j r =
      s • lowNormalSchwartzDilation s hs (firstJet244 f j r) :=
  lowNormalSchwartzDilation_lineDeriv s hs (h3FourierAxisDirection r) (f j)

private theorem thirdJet244_dilation
    (s : ℝ) (hs : 0 < s) (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) :
    thirdJet244 (lowNormalSchwartzVelocityDilation s hs f) j i k l =
      s ^ 3 • lowNormalSchwartzDilation s hs (thirdJet244 f j i k l) :=
  lowNormalSchwartzDilation_threeLineDerivs s hs
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (f j)

private theorem firstJet244_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) (j r : A3) :
    firstJet244 (fun q => a • f q) j r = a • firstJet244 f j r := by
  simp only [firstJet244, LineDeriv.lineDerivOp_smul]

private theorem thirdJet244_real_smul
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) (j i k l : A3) :
    thirdJet244 (fun q => a • f q) j i k l =
      a • thirdJet244 f j i k l := by
  simp only [thirdJet244, LineDeriv.lineDerivOp_smul]

/-- The four genuine D³u·Du terms of the PDE's gradient commutator for one
(j,i,k,l,r) tuple. Each of the four integrals includes the energy factor 2. -/
noncomputable def fullSchwartzGradientAxis244
    (f : A3 → SchwartzMap V3 ℝ) (j i k l r : A3) : ℝ :=
  fullGradientTriple244
    (thirdJet244 f j i k l) (thirdJet244 f r i k l) (firstJet244 f j r) +
  fullGradientTriple244
    (thirdJet244 f j i k l) (thirdJet244 f j i k r) (firstJet244 f r l) +
  fullGradientTriple244
    (thirdJet244 f j i k l) (thirdJet244 f j i r l) (firstJet244 f r k) +
  fullGradientTriple244
    (thirdJet244 f j i k l) (thirdJet244 f j r k l) (firstJet244 f r i)

/-- Exact spatial homogeneity of one four-term gradient axis block. -/
theorem fullSchwartzGradientAxis_dilation244
    (s : ℝ) (hs : 0 < s) (f : A3 → SchwartzMap V3 ℝ)
    (j i k l r : A3) :
    fullSchwartzGradientAxis244
      (lowNormalSchwartzVelocityDilation s hs f) j i k l r =
      s ^ 4 * fullSchwartzGradientAxis244 f j i k l r := by
  unfold fullSchwartzGradientAxis244
  simp only [thirdJet244_dilation, firstJet244_dilation]
  rw [fullGradientTriple_dilation244, fullGradientTriple_dilation244,
    fullGradientTriple_dilation244, fullGradientTriple_dilation244]
  ring

/-- Cubic homogeneity of one gradient axis block, including its signs. -/
theorem fullSchwartzGradientAxis_real_smul244
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) (j i k l r : A3) :
    fullSchwartzGradientAxis244 (fun q => a • f q) j i k l r =
      a ^ 3 * fullSchwartzGradientAxis244 f j i k l r := by
  unfold fullSchwartzGradientAxis244
  simp only [thirdJet244_real_smul, firstJet244_real_smul]
  rw [fullGradientTriple_real_smul244, fullGradientTriple_real_smul244,
    fullGradientTriple_real_smul244, fullGradientTriple_real_smul244]
  ring

/-- The complete 12-term gradient block: three velocity directions for each
third-order multi-index and velocity component. All five real-axis sums remain. -/
noncomputable def fullSchwartzGradientTransport244
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    fullSchwartzGradientAxis244 f j i k l r

/-- Exact spatial degree four of the complete 12-term gradient block. -/
theorem fullSchwartzGradientTransport_dilation244
    (s : ℝ) (hs : 0 < s) (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzGradientTransport244
      (lowNormalSchwartzVelocityDilation s hs f) =
      s ^ 4 * fullSchwartzGradientTransport244 f := by
  unfold fullSchwartzGradientTransport244
  simp_rw [fullSchwartzGradientAxis_dilation244 s hs f]
  simp only [← Finset.mul_sum]

/-- Exact velocity-amplitude degree three of the complete gradient block. -/
theorem fullSchwartzGradientTransport_real_smul244
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzGradientTransport244 (fun q => a • f q) =
      a ^ 3 * fullSchwartzGradientTransport244 f := by
  unfold fullSchwartzGradientTransport244
  simp_rw [fullSchwartzGradientAxis_real_smul244 a f]
  simp only [← Finset.mul_sum]

/-- The fully expanded physical third-order commutator shape coefficient.
The interpolation multiplicity THREE is the project's proved cyclic identity.
This is the Schwartz *spatial expression*, not a claimed path-time identity. -/
noncomputable def fullSchwartzThirdCommutator244
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  fullSchwartzGradientTransport244 f + 3 * lowNormalRealSchwartzPoint3Monomial f

/-- G and M have equal spatial homogeneity, including every physical slot. -/
theorem fullSchwartzThirdCommutator_dilation244
    (s : ℝ) (hs : 0 < s) (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzThirdCommutator244
      (lowNormalSchwartzVelocityDilation s hs f) =
      s ^ 4 * fullSchwartzThirdCommutator244 f := by
  unfold fullSchwartzThirdCommutator244
  rw [fullSchwartzGradientTransport_dilation244,
    lowNormalRealSchwartzPoint3Monomial_dilation]
  ring

/-- Both gradient and interpolation blocks are genuine odd cubic forms. -/
theorem fullSchwartzThirdCommutator_real_smul244
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzThirdCommutator244 (fun q => a • f q) =
      a ^ 3 * fullSchwartzThirdCommutator244 f := by
  unfold fullSchwartzThirdCommutator244
  rw [fullSchwartzGradientTransport_real_smul244,
    lowNormalRealSchwartzPoint3Monomial_real_smul]
  ring

/-- The full gradient block and the complete signed third commutator have
EXACTLY the same fixed-kinetic exponent as the positive first monomial. -/
theorem fixedKineticSchwartzConcentration_gradient_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzGradientTransport244
      (fixedKineticSchwartzConcentration244 t ht f) =
      t ^ 17 * fullSchwartzGradientTransport244 f := by
  unfold fixedKineticSchwartzConcentration244
  rw [fullSchwartzGradientTransport_real_smul244,
    fullSchwartzGradientTransport_dilation244]
  ring

/-- The complete third commutator cannot be separated from its gradient
channel by a fixed-kinetic concentration argument alone. -/
theorem fixedKineticSchwartzConcentration_fullThird_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzThirdCommutator244
      (fixedKineticSchwartzConcentration244 t ht f) =
      t ^ 17 * fullSchwartzThirdCommutator244 f := by
  unfold fullSchwartzThirdCommutator244
  rw [fixedKineticSchwartzConcentration_gradient_eq244,
    fixedKineticSchwartzConcentration_monomial_eq244]
  ring

/-- Under exact velocity reversal, the *whole* signed third commutator
changes sign. A nonzero coefficient therefore always has an adverse sign
for one of the two physically solenoidal velocity orientations. -/
theorem fullSchwartzThirdCommutator_oriented_positive244
    (f : A3 → SchwartzMap V3 ℝ)
    (hNonzero : fullSchwartzThirdCommutator244 f ≠ 0) :
    0 < fullSchwartzThirdCommutator244 f ∨
      0 < fullSchwartzThirdCommutator244 (fun j => (-1 : ℝ) • f j) := by
  by_cases hPos : 0 < fullSchwartzThirdCommutator244 f
  · exact Or.inl hPos
  · right
    have hLe : fullSchwartzThirdCommutator244 f ≤ 0 := le_of_not_gt hPos
    have hNeg : fullSchwartzThirdCommutator244 f < 0 :=
      lt_of_le_of_ne hLe hNonzero
    simpa only [fullSchwartzThirdCommutator_real_smul244,
      show ((-1 : ℝ) ^ 3) = -1 by norm_num,
      neg_one_mul, neg_pos] using hNeg

private theorem fullThird_scalar_absorption244
    (M D E0 E1 E2 E3 C K t : ℝ)
    (ht : 1 ≤ t)
    (hBudget : |C * D| +
      |K| * (1 + |E0| + |E1| + |E2| + |E3|) < t * M) :
    C * (t ^ 16 * D) +
      K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) <
        t ^ 17 * M := by
  have h16 : 1 ≤ t ^ 16 := one_le_pow₀ ht
  have hpos : 0 < t ^ 16 := lt_of_lt_of_le zero_lt_one h16
  have h4 : t ^ 4 ≤ t ^ 16 :=
    pow_le_pow_right₀ ht (by norm_num : (4 : ℕ) ≤ 16)
  have h8 : t ^ 8 ≤ t ^ 16 :=
    pow_le_pow_right₀ ht (by norm_num : (8 : ℕ) ≤ 16)
  have h12 : t ^ 12 ≤ t ^ 16 :=
    pow_le_pow_right₀ ht (by norm_num : (12 : ℕ) ≤ 16)
  have h0 : (t : ℝ) ^ 0 ≤ t ^ 16 := by simpa only [pow_zero] using h16
  have hTerm (p : ℕ) (E : ℝ) (hp : t ^ p ≤ t ^ 16) :
      K * (t ^ p * E) ≤ t ^ 16 * (|K| * |E|) := by
    calc
      K * (t ^ p * E) = t ^ p * (K * E) := by ring
      _ ≤ t ^ p * |K * E| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg (le_trans zero_le_one ht) _)
      _ = t ^ p * (|K| * |E|) := by rw [abs_mul]
      _ ≤ t ^ 16 * (|K| * |E|) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hC : C * (t ^ 16 * D) ≤ t ^ 16 * |C * D| := by
    calc
      C * (t ^ 16 * D) = t ^ 16 * (C * D) := by ring
      _ ≤ t ^ 16 * |C * D| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (le_trans zero_le_one h16)
  have hK : K ≤ t ^ 16 * |K| := by
    calc
      K ≤ |K| := le_abs_self _
      _ = 1 * |K| := by ring
      _ ≤ t ^ 16 * |K| := mul_le_mul_of_nonneg_right h16 (abs_nonneg _)
  have hE0 : K * E0 ≤ t ^ 16 * (|K| * |E0|) := by
    simpa only [pow_zero, one_mul] using hTerm 0 E0 h0
  have hE1 := hTerm 4 E1 h4
  have hE2 := hTerm 8 E2 h8
  have hE3 := hTerm 12 E3 h12
  have hMajor :
      C * (t ^ 16 * D) +
          K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) ≤
        t ^ 16 * (|C * D| +
          |K| * (1 + |E0| + |E1| + |E2| + |E3|)) := by
    calc
      _ = C * (t ^ 16 * D) + K + K * E0 + K * (t ^ 4 * E1) +
          K * (t ^ 8 * E2) + K * (t ^ 12 * E3) := by ring
      _ ≤ t ^ 16 * |C * D| + t ^ 16 * |K| +
          t ^ 16 * (|K| * |E0|) + t ^ 16 * (|K| * |E1|) +
          t ^ 16 * (|K| * |E2|) + t ^ 16 * (|K| * |E3|) := by
        linarith only [hC, hK, hE0, hE1, hE2, hE3]
      _ = _ := by ring
  calc
    _ ≤ t ^ 16 * (|C * D| +
          |K| * (1 + |E0| + |E1| + |E2| + |E3|)) := hMajor
    _ < t ^ 16 * (t * M) := mul_lt_mul_of_pos_left hBudget hpos
    _ = t ^ 17 * M := by ring


theorem fixedKineticSchwartzConcentration_exceeds_fullThird_absorption244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : 0 < fullSchwartzThirdCommutator244 f)
    (C K : ℝ) :
    ∃ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g ∧
      lowNormalRealSchwartzH3Energy0 g = lowNormalRealSchwartzH3Energy0 f ∧
      0 < fullSchwartzThirdCommutator244 g ∧
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy g <
          fullSchwartzThirdCommutator244 g := by
  let M : ℝ := fullSchwartzThirdCommutator244 f
  let D : ℝ := lowNormalRealSchwartzH3TopDissipation f
  let E0 : ℝ := lowNormalRealSchwartzH3Energy0 f
  let E1 : ℝ := lowNormalRealSchwartzH3Energy1 f
  let E2 : ℝ := lowNormalRealSchwartzH3Energy2 f
  let E3 : ℝ := lowNormalRealSchwartzH3Energy3 f
  have hMpos : 0 < M := hM
  let A : ℝ := |C * D| + |K| * (1 + |E0| + |E1| + |E2| + |E3|)
  let t : ℝ := (A + 1) / M + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have htOne : 1 ≤ t := by
    dsimp [t]
    have hnonneg : 0 ≤ (A + 1) / M :=
      div_nonneg (add_nonneg hA (by norm_num)) hMpos.le
    linarith
  have hBudget : A < t * M := by
    dsimp [t]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hMpos), one_mul]
    linarith only [hMpos]
  have hScalar :
      C * (t ^ 16 * D) +
        K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) <
          t ^ 17 * M := by
    apply fullThird_scalar_absorption244 M D E0 E1 E2 E3 C K t htOne
    exact hBudget
  let g : A3 → SchwartzMap V3 ℝ := fixedKineticSchwartzConcentration244 t ht f
  have hSol : lowNormalRealSchwartz_Point3Solenoidal g :=
    fixedKineticSchwartzConcentration_solenoidal244 t ht f hDiv
  have hMass : lowNormalRealSchwartzH3Energy0 g = E0 :=
    fixedKineticSchwartzConcentration_energy0_eq244 t ht f
  have hTop : lowNormalRealSchwartzH3TopDissipation g = t ^ 16 * D :=
    fixedKineticSchwartzConcentration_dissipation_eq244 t ht f
  have hMon : fullSchwartzThirdCommutator244 g = t ^ 17 * M :=
    fixedKineticSchwartzConcentration_fullThird_eq244 t ht f
  have hFull : lowNormalRealSchwartzH3Energy g =
      1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3 :=
    fixedKineticSchwartzConcentration_fullEnergy_eq244 t ht f
  have hAbsorb :
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy g <
          fullSchwartzThirdCommutator244 g := by
    calc
      _ = C * (t ^ 16 * D) +
            K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) := by
        rw [hTop, hFull]
      _ < t ^ 17 * M := hScalar
      _ = fullSchwartzThirdCommutator244 g := hMon.symm
  have hPositive : 0 < fullSchwartzThirdCommutator244 g := by
    rw [hMon]
    exact mul_pos (pow_pos ht 17) hMpos
  exact ⟨g, hSol, hMass, hPositive, hAbsorb⟩



/-- Any solenoidal Schwartz profile with nonzero *complete* third commutator
has one velocity orientation at which concentration defeats every fixed
coefficient static full-H³ absorption estimate. This makes the exact remaining
mathematical target explicit: exhibit even one solenoidal Schwartz profile
with G + 3M ≠ 0, or prove a cancellation identity ruling that out. -/
theorem fullSchwartzThirdCommutator_nonzero_forces_static_obstruction244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hNonzero : fullSchwartzThirdCommutator244 f ≠ 0)
    (C K : ℝ) :
    ∃ seed g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal seed ∧
      lowNormalRealSchwartz_Point3Solenoidal g ∧
      lowNormalRealSchwartzH3Energy0 g = lowNormalRealSchwartzH3Energy0 seed ∧
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy g <
          fullSchwartzThirdCommutator244 g := by
  rcases fullSchwartzThirdCommutator_oriented_positive244 f hNonzero with
    hPositive | hNegative
  · obtain ⟨g, hgDiv, hgE0, _, hgUpper⟩ :=
      fixedKineticSchwartzConcentration_exceeds_fullThird_absorption244
        f hDiv hPositive C K
    exact ⟨f, g, hDiv, hgDiv, hgE0, hgUpper⟩
  · let seed : A3 → SchwartzMap V3 ℝ := fun j => (-1 : ℝ) • f j
    have hSeed : lowNormalRealSchwartz_Point3Solenoidal seed :=
      lowNormalRealSchwartz_Point3Solenoidal_real_smul (-1) f hDiv
    obtain ⟨g, hgDiv, hgE0, _, hgUpper⟩ :=
      fixedKineticSchwartzConcentration_exceeds_fullThird_absorption244
        seed hSeed hNegative C K
    exact ⟨seed, g, hSeed, hgDiv, hgE0, hgUpper⟩

end
end PrimeTensor.FirstMonomialTriad
