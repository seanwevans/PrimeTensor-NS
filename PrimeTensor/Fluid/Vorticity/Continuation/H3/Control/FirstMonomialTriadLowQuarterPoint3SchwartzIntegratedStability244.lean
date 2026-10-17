import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSlotwiseStability244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderNormIdentities244
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrated L² × L⁴ × L⁴ stability of the actual signed 243-slot monomial

The previous theorem proved a pointwise trilinear telescoping identity and a
finite-index stability estimate, but did not control the spatial integrals of
those three differences. Here all six fields are genuine real Schwartz maps
on the actual three-dimensional Euclidean carrier.

For Schwartz triples (a,b,c) and (a',b',c'), exact linearity of the integral,
followed by the already-proved real 2-4-4 Holder theorem, gives

 |∫abc - ∫a'b'c'| ≤ ‖a-a'‖₂‖b‖₄‖c‖₄
                    + ‖a'‖₂‖b-b'‖₄‖c‖₄
                    + ‖a'‖₂‖b'‖₄‖c-c'‖₄.

The nonnegative norms are the *actual roots* of the corresponding square and
fourth-power integrals, not formal norm inputs. We then sum this estimate over
all 243 physical slots and preserve the pairing factor two.

This is unconditional for any TWO Schwartz fields. An extension to a general
H³ path still requires Schwartz jet approximation in L²/L⁴ and identification
of the limit with each physical spatial pairing. Neither is silently assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3
private abbrev SlotsIntegrated244 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeIntegrated244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact, nonnegative physical real L² norm of a Schwartz scalar. -/
noncomputable def schwartzIntegralL2Root244 (f : SchwartzMap V3 ℝ) : ℝ :=
  Real.sqrt (∫ x : V3, (f x) ^ 2)

/-- The exact, nonnegative physical real L⁴ norm of a Schwartz scalar. -/
noncomputable def schwartzIntegralL4Root244 (f : SchwartzMap V3 ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (∫ x : V3, (f x) ^ 4))

theorem schwartzIntegralL2Root244_nonneg (f : SchwartzMap V3 ℝ) :
    0 ≤ schwartzIntegralL2Root244 f := Real.sqrt_nonneg _

theorem schwartzIntegralL4Root244_nonneg (f : SchwartzMap V3 ℝ) :
    0 ≤ schwartzIntegralL4Root244 f := Real.sqrt_nonneg _

/-- One actual scalar Schwartz triple product, without pairing factor two. -/
noncomputable def schwartzTripleIntegral244
    (a b c : SchwartzMap V3 ℝ) : ℝ :=
  ∫ x : V3, a x * (b x * c x)

private theorem schwartzTripleIntegrable244
    (a b c : SchwartzMap V3 ℝ) :
    Integrable (fun x : V3 => a x * (b x * c x)) :=
  (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) b c)).integrable

/-- Real 2-4-4 Holder for three arbitrary real Schwartz functions, with
no additional norm-identification or positivity hypotheses. -/
theorem schwartzTripleIntegral_abs_le_roots244
    (a b c : SchwartzMap V3 ℝ) :
    |schwartzTripleIntegral244 a b c| ≤
      schwartzIntegralL2Root244 a *
        (schwartzIntegralL4Root244 b * schwartzIntegralL4Root244 c) := by
  have hHolder := enorm_integral_three_mul_le_244 (volume : Measure V3)
    (a.continuous.aemeasurable.enorm)
    (b.continuous.aemeasurable.enorm)
    (c.continuous.aemeasurable.enorm)
  change ‖schwartzTripleIntegral244 a b c‖ₑ ≤
    realLpEnorm volume 2 (a : V3 → ℝ) *
      (realLpEnorm volume 4 (b : V3 → ℝ) *
        realLpEnorm volume 4 (c : V3 → ℝ)) at hHolder
  rw [lowNormalSchwartz_realLpEnorm_two_eq_actualRoot244 a,
    lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244 b,
    lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244 c] at hHolder
  have ha := schwartzIntegralL2Root244_nonneg a
  have hb := schwartzIntegralL4Root244_nonneg b
  have hc := schwartzIntegralL4Root244_nonneg c
  have hProduct :
      0 ≤ schwartzIntegralL2Root244 a *
        (schwartzIntegralL4Root244 b * schwartzIntegralL4Root244 c) :=
    mul_nonneg ha (mul_nonneg hb hc)
  have hPacked :
      ENNReal.ofReal (schwartzIntegralL2Root244 a *
        (schwartzIntegralL4Root244 b * schwartzIntegralL4Root244 c)) =
      ENNReal.ofReal (schwartzIntegralL2Root244 a) *
        (ENNReal.ofReal (schwartzIntegralL4Root244 b) *
          ENNReal.ofReal (schwartzIntegralL4Root244 c)) := by
    rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  have hReal :
      ENNReal.ofReal |schwartzTripleIntegral244 a b c| ≤
        ENNReal.ofReal (schwartzIntegralL2Root244 a *
          (schwartzIntegralL4Root244 b * schwartzIntegralL4Root244 c)) := by
    calc
      ENNReal.ofReal |schwartzTripleIntegral244 a b c| =
          ‖schwartzTripleIntegral244 a b c‖ₑ := by
        simpa only [Real.norm_eq_abs] using
          (ofReal_norm (schwartzTripleIntegral244 a b c))
      _ ≤ _ := by rw [hPacked]; exact hHolder
  exact (ENNReal.ofReal_le_ofReal_iff hProduct).mp hReal

/-- The spatial *integrals* of three perturbed products telescope exactly.
The integral identities are valid because all products of Schwartz factors
are integrable, including the three difference products. -/
theorem schwartzTripleIntegral_telescoping244
    (a b c a' b' c' : SchwartzMap V3 ℝ) :
    schwartzTripleIntegral244 a b c -
      schwartzTripleIntegral244 a' b' c' =
      schwartzTripleIntegral244 (a - a') b c +
        schwartzTripleIntegral244 a' (b - b') c +
          schwartzTripleIntegral244 a' b' (c - c') := by
  have hA := schwartzTripleIntegrable244 a b c
  have hB := schwartzTripleIntegrable244 a' b' c'
  have hX := schwartzTripleIntegrable244 (a - a') b c
  have hY := schwartzTripleIntegrable244 a' (b - b') c
  have hZ := schwartzTripleIntegrable244 a' b' (c - c')
  unfold schwartzTripleIntegral244
  calc
    (∫ x : V3, a x * (b x * c x)) -
        (∫ x : V3, a' x * (b' x * c' x)) =
      ∫ x : V3, a x * (b x * c x) - a' x * (b' x * c' x) :=
        (integral_sub hA hB).symm
    _ = ∫ x : V3,
        (a - a') x * (b x * c x) +
          a' x * ((b - b') x * c x) +
            a' x * (b' x * (c - c') x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [sub_apply]
      ring
    _ = (∫ x : V3, (a - a') x * (b x * c x)) +
          (∫ x : V3, a' x * ((b - b') x * c x)) +
            (∫ x : V3, a' x * (b' x * (c - c') x)) := by
      calc
        _ = (∫ x : V3,
            (a - a') x * (b x * c x) +
              a' x * ((b - b') x * c x)) +
              (∫ x : V3, a' x * (b' x * (c - c') x)) :=
          integral_add (hX.add hY) hZ
        _ = _ := by rw [integral_add hX hY]

/-- Coefficient-one integrated perturbation inequality in ordinary reals.
The third term uses the ORIGINAL second factor `b'`, as required by exact
trilinear telescoping; none of the six fields is assumed nonnegative. -/
theorem schwartzTripleIntegral_difference_le244
    (a b c a' b' c' : SchwartzMap V3 ℝ) :
    |schwartzTripleIntegral244 a b c -
      schwartzTripleIntegral244 a' b' c'| ≤
      schwartzIntegralL2Root244 (a - a') *
        (schwartzIntegralL4Root244 b * schwartzIntegralL4Root244 c) +
      schwartzIntegralL2Root244 a' *
        (schwartzIntegralL4Root244 (b - b') * schwartzIntegralL4Root244 c) +
      schwartzIntegralL2Root244 a' *
        (schwartzIntegralL4Root244 b' * schwartzIntegralL4Root244 (c - c')) := by
  rw [schwartzTripleIntegral_telescoping244]
  calc
    |schwartzTripleIntegral244 (a - a') b c +
      schwartzTripleIntegral244 a' (b - b') c +
      schwartzTripleIntegral244 a' b' (c - c')| ≤
      (|schwartzTripleIntegral244 (a - a') b c| +
        |schwartzTripleIntegral244 a' (b - b') c|) +
        |schwartzTripleIntegral244 a' b' (c - c')| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ _ := by
      exact add_le_add
        (add_le_add
          (schwartzTripleIntegral_abs_le_roots244 (a - a') b c)
          (schwartzTripleIntegral_abs_le_roots244 a' (b - b') c))
        (schwartzTripleIntegral_abs_le_roots244 a' b' (c - c'))

/-- The complete five-axis product index set; each of the 243 ordered
physical velocity/derivative slots appears once. -/
private abbrev physicalThird244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SlotsIntegrated244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2)))

private abbrev physicalMiddle244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SlotsIntegrated244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.2.1}
    (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1))

private abbrev physicalCross244 (f : A3 → SchwartzMap V3 ℝ)
    (p : SlotsIntegrated244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2))

/-- One nonnegative error envelope, with exactly three spatial 2-4-4
products, attached to each actual physical slot. -/
noncomputable def schwartzPhysicalSlotPerturbation244
    (f g : A3 → SchwartzMap V3 ℝ) (p : SlotsIntegrated244) : ℝ :=
  schwartzIntegralL2Root244 (physicalThird244 f p - physicalThird244 g p) *
    (schwartzIntegralL4Root244 (physicalMiddle244 f p) *
      schwartzIntegralL4Root244 (physicalCross244 f p)) +
  schwartzIntegralL2Root244 (physicalThird244 g p) *
    (schwartzIntegralL4Root244 (physicalMiddle244 f p - physicalMiddle244 g p) *
      schwartzIntegralL4Root244 (physicalCross244 f p)) +
  schwartzIntegralL2Root244 (physicalThird244 g p) *
    (schwartzIntegralL4Root244 (physicalMiddle244 g p) *
      schwartzIntegralL4Root244 (physicalCross244 f p - physicalCross244 g p))

/-- The full 243-slot signed physical monomial is quantitatively stable
in the *actual* L² × L⁴ × L⁴ derivative norms. No sign cancellation, slot
selection or extra multiplicity is used. The physical pairing factor two
is the only prefactor. -/
theorem lowNormalRealSchwartz_fullMonomial_integratedStability244
    (f g : A3 → SchwartzMap V3 ℝ) :
    |lowNormalRealSchwartzPoint3Monomial f -
      lowNormalRealSchwartzPoint3Monomial g| ≤
      2 * (∑ p : SlotsIntegrated244,
        schwartzPhysicalSlotPerturbation244 f g p) := by
  classical
  have hReorder (v : A3 → SchwartzMap V3 ℝ) :
      lowNormalRealSchwartzPoint3Monomial v =
        2 * (∑ p : SlotsIntegrated244,
          schwartzTripleIntegral244
            (physicalThird244 v p) (physicalMiddle244 v p)
            (physicalCross244 v p)) := by
    rw [lowNormalRealSchwartz_firstMonomial_eq_twice_slotSum]
    congr 1
    simp only [SlotsIntegrated244, Fintype.sum_prod_type]
    rfl
  rw [hReorder f, hReorder g]
  have hFinite :
      |(∑ p : SlotsIntegrated244,
        schwartzTripleIntegral244
          (physicalThird244 f p) (physicalMiddle244 f p)
          (physicalCross244 f p)) -
        (∑ p : SlotsIntegrated244,
          schwartzTripleIntegral244
            (physicalThird244 g p) (physicalMiddle244 g p)
            (physicalCross244 g p))| ≤
        ∑ p : SlotsIntegrated244,
          schwartzPhysicalSlotPerturbation244 f g p := by
    calc
      _ = |∑ p : SlotsIntegrated244,
        (schwartzTripleIntegral244
            (physicalThird244 f p) (physicalMiddle244 f p)
            (physicalCross244 f p) -
          schwartzTripleIntegral244
            (physicalThird244 g p) (physicalMiddle244 g p)
            (physicalCross244 g p))| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ p : SlotsIntegrated244,
          |schwartzTripleIntegral244
            (physicalThird244 f p) (physicalMiddle244 f p)
            (physicalCross244 f p) -
           schwartzTripleIntegral244
            (physicalThird244 g p) (physicalMiddle244 g p)
            (physicalCross244 g p)| := by
        simpa only [Real.norm_eq_abs] using
          (norm_sum_le (Finset.univ : Finset SlotsIntegrated244)
            (fun p => schwartzTripleIntegral244
                (physicalThird244 f p) (physicalMiddle244 f p)
                (physicalCross244 f p) -
              schwartzTripleIntegral244
                (physicalThird244 g p) (physicalMiddle244 g p)
                (physicalCross244 g p)))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        exact schwartzTripleIntegral_difference_le244
          (physicalThird244 f p) (physicalMiddle244 f p)
          (physicalCross244 f p)
          (physicalThird244 g p) (physicalMiddle244 g p)
          (physicalCross244 g p)
  calc
    |2 * (∑ p : SlotsIntegrated244,
      schwartzTripleIntegral244
        (physicalThird244 f p) (physicalMiddle244 f p)
        (physicalCross244 f p)) -
     2 * (∑ p : SlotsIntegrated244,
      schwartzTripleIntegral244
        (physicalThird244 g p) (physicalMiddle244 g p)
        (physicalCross244 g p))| =
      2 * |(∑ p : SlotsIntegrated244,
        schwartzTripleIntegral244
          (physicalThird244 f p) (physicalMiddle244 f p)
          (physicalCross244 f p)) -
       (∑ p : SlotsIntegrated244,
        schwartzTripleIntegral244
          (physicalThird244 g p) (physicalMiddle244 g p)
          (physicalCross244 g p))| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (∑ p : SlotsIntegrated244,
      schwartzPhysicalSlotPerturbation244 f g p) :=
      mul_le_mul_of_nonneg_left hFinite (by norm_num)

end
end PrimeTensor.FirstMonomialTriad
