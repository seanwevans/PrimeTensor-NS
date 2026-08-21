import PrimeTensor.Tensor.Calculus

/-!
# Conventional rational bridge

Ordinary rationals occur only here. They are semantic projections of finite
prime barcodes, never stored coefficients in the multiplicative tensor layer.
-/

namespace PrimeTensor
namespace Bridge

/-- Conventional rational interpretation of a finite oriented prime barcode. -/
def PrimeRatio.toRat (q : PrimeRatio) : ℚ :=
  (q.upper.eval : ℚ) / (q.lower.eval : ℚ)

/-- Every quotient-level prime multiset still represents a magnitude at least `1`. -/
private theorem multiset_one_le_eval (q : PrimeMultiset) : 1 ≤ q.eval := by
  refine Quotient.inductionOn q ?_
  intro b
  exact PrimeBag.one_le_eval b

private theorem multiset_eval_ne_zero (q : PrimeMultiset) : (q.eval : ℚ) ≠ 0 := by
  have h : 1 ≤ q.eval := multiset_one_le_eval q
  have hn : q.eval ≠ 0 := Nat.one_le_iff_ne_zero.mp h
  exact_mod_cast hn

private theorem upper_ne_zero (q : PrimeRatio) : (q.upper.eval : ℚ) ≠ 0 :=
  multiset_eval_ne_zero q.upper

private theorem lower_ne_zero (q : PrimeRatio) : (q.lower.eval : ℚ) ≠ 0 :=
  multiset_eval_ne_zero q.lower

@[simp] theorem toRat_one : PrimeRatio.toRat 1 = 1 := by
  change ((PrimeMultiset.eval (1 : PrimeMultiset) : ℚ) /
    (PrimeMultiset.eval (1 : PrimeMultiset) : ℚ)) = 1
  rw [PrimeMultiset.eval_one]
  norm_num

/-- Barcode multiplication projects to ordinary rational multiplication. -/
theorem toRat_mul (a b : PrimeRatio) :
    PrimeRatio.toRat (a * b) = PrimeRatio.toRat a * PrimeRatio.toRat b := by
  simp only [PrimeRatio.toRat, PrimeRatio.upper_mul, PrimeRatio.lower_mul,
    Nat.cast_mul]
  field_simp [lower_ne_zero a, lower_ne_zero b]

/-- Barcode inversion projects to ordinary rational inversion. -/
theorem toRat_inv (a : PrimeRatio) :
    PrimeRatio.toRat a⁻¹ = (PrimeRatio.toRat a)⁻¹ := by
  simp only [PrimeRatio.toRat, PrimeRatio.inv_upper, PrimeRatio.inv_lower]
  field_simp [upper_ne_zero a, lower_ne_zero a]

/-- Evaluation commutes with a nonempty axis product. -/
theorem fold_toRat : ∀ (d : Depth) (f : Axis d → PrimeRatio),
    PrimeRatio.toRat (Axis.fold (· * ·) d f) =
      Axis.fold (· * ·) d (fun i => PrimeRatio.toRat (f i))
  | .one, f => rfl
  | .succ d, f => by
      change PrimeRatio.toRat
          (f .first * Axis.fold (· * ·) d (fun i => f (.next i))) =
        PrimeRatio.toRat (f .first) *
          Axis.fold (· * ·) d (fun i => PrimeRatio.toRat (f (.next i)))
      rw [toRat_mul, fold_toRat d]

/-- The first tensor bridge: evaluation commutes with multiplicative contraction. -/
theorem contract₂_toRat {dim : Depth} (m : Tensor.Matrix PrimeRatio dim) :
    PrimeRatio.toRat (Tensor.contract₂ m) =
      Axis.fold (· * ·) dim (fun i => PrimeRatio.toRat (m.component (i, i))) := by
  exact fold_toRat dim (fun i => m.component (i, i))

end Bridge
end PrimeTensor
