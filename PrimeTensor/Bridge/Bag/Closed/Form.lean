import PrimeTensor.Bridge.Bag.Semantics

/-!
# Closed form for ordered-bag semantic targets

`Bridge.BagSemantics` proved convergence to recursive real targets that mirror
the native prime-bag stream recursion exactly.

This file normalizes those recursive targets to the expected logarithmic closed
form.  The proof is split through a bridge-only additive coordinate:

    bagLog one = 0
    bagLog (factor p rest) = log p + bagLog rest

Then:

* `bagLog b = log (b.eval)`;
* coupling one prime against a bag is
  `exp (log p * bagLog b)`;
* coupling two bags is
  `exp (bagLog a * bagLog b)`;
* hence the recursive target is exactly
  `exp (log (a.eval) * log (b.eval))`.

All additive and logarithmic machinery remains confined to the bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairStreamSeed

/-- Conventional additive log-coordinate of an ordered positive prime bag. -/
noncomputable def bagLog : PrimeBag → ℝ
  | .one =>
      0
  | .factor p rest =>
      Real.log (p.value : ℝ) +
        bagLog rest

@[simp] theorem bagLog_one :
    bagLog .one = 0 := by
  rfl

@[simp] theorem bagLog_factor
    (p : Prime)
    (rest : PrimeBag) :
    bagLog (.factor p rest) =
      Real.log (p.value : ℝ) +
        bagLog rest := by
  rfl

/-- Every prime value remains nonzero after casting into the conventional reals. -/
private theorem prime_value_cast_ne_zero
    (p : Prime) :
    (p.value : ℝ) ≠ 0 := by

  have hpNat : p.value ≠ 0 :=
    Nat.ne_of_gt
      (lt_trans Nat.zero_lt_one p.one_lt)

  exact_mod_cast hpNat

/-- Every positive prime bag evaluates to a nonzero conventional real. -/
private theorem bag_eval_cast_ne_zero
    (b : PrimeBag) :
    (b.eval : ℝ) ≠ 0 := by

  have hbNat : b.eval ≠ 0 :=
    Nat.ne_of_gt
      (lt_of_lt_of_le
        Nat.zero_lt_one
        (PrimeBag.one_le_eval b))

  exact_mod_cast hbNat

/--
The recursive additive coordinate is exactly the conventional logarithm of the
bag's represented natural magnitude.
-/
theorem bagLog_eq_log_eval :
    ∀ b : PrimeBag,
      bagLog b =
        Real.log (b.eval : ℝ)
  | .one => by
      simp only [
        bagLog_one,
        PrimeBag.eval_one,
        Nat.cast_one,
        Real.log_one
      ]

  | .factor p rest => by

      rw [
        bagLog_factor,
        bagLog_eq_log_eval rest
      ]

      have hp :
          (p.value : ℝ) ≠ 0 :=
        prime_value_cast_ne_zero p

      have hr :
          (rest.eval : ℝ) ≠ 0 :=
        bag_eval_cast_ne_zero rest

      rw [← Real.log_mul hp hr]

      congr 1

      simp only [
        PrimeBag.eval_factor,
        Nat.cast_mul
      ]

/--
The recursive one-prime-against-bag target is exponential multiplication in
the bag's additive log-coordinate.
-/
theorem primeAgainstBagTarget_eq_exp_bagLog
    (p : Prime) :
    ∀ b : PrimeBag,
      primeAgainstBagTarget p b =
        Real.exp
          (
            Real.log (p.value : ℝ) *
              bagLog b
          )
  | .one => by

      simp only [
        primeAgainstBagTarget_one,
        bagLog_one,
        mul_zero,
        Real.exp_zero
      ]

  | .factor q rest => by

      rw [
        primeAgainstBagTarget_factor,
        primeAgainstBagTarget_eq_exp_bagLog
          p rest
      ]

      unfold logProductTarget

      rw [← Real.exp_add]

      congr 1

      rw [bagLog_factor, mul_add]

/--
The full recursive bag-pair target is exponential multiplication of the two
additive bag coordinates.
-/
theorem bagPairTarget_eq_exp_bagLog :
    ∀ a b : PrimeBag,
      bagPairTarget a b =
        Real.exp
          (
            bagLog a *
              bagLog b
          )
  | .one, b => by

      simp only [
        bagPairTarget_one_left,
        bagLog_one,
        zero_mul,
        Real.exp_zero
      ]

  | .factor p rest, b => by

      rw [
        bagPairTarget_factor_left,
        primeAgainstBagTarget_eq_exp_bagLog
          p b,
        bagPairTarget_eq_exp_bagLog
          rest b
      ]

      rw [← Real.exp_add]

      congr 1

      rw [bagLog_factor, add_mul]

/--
Closed form for the ordered-bag semantic coupling target.
-/
theorem bagPairTarget_eq_logProduct
    (a b : PrimeBag) :
    bagPairTarget a b =
      Real.exp
        (
          Real.log (a.eval : ℝ) *
            Real.log (b.eval : ℝ)
        ) := by

  rw [
    bagPairTarget_eq_exp_bagLog,
    bagLog_eq_log_eval,
    bagLog_eq_log_eval
  ]

end PrimePairStreamSeed

namespace PrimePairApprox

/--
The concrete dyadic bag-pair stream converges to the expected closed logarithmic
product target.
-/
theorem bagPair_convergesReal_logProduct
    (a b : PrimeBag) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (kernel.bagPair a b)
      (
        Real.exp
          (
            Real.log (a.eval : ℝ) *
              Real.log (b.eval : ℝ)
          )
      ) := by

  rw [
    ← PrimeTensor.Bridge.PrimePairStreamSeed.bagPairTarget_eq_logProduct
        a b
  ]

  exact bagPair_convergesReal a b

end PrimePairApprox

end Bridge
end PrimeTensor
