import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandAnalyticWienerPersistence
import Mathlib.Tactic

/-!
# Analytic Wiener weights and finite-mode kinetic dissipation

The previous persistence argument has a remaining infinite-dimensional
Fourier-PDE bridge. This module proves the all-degree rational Wiener
estimates, a finite-support ordered-kernel sum bound, and a uniform kinetic
viscosity ceiling for EVERY finite frequency set. These estimates do not
truncate the nonlinear PDE, and their constants do not depend on the set.

If the real unforced PDE solution obeys the shrinking-radius Wiener bound,
then its normalized total viscous kinetic charge over a persistence interval
is at most 160000*mu*T, whereas the lower outward nonlinear kinetic transfer
is greater than 19/10*T. Consequently, the ratio of actual viscosity payment
to persistent forward transfer can be arbitrarily small when mu tends to
zero. Persistence of two forward fluxes ALONE cannot force a uniform positive
viscous payment.

The scalar ratio theorem has explicit hypotheses on the integrated actual
transfer and viscosity charge. It does not assert the unformalized PDE bridge,
construct a Fourier solution, or resolve H3 continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Uniform exponential envelopes for every integer Fourier ℓ¹ degree.
The first one is the elementary embedding W_(3/2) ⊂ W_(5/4); the
other two control one and two frequency derivatives in W_(5/4). -/
theorem thirdFullThreeBand_allDegreeWienerEnvelopes244 (n : ℕ) :
    (5 / 4 : ℝ) ^ n ≤ (3 / 2 : ℝ) ^ n ∧
    (n : ℝ) * (5 / 4 : ℝ) ^ n ≤ 5 * (3 / 2 : ℝ) ^ n ∧
    (n : ℝ) ^ 2 * (5 / 4 : ℝ) ^ n ≤ 100 * (3 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hb : 0 ≤ (3 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) n
    constructor
    · simp only [pow_succ]
      nlinarith
    constructor
    · simp only [pow_succ, Nat.cast_succ]
      nlinarith
    · simp only [pow_succ, Nat.cast_succ]
      nlinarith

/-- Every integer frequency degree is absorbed by one analytic Wiener weight. -/
theorem thirdFullThreeBand_degreeAbsorbedByWiener244 (n : ℕ) :
    (n : ℝ) ≤ 4 * (5 / 4 : ℝ) ^ n := by
  have hbase : ∀ m : ℕ, (1 : ℝ) ≤ (5 / 4 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      nlinarith
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp := hbase n
    simp only [pow_succ, Nat.cast_succ]
    nlinarith

/-- A uniform finite-mode square-of-sum inequality; no frequency cutoff
or cardinality appears in the bound. -/
theorem thirdFullThreeBand_finiteSquares_le_squareSum244
    {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ s, (f a) ^ 2) ≤ (∑ a ∈ s, f a) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa : 0 ≤ f a := hf a
    have hs : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg (by
      intro i hi
      exact hf i)
    have hcross : 0 ≤ f a * (∑ i ∈ s, f i) :=
      mul_nonneg hfa hs
    simp only [Finset.sum_insert ha]
    nlinarith [ih, hcross]

/-- The exact full *ordered* pair sum is bounded by the product of the
corresponding two weighted sums. This is the finite algebraic core of the
Wiener estimate for the complete quadratic Leray convolution. -/
theorem thirdFullThreeBand_finiteOrderedKernelBound244
    {α : Type*} (s : Finset α) (F G : α → ℝ)
    (K : α → α → ℝ)
    (hK : ∀ p ∈ s, ∀ q ∈ s, K p q ≤ F p * G q) :
    (∑ p ∈ s, ∑ q ∈ s, K p q) ≤
      (∑ p ∈ s, F p) * (∑ q ∈ s, G q) := by
  classical
  calc
    _ ≤ ∑ p ∈ s, ∑ q ∈ s, F p * G q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact hK p hp q hq
    _ = (∑ p ∈ s, F p) * (∑ q ∈ s, G q) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- Universal finite-mode kinetic gradient bound from a W_(5/4) ball:
for EVERY finite frequency set, sum m(n)^2 |u_n|^2 ≤ 16*M^2.
Here `degree` is the integer ℓ¹ frequency degree and `amp` denotes
nonnegative Euclidean Fourier amplitude. No cardinality dependence occurs. -/
theorem thirdFullThreeBand_finiteWienerKineticCeiling244
    {α : Type*} (s : Finset α)
    (degree : α → ℕ) (amp : α → ℝ)
    (hamp : ∀ a, 0 ≤ amp a)
    (hW : (∑ a ∈ s, (5 / 4 : ℝ) ^ (degree a) * amp a) ≤ 100) :
    (∑ a ∈ s, ((degree a : ℝ) * amp a) ^ 2) ≤ 160000 := by
  classical
  have hd : (∑ a ∈ s, (degree a : ℝ) * amp a) ≤
      4 * (∑ a ∈ s, (5 / 4 : ℝ) ^ (degree a) * amp a) := by
    calc
      _ ≤ ∑ a ∈ s, 4 * ((5 / 4 : ℝ) ^ (degree a) * amp a) := by
        apply Finset.sum_le_sum
        intro a ha
        have h := thirdFullThreeBand_degreeAbsorbedByWiener244 (degree a)
        calc
          (degree a : ℝ) * amp a ≤
              (4 * (5 / 4 : ℝ) ^ (degree a)) * amp a :=
                mul_le_mul_of_nonneg_right h (hamp a)
          _ = 4 * ((5 / 4 : ℝ) ^ (degree a) * amp a) := by ring
      _ = _ := by rw [Finset.mul_sum]
  have hf : ∀ a, 0 ≤ (degree a : ℝ) * amp a := by
    intro a
    exact mul_nonneg (Nat.cast_nonneg _) (hamp a)
  have hsq := thirdFullThreeBand_finiteSquares_le_squareSum244 s
    (fun a => (degree a : ℝ) * amp a) hf
  have hsum : 0 ≤ (∑ a ∈ s, (degree a : ℝ) * amp a) :=
    Finset.sum_nonneg (by intro a ha; exact hf a)
  have hcap : (∑ a ∈ s, (degree a : ℝ) * amp a) ≤ 400 := by
    have h := mul_le_mul_of_nonneg_left hW (by norm_num : (0:ℝ) ≤ 4)
    linarith
  have hprod : 0 ≤ (400 - (∑ a ∈ s, (degree a : ℝ) * amp a)) *
      (400 + (∑ a ∈ s, (degree a : ℝ) * amp a)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- A scalar viscous charge ceiling, designed for the normalized PDE
energy ledger once the (independently finite-mode) Wiener majorant applies. -/
theorem thirdFullThreeBand_viscousChargeFromGradientCap244
    (mu T energy charge : ℝ)
    (hmu : 0 ≤ mu) (hT : 0 ≤ T)
    (hEnergy : 0 ≤ energy ∧ energy ≤ 160000)
    (hCharge : charge ≤ mu * T * energy) :
    charge ≤ 160000 * mu * T := by
  have hmul : mu * T * energy ≤ mu * T * 160000 :=
    mul_le_mul_of_nonneg_left hEnergy.2 (mul_nonneg hmu hT)
  nlinarith

/-- Persistence of outward nonlinear transfer alone does not force a
viscosity-independent kinetic dissipation payment. Once the actual lower
flux transfers at least 19/10*T and the normalized total viscous loss obeys
the all-frequency Wiener ceiling, choosing mu ≤ ε/100000 makes the kinetic
loss at most ε times the transferred amount. -/
theorem thirdFullThreeBand_persistentTransfer_noUniformViscousCharge244
    (epsilon mu T charge transfer : ℝ)
    (heps : 0 ≤ epsilon) (hT : 0 ≤ T)
    (hmu : 0 ≤ mu)
    (hSmall : mu ≤ epsilon / 100000)
    (hCharge : charge ≤ 160000 * mu * T)
    (hTransfer : (19 / 10 : ℝ) * T ≤ transfer) :
    charge ≤ epsilon * transfer := by
  have hsmall : mu * T ≤ (epsilon / 100000) * T :=
    mul_le_mul_of_nonneg_right hSmall hT
  have htransfer : epsilon * ((19 / 10 : ℝ) * T) ≤
      epsilon * transfer := mul_le_mul_of_nonneg_left hTransfer heps
  have hbound : 160000 * mu * T ≤ (8 / 5 : ℝ) * epsilon * T := by
    nlinarith [hsmall]
  have hepsT : 0 ≤ epsilon * T := mul_nonneg heps hT
  nlinarith

/-- For every positive requested relative cost ε there is a strictly
positive normalized viscosity below both 1/10 and ε/100000. This makes
the no-uniform-charge conclusion nontrivial for Navier--Stokes, not only
for the inviscid Euler endpoint. -/
theorem thirdFullThreeBand_smallPositiveViscosityForCharge244
    (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ mu : ℝ, 0 < mu ∧ mu ≤ (1 / 10 : ℝ) ∧
      mu ≤ epsilon / 100000 := by
  refine ⟨min (1 / 20 : ℝ) (epsilon / 200000), ?_, ?_, ?_⟩
  · exact lt_min_iff.mpr ⟨by norm_num, div_pos heps (by norm_num)⟩
  · exact (min_le_left _ _).trans (by norm_num)
  · have h := min_le_right (1 / 20 : ℝ) (epsilon / 200000)
    linarith [le_of_lt heps]

end
end PrimeTensor.FirstMonomialTriad
