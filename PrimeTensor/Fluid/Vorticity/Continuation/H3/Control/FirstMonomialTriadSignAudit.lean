import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadGlobalBound

/-!
# Exact sign audit of the complete six-order triad coefficient

All six assignments of the three frequencies are included. A comparable
three-dimensional incompressible triad has either imaginary sign. This
is an algebraic statement about the symbol, not a Schwartz-field or PDE
counterexample.
-/

namespace PrimeTensor.FirstMonomialTriad

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- One ordered contribution with three independent polarizations. -/
def orderedTriadCoefficient (p q r : ι → ℝ) (a b c : ι → ℂ) : ℂ :=
  complexCoefficient p q r b * amplitudeDot a c

/-- All six frequency assignments, each with its corresponding polarization. -/
def sixOrderTriadCoefficient (p q r : ι → ℝ) (a b c : ι → ℂ) : ℂ :=
  orderedTriadCoefficient p q r a b c + orderedTriadCoefficient p r q a c b +
  orderedTriadCoefficient q p r b a c + orderedTriadCoefficient q r p b c a +
  orderedTriadCoefficient r p q c a b + orderedTriadCoefficient r q p c b a

/-- Pairing the six assignments recovers three shell terms exactly. -/
theorem sixOrderTriadCoefficient_eq_shells
    (p q r : ι → ℝ) (a b c : ι → ℂ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (ha : mixedDot p a = 0) (hb : mixedDot q b = 0) (hc : mixedDot r c = 0) :
    sixOrderTriadCoefficient p q r a b c =
      complexShellCoefficient p q r b * amplitudeDot a c +
      complexShellCoefficient p r q c * amplitudeDot a b +
      complexShellCoefficient q p r a * amplitudeDot b c := by
  have hprq : ∀ i, p i + r i + q i = 0 := by
    intro i
    linarith [hMomentum i]
  have hqpr : ∀ i, q i + p i + r i = 0 := by
    intro i
    linarith [hMomentum i]
  rw [← complex_exchanged_coefficient p q r b hMomentum hb,
    ← complex_exchanged_coefficient p r q c hprq hc,
    ← complex_exchanged_coefficient q p r a hqpr ha]
  simp only [sixOrderTriadCoefficient, orderedTriadCoefficient,
    amplitudeDot_comm c a, amplitudeDot_comm b a, amplitudeDot_comm c b]
  ring

/-- Fixed frequencies have squared radii 1, 2 and 5. -/
def signAuditP : Fin 3 → ℝ := ![1, 0, 0]
def signAuditQ : Fin 3 → ℝ := ![1, 1, 0]
def signAuditR : Fin 3 → ℝ := ![-2, -1, 0]

/-- Two polarizations are perpendicular to the frequency plane. -/
def signAuditA : Fin 3 → ℂ := ![0, 0, 1]

/-- The middle polarization is tangent to its incompressibility plane. -/
def signAuditB (τ : ℝ) : Fin 3 → ℂ := ![-(τ : ℂ) * Complex.I, (τ : ℂ) * Complex.I, 0]

theorem signAudit_momentum : ∀ i, signAuditP i + signAuditQ i + signAuditR i = 0 := by
  intro i
  fin_cases i <;> norm_num [signAuditP, signAuditQ, signAuditR]

theorem signAudit_squared_radii :
    dot signAuditP signAuditP = 1 ∧ dot signAuditQ signAuditQ = 2 ∧
      dot signAuditR signAuditR = 5 := by
  norm_num [dot, signAuditP, signAuditQ, signAuditR, Fin.sum_univ_succ]

theorem signAudit_incompressible (τ : ℝ) :
    mixedDot signAuditP signAuditA = 0 ∧
      mixedDot signAuditQ (signAuditB τ) = 0 ∧ mixedDot signAuditR signAuditA = 0 := by
  norm_num [mixedDot, signAuditP, signAuditQ, signAuditR, signAuditA, signAuditB,
    Fin.sum_univ_succ] <;> ring

/-- The full six-order coefficient is nonzero and linear in the chosen phase. -/
theorem signAudit_sixOrder (τ : ℝ) :
    sixOrderTriadCoefficient signAuditP signAuditQ signAuditR
      signAuditA (signAuditB τ) signAuditA = 16 * (τ : ℂ) * Complex.I := by
  norm_num [sixOrderTriadCoefficient, orderedTriadCoefficient, complexCoefficient,
    dot, mixedDot, amplitudeDot, signAuditP, signAuditQ, signAuditR,
    signAuditA, signAuditB, Fin.sum_univ_succ] <;> ring

theorem signAudit_positive :
    (sixOrderTriadCoefficient signAuditP signAuditQ signAuditR
      signAuditA (signAuditB 1) signAuditA).im = 16 := by
  rw [signAudit_sixOrder]
  norm_num

theorem signAudit_negative :
    (sixOrderTriadCoefficient signAuditP signAuditQ signAuditR
      signAuditA (signAuditB (-1)) signAuditA).im = -16 := by
  rw [signAudit_sixOrder]
  norm_num

/-- Reflecting every frequency and conjugating this explicit polarization
configuration retains the same imaginary coefficient. Thus the opposite
frequency triad does not cancel it by the real-field symmetry alone. -/
theorem signAudit_reflected_sixOrder (τ : ℝ) :
    sixOrderTriadCoefficient (fun i => -signAuditP i) (fun i => -signAuditQ i)
      (fun i => -signAuditR i) signAuditA (signAuditB (-τ)) signAuditA =
      16 * (τ : ℂ) * Complex.I := by
  norm_num [sixOrderTriadCoefficient, orderedTriadCoefficient, complexCoefficient,
    dot, mixedDot, amplitudeDot, signAuditP, signAuditQ, signAuditR,
    signAuditA, signAuditB, Fin.sum_univ_succ] <;> ring

end
end PrimeTensor.FirstMonomialTriad
