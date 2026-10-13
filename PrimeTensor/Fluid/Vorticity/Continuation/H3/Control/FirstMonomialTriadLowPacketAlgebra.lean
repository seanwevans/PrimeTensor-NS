import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowPolarizationGerm

/-!
# Reality-symmetric divergence-free assembly of the sharp low-normal packets

This is the algebraic packet assembly, prior to constructing the scalar
Schwartz cutoffs. The three center germs are normalized polynomial Leray
lifts, so no variable-frequency denominator occurs. Real scalar weights may
be localized independently at p, q, r. Adding the conjugate-reflected copy
makes their sum Hermitian: U(-ξ) = star (U ξ), while preserving ξ · U(ξ) = 0.

The cutoffs are arbitrary functions in this module; smooth compact supports,
pointwise positivity, and noncancellation of the resulting triad integral are
NOT asserted by these algebraic identities.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private theorem lowNormalMixedDot_add
    (ξ : Fin 3 → ℝ) (a b : Fin 3 → ℂ) :
    mixedDot ξ (fun d => a d + b d) = mixedDot ξ a + mixedDot ξ b := by
  simp [mixedDot, Fin.sum_univ_succ, mul_add]
  ring

private theorem lowNormalMixedDot_scalar
    (ξ : Fin 3 → ℝ) (s : ℂ) (a : Fin 3 → ℂ) :
    mixedDot ξ (fun d => s * a d) = s * mixedDot ξ a := by
  simp [mixedDot, Fin.sum_univ_succ]
  ring

private theorem lowNormalMixedDot_neg
    (ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ) :
    mixedDot (fun d => -ξ d) a = -mixedDot ξ a := by
  simp [mixedDot, Fin.sum_univ_succ]

private theorem lowNormalMixedDot_star
    (ξ : Fin 3 → ℝ) (a : Fin 3 → ℂ) :
    mixedDot ξ (fun d => star (a d)) = star (mixedDot ξ a) := by
  change mixedDot ξ (fun d => (starRingEnd ℂ) (a d)) =
    (starRingEnd ℂ) (mixedDot ξ a)
  simp [mixedDot, Fin.sum_univ_succ, map_add, map_mul, Complex.conj_ofReal]

/-- Real scalar localization preserves pointwise complex Fourier divergence. -/
def lowNormalScalarPacket
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (χ : (Fin 3 → ℝ) → ℝ)
    (ξ : Fin 3 → ℝ) (d : Fin 3) : ℂ :=
  (χ ξ : ℂ) * lowNormalNormalizedSolenoidalGerm η ξ a d

theorem lowNormalScalarPacket_divergence
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (χ : (Fin 3 → ℝ) → ℝ) (ξ : Fin 3 → ℝ) :
    mixedDot ξ (lowNormalScalarPacket η a χ ξ) = 0 := by
  calc
    _ = (χ ξ : ℂ) * mixedDot ξ (lowNormalNormalizedSolenoidalGerm η ξ a) := by
      exact lowNormalMixedDot_scalar ξ (χ ξ : ℂ)
        (lowNormalNormalizedSolenoidalGerm η ξ a)
    _ = 0 := by rw [lowNormalNormalizedSolenoidalGerm_divergence]; ring

theorem lowNormalScalarPacket_zero_of_cutoff_zero
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (χ : (Fin 3 → ℝ) → ℝ) (ξ : Fin 3 → ℝ)
    (hχ : χ ξ = 0) :
    lowNormalScalarPacket η a χ ξ = fun _ => 0 := by
  funext d
  simp [lowNormalScalarPacket, hχ]

/-- The positive-frequency half of the six-packet field. -/
def lowNormalPositiveThreePacketSum
    (t : ℝ)
    (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (ξ : Fin 3 → ℝ) (d : Fin 3) : ℂ :=
  (lowNormalScalarPacket lowNormalAuditP lowNormalAuditA χP ξ d +
    lowNormalScalarPacket (lowNormalAuditQ t) lowNormalAuditB χQ ξ d) +
    lowNormalScalarPacket (lowNormalAuditR t) lowNormalAuditC χR ξ d

theorem lowNormalPositiveThreePacketSum_divergence
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ) (ξ : Fin 3 → ℝ) :
    mixedDot ξ (lowNormalPositiveThreePacketSum t χP χQ χR ξ) = 0 := by
  change mixedDot ξ (fun d =>
      (lowNormalScalarPacket lowNormalAuditP lowNormalAuditA χP ξ d +
        lowNormalScalarPacket (lowNormalAuditQ t) lowNormalAuditB χQ ξ d) +
        lowNormalScalarPacket (lowNormalAuditR t) lowNormalAuditC χR ξ d) = 0
  rw [lowNormalMixedDot_add, lowNormalMixedDot_add]
  simp only [lowNormalScalarPacket_divergence, zero_add]

theorem lowNormalPositiveThreePacketSum_zero_of_cutoffs_zero
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ) (ξ : Fin 3 → ℝ)
    (hp : χP ξ = 0) (hq : χQ ξ = 0) (hr : χR ξ = 0) :
    lowNormalPositiveThreePacketSum t χP χQ χR ξ = fun _ => 0 := by
  funext d
  simp [lowNormalPositiveThreePacketSum, lowNormalScalarPacket, hp, hq, hr]

/-- Algebraic Hermitianization on a real frequency carrier. -/
def lowNormalHermitianize
    (G : (Fin 3 → ℝ) → (Fin 3 → ℂ))
    (ξ : Fin 3 → ℝ) (d : Fin 3) : ℂ :=
  G ξ d + star (G (fun k => -ξ k) d)

/-- The reality involution holds with no assumptions on G. -/
theorem lowNormalHermitianize_reality
    (G : (Fin 3 → ℝ) → (Fin 3 → ℂ)) (ξ : Fin 3 → ℝ) :
    lowNormalHermitianize G (fun k => -ξ k) =
      fun d => star (lowNormalHermitianize G ξ d) := by
  funext d
  simp [lowNormalHermitianize, star_add, add_comm]

/-- Hermitianization preserves pointwise incompressibility. The minus sign
from reflecting frequency is essential; conjugation alone is not sufficient. -/
theorem lowNormalHermitianize_divergence
    (G : (Fin 3 → ℝ) → (Fin 3 → ℂ))
    (hG : ∀ ξ, mixedDot ξ (G ξ) = 0)
    (ξ : Fin 3 → ℝ) :
    mixedDot ξ (lowNormalHermitianize G ξ) = 0 := by
  have hOpp : mixedDot ξ (G (fun k => -ξ k)) = 0 := by
    have h := hG (fun k => -ξ k)
    rw [lowNormalMixedDot_neg] at h
    exact neg_eq_zero.mp h
  have hRef : mixedDot ξ (fun d => star (G (fun k => -ξ k) d)) = 0 := by
    rw [lowNormalMixedDot_star, hOpp]
    simp
  change mixedDot ξ (fun d =>
    G ξ d + star (G (fun k => -ξ k) d)) = 0
  rw [lowNormalMixedDot_add, hG ξ, hRef]
  ring

/-- Fourier field consisting of the three localized sharp germs and their
three opposite-frequency complex-conjugated partners. -/
def lowNormalSixPacketFourier
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (ξ : Fin 3 → ℝ) : Fin 3 → ℂ :=
  lowNormalHermitianize (lowNormalPositiveThreePacketSum t χP χQ χR) ξ

theorem lowNormalSixPacketFourier_divergence
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ) (ξ : Fin 3 → ℝ) :
    mixedDot ξ (lowNormalSixPacketFourier t χP χQ χR ξ) = 0 :=
  lowNormalHermitianize_divergence _
    (lowNormalPositiveThreePacketSum_divergence t χP χQ χR) ξ

theorem lowNormalSixPacketFourier_reality
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ) (ξ : Fin 3 → ℝ) :
    lowNormalSixPacketFourier t χP χQ χR (fun k => -ξ k) =
      fun d => star (lowNormalSixPacketFourier t χP χQ χR ξ d) :=
  lowNormalHermitianize_reality _ ξ

/-- Vanishing of the three positive cutoffs at both ξ and -ξ forces the
full six-packet field to vanish at ξ. -/
theorem lowNormalSixPacketFourier_zero_of_cutoffs_zero
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ) (ξ : Fin 3 → ℝ)
    (hp : χP ξ = 0) (hq : χQ ξ = 0) (hr : χR ξ = 0)
    (hpn : χP (fun k => -ξ k) = 0)
    (hqn : χQ (fun k => -ξ k) = 0)
    (hrn : χR (fun k => -ξ k) = 0) :
    lowNormalSixPacketFourier t χP χQ χR ξ = fun _ => 0 := by
  have hPos := lowNormalPositiveThreePacketSum_zero_of_cutoffs_zero
    t χP χQ χR ξ hp hq hr
  have hNeg := lowNormalPositiveThreePacketSum_zero_of_cutoffs_zero
    t χP χQ χR (fun k => -ξ k) hpn hqn hrn
  funext d
  simp [lowNormalSixPacketFourier, lowNormalHermitianize, hPos, hNeg]

/-- A one-at-center scalar packet recovers the sharp positive p-polarization
provided the other two positive scalar packets vanish there. -/
theorem lowNormalPositiveThreePacketSum_at_P
    (t : ℝ) (ht : t ≠ 0)
    (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (hp : χP lowNormalAuditP = 1)
    (hq : χQ lowNormalAuditP = 0)
    (hr : χR lowNormalAuditP = 0) :
    lowNormalPositiveThreePacketSum t χP χQ χR lowNormalAuditP =
      lowNormalAuditA := by
  have hA := (lowNormalSharpPolarizationGerms_at_centers t ht).1
  funext d
  simp [lowNormalPositiveThreePacketSum, lowNormalScalarPacket,
    hp, hq, hr, hA]

/-- Analogous recovery at the small middle q-frequency. -/
theorem lowNormalPositiveThreePacketSum_at_Q
    (t : ℝ) (ht : t ≠ 0)
    (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (hp : χP (lowNormalAuditQ t) = 0)
    (hq : χQ (lowNormalAuditQ t) = 1)
    (hr : χR (lowNormalAuditQ t) = 0) :
    lowNormalPositiveThreePacketSum t χP χQ χR (lowNormalAuditQ t) =
      lowNormalAuditB := by
  have hB := (lowNormalSharpPolarizationGerms_at_centers t ht).2.1
  funext d
  simp [lowNormalPositiveThreePacketSum, lowNormalScalarPacket,
    hp, hq, hr, hB]

/-- Analogous recovery at the third r-frequency. -/
theorem lowNormalPositiveThreePacketSum_at_R
    (t : ℝ) (ht : t ≠ 0)
    (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (hp : χP (lowNormalAuditR t) = 0)
    (hq : χQ (lowNormalAuditR t) = 0)
    (hr : χR (lowNormalAuditR t) = 1) :
    lowNormalPositiveThreePacketSum t χP χQ χR (lowNormalAuditR t) =
      lowNormalAuditC := by
  have hC := (lowNormalSharpPolarizationGerms_at_centers t ht).2.2
  funext d
  simp [lowNormalPositiveThreePacketSum, lowNormalScalarPacket,
    hp, hq, hr, hC]

end
end PrimeTensor.FirstMonomialTriad
