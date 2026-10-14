import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowSmoothCutoff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

/-!
# The complete sharp low-normal six-packet Fourier Schwartz field

The smooth compact scalar cutoffs of `FirstMonomialTriadLowSmoothCutoff`
are multiplied by the normalized polynomial solenoidal germs.  Compact
support is inherited from the cutoffs, despite polynomial growth of the
germs; smoothness follows by differentiating their finite polynomial
components.  Conjugation and reflection preserve both properties.

The result is a *vector-valued Schwartz map* on exactly the finite real
Fourier carrier used by the sharp first-monomial symbol audit.  Its
pointwise Fourier divergence vanishes and it obeys Hermitian reality.

A nonzero *integral* of the signed nonlinear triad kernel remains to be
proved.  No Navier--Stokes singularity statement is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
open scoped Topology ContDiff SchwartzMap

noncomputable section

private theorem lowNormalComplexCoordinate_smooth (d : Fin 3) :
    ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ => (ξ d : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_apply ℝ ℝ d)

/-- The complexified real squared radius is a smooth polynomial. -/
theorem lowNormalComplexSquaredRadius_contDiff :
    ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ => lowNormalComplexSquaredRadius ξ) := by
  have h0 := (lowNormalComplexCoordinate_smooth 0).mul
    (lowNormalComplexCoordinate_smooth 0)
  have h1 := (lowNormalComplexCoordinate_smooth 1).mul
    (lowNormalComplexCoordinate_smooth 1)
  have h2 := (lowNormalComplexCoordinate_smooth 2).mul
    (lowNormalComplexCoordinate_smooth 2)
  simpa [lowNormalComplexSquaredRadius, mixedDot, Fin.sum_univ_succ]
    using h0.add (h1.add h2)

private theorem lowNormalMixedDot_fixed_contDiff (a : Fin 3 → ℂ) :
    ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ => mixedDot ξ a) := by
  have h0 := (lowNormalComplexCoordinate_smooth 0).mul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 3 → ℝ => a 0))
  have h1 := (lowNormalComplexCoordinate_smooth 1).mul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 3 → ℝ => a 1))
  have h2 := (lowNormalComplexCoordinate_smooth 2).mul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 3 → ℝ => a 2))
  simpa [mixedDot, Fin.sum_univ_succ]
    using h0.add (h1.add h2)

/-- Each fixed-center polynomial solenoidal germ is smooth to all orders. -/
theorem lowNormalNormalizedSolenoidalGerm_contDiff
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ) (d : Fin 3) :
    ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ =>
      lowNormalNormalizedSolenoidalGerm η ξ a d) := by
  have hRadius := lowNormalComplexSquaredRadius_contDiff.mul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 3 → ℝ => a d))
  have hDot := (lowNormalMixedDot_fixed_contDiff a).mul
    (lowNormalComplexCoordinate_smooth d)
  have h := (hRadius.sub hDot).div_const (lowNormalComplexSquaredRadius η)
  exact h

/-- A smooth real scalar weight produces a smooth complex vector packet. -/
theorem lowNormalScalarPacket_contDiff
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (χ : (Fin 3 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ => lowNormalScalarPacket η a χ ξ) := by
  apply contDiff_pi'
  intro d
  have hχc : ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ => (χ ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hχ
  exact hχc.mul (lowNormalNormalizedSolenoidalGerm_contDiff η a d)

/-- A compactly supported weight produces a compactly supported vector packet. -/
theorem lowNormalScalarPacket_hasCompactSupport
    (η : Fin 3 → ℝ) (a : Fin 3 → ℂ)
    (χ : (Fin 3 → ℝ) → ℝ)
    (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun ξ : Fin 3 → ℝ => lowNormalScalarPacket η a χ ξ) := by
  have hs := hχ.smul_right
    (f' := fun ξ : Fin 3 → ℝ => lowNormalNormalizedSolenoidalGerm η ξ a)
  convert hs using 1
  funext ξ d
  change ((χ ξ : ℂ) * lowNormalNormalizedSolenoidalGerm η ξ a d) =
    (χ ξ : ℝ) • lowNormalNormalizedSolenoidalGerm η ξ a d
  rw [← Complex.coe_smul, smul_eq_mul]

/-- Smoothness is preserved by the algebraic three-packet sum. -/
theorem lowNormalPositiveThreePacketSum_contDiff
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (hp : ContDiff ℝ ∞ χP)
    (hq : ContDiff ℝ ∞ χQ)
    (hr : ContDiff ℝ ∞ χR) :
    ContDiff ℝ ∞ (lowNormalPositiveThreePacketSum t χP χQ χR) := by
  have hP := lowNormalScalarPacket_contDiff lowNormalAuditP lowNormalAuditA χP hp
  have hQ := lowNormalScalarPacket_contDiff
    (lowNormalAuditQ t) lowNormalAuditB χQ hq
  have hR := lowNormalScalarPacket_contDiff
    (lowNormalAuditR t) lowNormalAuditC χR hr
  exact (hP.add hQ).add hR

/-- Compact support is preserved by the algebraic three-packet sum. -/
theorem lowNormalPositiveThreePacketSum_hasCompactSupport
    (t : ℝ) (χP χQ χR : (Fin 3 → ℝ) → ℝ)
    (hp : HasCompactSupport χP)
    (hq : HasCompactSupport χQ)
    (hr : HasCompactSupport χR) :
    HasCompactSupport (lowNormalPositiveThreePacketSum t χP χQ χR) := by
  have hP := lowNormalScalarPacket_hasCompactSupport lowNormalAuditP lowNormalAuditA χP hp
  have hQ := lowNormalScalarPacket_hasCompactSupport
    (lowNormalAuditQ t) lowNormalAuditB χQ hq
  have hR := lowNormalScalarPacket_hasCompactSupport
    (lowNormalAuditR t) lowNormalAuditC χR hr
  exact (hP.add hQ).add hR

/-- The Hermitian reflection operation preserves smoothness. -/
theorem lowNormalHermitianize_contDiff
    (G : (Fin 3 → ℝ) → (Fin 3 → ℂ))
    (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (lowNormalHermitianize G) := by
  have hReflect : ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ => G (-ξ)) :=
    hG.comp contDiff_id.neg
  have hConj : ContDiff ℝ ∞
      (fun ξ : Fin 3 → ℝ => fun d : Fin 3 => star (G (-ξ) d)) := by
    apply contDiff_pi'
    intro d
    have hComponent : ContDiff ℝ ∞ (fun ξ : Fin 3 → ℝ => G (-ξ) d) :=
      (contDiff_apply ℝ ℂ d).comp hReflect
    have h := Complex.conjCLE.contDiff.comp hComponent
    simpa only [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using h
  exact hG.add hConj

/-- The Hermitian reflection operation preserves compact support. -/
theorem lowNormalHermitianize_hasCompactSupport
    (G : (Fin 3 → ℝ) → (Fin 3 → ℂ))
    (hG : HasCompactSupport G) :
    HasCompactSupport (lowNormalHermitianize G) := by
  have hReflect : HasCompactSupport (fun ξ : Fin 3 → ℝ => G (-ξ)) := by
    simpa only [Function.comp_def, Homeomorph.coe_neg] using
      hG.comp_homeomorph (Homeomorph.neg (Fin 3 → ℝ))
  have hConj : HasCompactSupport
      (fun ξ : Fin 3 → ℝ => fun d : Fin 3 => star (G (-ξ) d)) := by
    let J : (Fin 3 → ℂ) → (Fin 3 → ℂ) :=
      fun v d => star (v d)
    have hJ0 : J 0 = 0 := by
      funext d
      simp [J]
    have h := hReflect.comp_left (g := J) hJ0
    simpa only [J, Function.comp_def] using h
  exact hG.add hConj

/-- The actual six-packet Fourier field is smooth to all orders. -/
theorem lowNormalSmoothSixPacketFourier_contDiff
    (t : ℝ) (ht : t ≠ 0) :
    ContDiff ℝ ∞ (lowNormalSmoothSixPacketFourier t ht) := by
  exact lowNormalHermitianize_contDiff _
    (lowNormalPositiveThreePacketSum_contDiff t _ _ _
      (lowNormalSmoothCenterCutoff_contDiff t ht 0)
      (lowNormalSmoothCenterCutoff_contDiff t ht 1)
      (lowNormalSmoothCenterCutoff_contDiff t ht 2))

/-- The complete vector field, not just its scalar weights, is compactly supported. -/
theorem lowNormalSmoothSixPacketFourier_hasCompactSupport
    (t : ℝ) (ht : t ≠ 0) :
    HasCompactSupport (lowNormalSmoothSixPacketFourier t ht) := by
  exact lowNormalHermitianize_hasCompactSupport _
    (lowNormalPositiveThreePacketSum_hasCompactSupport t _ _ _
      (lowNormalSmoothCenterCutoff_hasCompactSupport t ht 0)
      (lowNormalSmoothCenterCutoff_hasCompactSupport t ht 1)
      (lowNormalSmoothCenterCutoff_hasCompactSupport t ht 2))

/-- The full real-compatible solenoidal Fourier field as one vector Schwartz map. -/
noncomputable def lowNormalSmoothSixPacketSchwartz
    (t : ℝ) (ht : t ≠ 0) :
    𝓢(Fin 3 → ℝ, Fin 3 → ℂ) :=
  (lowNormalSmoothSixPacketFourier_hasCompactSupport t ht).toSchwartzMap
    (lowNormalSmoothSixPacketFourier_contDiff t ht)

@[simp] theorem lowNormalSmoothSixPacketSchwartz_apply
    (t : ℝ) (ht : t ≠ 0) (ξ : Fin 3 → ℝ) :
    lowNormalSmoothSixPacketSchwartz t ht ξ =
      lowNormalSmoothSixPacketFourier t ht ξ := rfl

/-- Exact pointwise incompressibility of the packaged Schwartz field. -/
theorem lowNormalSmoothSixPacketSchwartz_divergence
    (t : ℝ) (ht : t ≠ 0) (ξ : Fin 3 → ℝ) :
    mixedDot ξ (lowNormalSmoothSixPacketSchwartz t ht ξ) = 0 := by
  rw [lowNormalSmoothSixPacketSchwartz_apply]
  exact lowNormalSmoothSixPacketFourier_divergence t ht ξ

/-- Exact conjugate reflection of the packaged Schwartz field. -/
theorem lowNormalSmoothSixPacketSchwartz_reality
    (t : ℝ) (ht : t ≠ 0) (ξ : Fin 3 → ℝ) :
    lowNormalSmoothSixPacketSchwartz t ht (-ξ) =
      fun d => star (lowNormalSmoothSixPacketSchwartz t ht ξ d) := by
  simp only [lowNormalSmoothSixPacketSchwartz_apply]
  have hNeg : (-ξ : Fin 3 → ℝ) = (fun d => -ξ d) := by
    funext d
    simp
  rw [hNeg]
  exact lowNormalSmoothSixPacketFourier_reality t ht ξ

end
end PrimeTensor.FirstMonomialTriad
