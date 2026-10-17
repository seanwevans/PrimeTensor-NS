import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderEnergy244

/-!
# Actual 243-slot square/fourth roots and the real Holder interface

The preceding global E₂/E₃ estimate still accepted three mass-identification
hypotheses and one real Holder hypothesis. Here the arrays are the actual
positive roots of the 3/2/2 Schwartz derivative integrals. Consequently all
three mass-identification hypotheses are proved, with exact 243-slot indexing.

The analytic step is reduced to two genuine `realLpEnorm` root identities,
for exponents 2 and 4, applied to the actual jets. We transfer those
identities to the real slot Holder inequality via the already proved
extended-real Holder theorem; no unproved `hSlot` is passed to the result.

This module does NOT assert the Lp identities. They remain explicit until
proved separately. No Navier--Stokes regularity conclusion is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3
private abbrev Slots244 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeHolderActualRoots244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev actualThirdJet244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.2)))

private abbrev actualMiddleJet244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.2.1}
    (∂_{h3FourierAxisDirection p.2.2.1} (f p.2.2.2.1))

private abbrev actualCrossJet244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection p.1}
    (∂_{h3FourierAxisDirection p.2.2.2.1} (f p.2.2.2.2))

private abbrev actualSlot244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : ℝ :=
  lowNormalRealSchwartz_firstMonomialSlotIntegral f
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

private abbrev actualThirdMass244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : ℝ :=
  ∫ ξ : V3, (actualThirdJet244 f p ξ) ^ 2

private abbrev actualMiddleMass244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : ℝ :=
  ∫ ξ : V3, (actualMiddleJet244 f p ξ) ^ 4

private abbrev actualCrossMass244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : ℝ :=
  ∫ ξ : V3, (actualCrossJet244 f p ξ) ^ 4

private theorem actualThirdMass244_nonneg
    (f : A3 → SchwartzMap V3 ℝ) (p : Slots244) :
    0 ≤ actualThirdMass244 f p :=
  integral_nonneg (fun ξ => sq_nonneg _)

private theorem actualMiddleMass244_nonneg
    (f : A3 → SchwartzMap V3 ℝ) (p : Slots244) :
    0 ≤ actualMiddleMass244 f p :=
  integral_nonneg (fun ξ => by positivity)

private theorem actualCrossMass244_nonneg
    (f : A3 → SchwartzMap V3 ℝ) (p : Slots244) :
    0 ≤ actualCrossMass244 f p :=
  integral_nonneg (fun ξ => by positivity)

/-- Exact positive L²-root of a third Schwartz jet's square integral. -/
noncomputable def actualThirdRoot244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : ℝ :=
  Real.sqrt (actualThirdMass244 f p)

/-- Exact positive L⁴-root of a middle second-jet's quartic integral. -/
noncomputable def actualMiddleRoot244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : ℝ :=
  Real.sqrt (Real.sqrt (actualMiddleMass244 f p))

/-- Exact positive L⁴-root of a cross second-jet's quartic integral. -/
noncomputable def actualCrossRoot244 (f : A3 → SchwartzMap V3 ℝ)
    (p : Slots244) : ℝ :=
  Real.sqrt (Real.sqrt (actualCrossMass244 f p))

private theorem sqrt_sqrt_pow_four (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt (Real.sqrt x)) ^ 4 = x := by
  calc
    (Real.sqrt (Real.sqrt x)) ^ 4 =
        ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt x) ^ 2 := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg x)]
    _ = x := Real.sq_sqrt hx

/-- All three roots are nonnegative, including the zero-integral case. -/
theorem actualHolderRoots244_nonneg
    (f : A3 → SchwartzMap V3 ℝ) (p : Slots244) :
    0 ≤ actualThirdRoot244 f p ∧
      0 ≤ actualMiddleRoot244 f p ∧
      0 ≤ actualCrossRoot244 f p := by
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩

/-- No Sobolev interpolation is needed for these exact root powers. -/
theorem actualHolderRoots244_powers
    (f : A3 → SchwartzMap V3 ℝ) (p : Slots244) :
    actualThirdRoot244 f p ^ 2 = actualThirdMass244 f p ∧
      actualMiddleRoot244 f p ^ 4 = actualMiddleMass244 f p ∧
      actualCrossRoot244 f p ^ 4 = actualCrossMass244 f p := by
  refine ⟨?_, ?_, ?_⟩
  · exact Real.sq_sqrt (actualThirdMass244_nonneg f p)
  · exact sqrt_sqrt_pow_four _ (actualMiddleMass244_nonneg f p)
  · exact sqrt_sqrt_pow_four _ (actualCrossMass244_nonneg f p)

private theorem actualThirdMass244_sum
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ p : Slots244, actualThirdMass244 f p) =
      lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass f := by
  classical
  simp only [Slots244, Fintype.sum_prod_type,
    actualThirdMass244, actualThirdJet244,
    lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass]

private theorem actualMiddleMass244_sum
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ p : Slots244, actualMiddleMass244 f p) =
      lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass f := by
  classical
  simp only [Slots244, Fintype.sum_prod_type,
    actualMiddleMass244, actualMiddleJet244,
    lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass]

private theorem actualCrossMass244_sum
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ p : Slots244, actualCrossMass244 f p) =
      lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass f := by
  classical
  simp only [Slots244, Fintype.sum_prod_type,
    actualCrossMass244, actualCrossJet244,
    lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass]

/-- No longer any mass-identification premises: all three equalities
follow by summing the exact pointwise squared/fourth-power roots. -/
theorem actualHolderRoots244_globalMasses
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ p : Slots244, actualThirdRoot244 f p ^ 2) =
        lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass f ∧
    (∑ p : Slots244, actualMiddleRoot244 f p ^ 4) =
        lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass f ∧
    (∑ p : Slots244, actualCrossRoot244 f p ^ 4) =
        lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass f := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · calc
      (∑ p : Slots244, actualThirdRoot244 f p ^ 2) =
          ∑ p : Slots244, actualThirdMass244 f p := by
        apply Finset.sum_congr rfl
        intro p _
        exact (actualHolderRoots244_powers f p).1
      _ = _ := actualThirdMass244_sum f
  · calc
      (∑ p : Slots244, actualMiddleRoot244 f p ^ 4) =
          ∑ p : Slots244, actualMiddleMass244 f p := by
        apply Finset.sum_congr rfl
        intro p _
        exact (actualHolderRoots244_powers f p).2.1
      _ = _ := actualMiddleMass244_sum f
  · calc
      (∑ p : Slots244, actualCrossRoot244 f p ^ 4) =
          ∑ p : Slots244, actualCrossMass244 f p := by
        apply Finset.sum_congr rfl
        intro p _
        exact (actualHolderRoots244_powers f p).2.2
      _ = _ := actualCrossMass244_sum f

/-- The existing extended-real spatial Holder theorem implies a genuine
real signed slot inequality once the exact three Lp-root representations
are available. There is no *extra* real-Holder hypothesis. -/
theorem actualHolderRoots244_realSlot_of_normIdentities
    (f : A3 → SchwartzMap V3 ℝ)
    (h2 : ∀ p : Slots244,
      realLpEnorm volume 2 (actualThirdJet244 f p) =
        ENNReal.ofReal (actualThirdRoot244 f p))
    (h4middle : ∀ p : Slots244,
      realLpEnorm volume 4 (actualMiddleJet244 f p) =
        ENNReal.ofReal (actualMiddleRoot244 f p))
    (h4cross : ∀ p : Slots244,
      realLpEnorm volume 4 (actualCrossJet244 f p) =
        ENNReal.ofReal (actualCrossRoot244 f p))
    (p : Slots244) :
    |actualSlot244 f p| ≤
      actualThirdRoot244 f p *
        (actualMiddleRoot244 f p * actualCrossRoot244 f p) := by
  have hHolder := lowNormalRealSchwartz_firstMonomialSlot_holder244 f
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  change ‖actualSlot244 f p‖ₑ ≤
    realLpEnorm volume 2 (actualThirdJet244 f p) *
      (realLpEnorm volume 4 (actualMiddleJet244 f p) *
        realLpEnorm volume 4 (actualCrossJet244 f p)) at hHolder
  rw [h2 p, h4middle p, h4cross p] at hHolder
  obtain ⟨ha, hb, hc⟩ := actualHolderRoots244_nonneg f p
  have hProduct : 0 ≤ actualThirdRoot244 f p *
      (actualMiddleRoot244 f p * actualCrossRoot244 f p) :=
    mul_nonneg ha (mul_nonneg hb hc)
  have hPacked :
      ENNReal.ofReal (actualThirdRoot244 f p *
        (actualMiddleRoot244 f p * actualCrossRoot244 f p)) =
      ENNReal.ofReal (actualThirdRoot244 f p) *
        (ENNReal.ofReal (actualMiddleRoot244 f p) *
          ENNReal.ofReal (actualCrossRoot244 f p)) := by
    rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  have hReal : ENNReal.ofReal |actualSlot244 f p| ≤
      ENNReal.ofReal (actualThirdRoot244 f p *
        (actualMiddleRoot244 f p * actualCrossRoot244 f p)) := by
    calc
      ENNReal.ofReal |actualSlot244 f p| =
          ‖actualSlot244 f p‖ₑ := by
        simpa only [Real.norm_eq_abs] using
          (ofReal_norm (actualSlot244 f p))
      _ ≤ _ := by
        rw [hPacked]
        exact hHolder
  exact (ENNReal.ofReal_le_ofReal_iff hProduct).mp hReal

/-- The final physical E₂ E₃⁵ estimate now needs ONLY the actual
Lp-norm-to-root identities, not four independent free-array hypotheses. -/
theorem lowNormalRealSchwartz_firstMonomial_holder244_energyGN_of_normIdentities
    (f : A3 → SchwartzMap V3 ℝ)
    (h2 : ∀ p : Slots244,
      realLpEnorm volume 2 (actualThirdJet244 f p) =
        ENNReal.ofReal (actualThirdRoot244 f p))
    (h4middle : ∀ p : Slots244,
      realLpEnorm volume 4 (actualMiddleJet244 f p) =
        ENNReal.ofReal (actualMiddleRoot244 f p))
    (h4cross : ∀ p : Slots244,
      realLpEnorm volume 4 (actualCrossJet244 f p) =
        ENNReal.ofReal (actualCrossRoot244 f p)) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
      (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 9 *
        lowNormalSecondJetSobolevRealConstant ^ 6 *
          (lowNormalRealSchwartzH3Energy2 f *
            (lowNormalRealSchwartzH3Energy3 f) ^ 5) := by
  obtain ⟨hThird, hMiddle, hCross⟩ := actualHolderRoots244_globalMasses f
  exact lowNormalRealSchwartz_firstMonomial_holder244_energyGN f
    (actualThirdRoot244 f) (actualMiddleRoot244 f) (actualCrossRoot244 f)
    (fun p => actualHolderRoots244_realSlot_of_normIdentities f
      h2 h4middle h4cross p)
    hThird hMiddle hCross

end
end PrimeTensor.FirstMonomialTriad
