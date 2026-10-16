import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderDiscrete244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetQuarticGN

/-!
# The 243-slot discrete 2-4-4 bound in genuine E₂ and E₃ energies

The previously proved finite Cauchy--Schwarz inequality has coefficient one,
and the exact slot multiplicities are 3, 9, 9. This file combines that
algebra with the already verified 27-slot fourth-power GN theorem.

The only *conditional* step is the precise real representation of each
analytic slot Holder weight. The arguments `hSlot`, `hThird`, `hMiddle`,
and `hCross` expose that interface instead of claiming it has been proved.

The final coefficient is 16 * card(Axis three)^9 * S^6 and the final energy
monomial is E₂ * E₃^5. This estimate alone is not a continuation criterion.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3
private abbrev FiveSlotsEnergy244 := A3 × (A3 × (A3 × (A3 × A3)))

noncomputable local instance axisFintypeEnergy244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev slotEnergy244 (f : A3 → SchwartzMap V3 ℝ)
    (p : FiveSlotsEnergy244) : ℝ :=
  lowNormalRealSchwartz_firstMonomialSlotIntegral f
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- Exact assembly from the 243-slot real Holder interface to the physical
third- and second-jet masses. The three sum identities are explicit to
prevent an illicit change of norm or dropping any index multiplicity. -/
theorem lowNormalRealSchwartz_firstMonomial_holder244_energyMass
    (f : A3 → SchwartzMap V3 ℝ)
    (a b c : FiveSlotsEnergy244 → ℝ)
    (hSlot : ∀ p : FiveSlotsEnergy244,
      |slotEnergy244 f p| ≤ a p * (b p * c p))
    (hThird :
      (∑ p : FiveSlotsEnergy244, a p ^ 2) =
        lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass f)
    (hMiddle :
      (∑ p : FiveSlotsEnergy244, b p ^ 4) =
        lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass f)
    (hCross :
      (∑ p : FiveSlotsEnergy244, c p ^ 4) =
        lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass f) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
      (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 6 *
        ((lowNormalRealSchwartzH3Energy3 f) ^ 2 *
          (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2) := by
  have hDiscrete :
      (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
        (16 : ℝ) *
          ((∑ p : FiveSlotsEnergy244, a p ^ 2) ^ 2 *
            ((∑ p : FiveSlotsEnergy244, b p ^ 4) *
              (∑ p : FiveSlotsEnergy244, c p ^ 4))) :=
    lowNormalRealSchwartz_firstMonomial_discrete244_transfer f a b c hSlot
  calc
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
        (16 : ℝ) *
          ((∑ p : FiveSlotsEnergy244, a p ^ 2) ^ 2 *
            ((∑ p : FiveSlotsEnergy244, b p ^ 4) *
              (∑ p : FiveSlotsEnergy244, c p ^ 4))) := hDiscrete
    _ = (16 : ℝ) *
          ((lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass f) ^ 2 *
            (lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass f *
              lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass f)) := by
      rw [hThird, hMiddle, hCross]
    _ = (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 6 *
          ((lowNormalRealSchwartzH3Energy3 f) ^ 2 *
            (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2) := by
      rw [lowNormalRealSchwartz_firstMonomialSlotMomentProduct_eq_E3_Q4]
      ring

/-- Apply the proved real 27-slot quartic GN bound. This exposes the
precise energy exponents: the full monomial's fourth power is bounded by
E₂ * E₃^5, with the exact finite multiplicity card(Axis three)^9. -/
theorem lowNormalRealSchwartz_firstMonomial_holder244_energyGN
    (f : A3 → SchwartzMap V3 ℝ)
    (a b c : FiveSlotsEnergy244 → ℝ)
    (hSlot : ∀ p : FiveSlotsEnergy244,
      |slotEnergy244 f p| ≤ a p * (b p * c p))
    (hThird :
      (∑ p : FiveSlotsEnergy244, a p ^ 2) =
        lowNormalRealSchwartz_firstMonomialThirdSlotSquareMass f)
    (hMiddle :
      (∑ p : FiveSlotsEnergy244, b p ^ 4) =
        lowNormalRealSchwartz_firstMonomialMiddleSlotQuarticMass f)
    (hCross :
      (∑ p : FiveSlotsEnergy244, c p ^ 4) =
        lowNormalRealSchwartz_firstMonomialCrossSlotQuarticMass f) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
      (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 9 *
        lowNormalSecondJetSobolevRealConstant ^ 6 *
          (lowNormalRealSchwartzH3Energy2 f *
            (lowNormalRealSchwartzH3Energy3 f) ^ 5) := by
  have hMass := lowNormalRealSchwartz_firstMonomial_holder244_energyMass
    f a b c hSlot hThird hMiddle hCross
  have hGN := lowNormalRealSchwartz_secondJets_quarticGN_real_normalized f
  have hNonneg :
      0 ≤ (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 6 *
        (lowNormalRealSchwartzH3Energy3 f) ^ 2 := by
    positivity
  calc
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
        (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 6 *
          ((lowNormalRealSchwartzH3Energy3 f) ^ 2 *
            (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2) := hMass
    _ = ((16 : ℝ) * (Fintype.card A3 : ℝ) ^ 6 *
          (lowNormalRealSchwartzH3Energy3 f) ^ 2) *
          (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2 := by ring
    _ ≤ ((16 : ℝ) * (Fintype.card A3 : ℝ) ^ 6 *
          (lowNormalRealSchwartzH3Energy3 f) ^ 2) *
          (lowNormalSecondJetSobolevRealConstant ^ 6 *
            (lowNormalRealSchwartzH3Energy2 f *
              (((Fintype.card A3 : ℝ) *
                lowNormalRealSchwartzH3Energy3 f) ^ 3))) :=
      mul_le_mul_of_nonneg_left hGN hNonneg
    _ = (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 9 *
          lowNormalSecondJetSobolevRealConstant ^ 6 *
            (lowNormalRealSchwartzH3Energy2 f *
              (lowNormalRealSchwartzH3Energy3 f) ^ 5) := by ring

end
end PrimeTensor.FirstMonomialTriad
