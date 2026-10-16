import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetSixthMassBound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzQuarticL2L6

/-!
# Quantitative fourth-power Gagliardo–Nirenberg for all 27 Schwartz second jets

The already proved coefficient-one 27-slot L²/L⁶ quartic interpolation is
combined with the proved genuine sixth-mass Sobolev bound.  First we work in
`ENNReal` without suppressing any coercion or division-by-zero case; then the
finite Sobolev coefficient is returned to `ℝ` and the actual quartic bound
is obtained there.  The sole dimension factor comes from the existing
`Point3` sup-norm Fréchet-to-coordinate estimate.

No PDE, incompressibility, monomial estimate, or continuation claim is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal NNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSecondJetQuarticGN (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- All 27 *actual* real quartic integrals, not a selected jet. -/
noncomputable def lowNormalRealSchwartzSecondJetsQuarticMass
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3,
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))) ξ) ^ 4

/-- All 27 actual real sixth-power integrals. -/
noncomputable def lowNormalRealSchwartzSecondJetsSixthMass
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3,
    ∫ ξ : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))) ξ) ^ 6

/-- Coefficient-one quartic interpolation for the named full mass. -/
theorem lowNormalRealSchwartz_secondJets_quarticMass_sq_le_E2_mul_sixthMass
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2 ≤
      lowNormalRealSchwartzH3Energy2 f *
        lowNormalRealSchwartzSecondJetsSixthMass f := by
  exact lowNormalRealSchwartz_secondJets_quartic_sq_le_E2_mul_sixth f

/-- The sixth-power bound with its full real-mass interface. -/
theorem lowNormalRealSchwartz_secondJets_sixthMass_ofReal_le_E3
    (f : A3 → SchwartzMap V3 ℝ) :
    ENNReal.ofReal (lowNormalRealSchwartzSecondJetsSixthMass f) ≤
      (lowNormalSecondJetSobolevConstant ^ 2 *
        ENNReal.ofReal
          ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3 := by
  exact lowNormalRealSchwartz_secondJets_sixthMass_le_sobolev_E3_cube f

/-- The genuine combined 27-slot GN bound in `ENNReal`: the separate
quartic interpolation and sixth-mass Sobolev theorems are both discharged. -/
theorem lowNormalRealSchwartz_secondJets_quarticGN_ennreal
    (f : A3 → SchwartzMap V3 ℝ) :
    ENNReal.ofReal ((lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2) ≤
      ENNReal.ofReal (lowNormalRealSchwartzH3Energy2 f) *
        (lowNormalSecondJetSobolevConstant ^ 2 *
          ENNReal.ofReal
            ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3 := by
  have hE2 : 0 ≤ lowNormalRealSchwartzH3Energy2 f :=
    lowNormalRealSchwartzH3Energy2_nonneg f
  have hQuartic :=
    lowNormalRealSchwartz_secondJets_quarticMass_sq_le_E2_mul_sixthMass f
  have hSixth :=
    lowNormalRealSchwartz_secondJets_sixthMass_ofReal_le_E3 f
  calc
    ENNReal.ofReal ((lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2) ≤
        ENNReal.ofReal
          (lowNormalRealSchwartzH3Energy2 f *
            lowNormalRealSchwartzSecondJetsSixthMass f) :=
      ENNReal.ofReal_le_ofReal hQuartic
    _ = ENNReal.ofReal (lowNormalRealSchwartzH3Energy2 f) *
          ENNReal.ofReal (lowNormalRealSchwartzSecondJetsSixthMass f) :=
      ENNReal.ofReal_mul hE2
    _ ≤ ENNReal.ofReal (lowNormalRealSchwartzH3Energy2 f) *
          (lowNormalSecondJetSobolevConstant ^ 2 *
            ENNReal.ofReal
              ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3 :=
      mul_le_mul_of_nonneg_left hSixth (by positivity)

/-- The actual *finite real* homogeneous Sobolev coefficient, before the
`ENNReal` embedding used for the Lp seminorm inequalities. -/
noncomputable def lowNormalSecondJetSobolevRealConstant : ℝ :=
  ((MeasureTheory.SNormLESNormFDerivOfEqConst
    ℝ (volume : Measure Point3) (2 : ℝ≥0) : ℝ≥0) : ℝ)

theorem lowNormalSecondJetSobolevRealConstant_nonneg :
    0 ≤ lowNormalSecondJetSobolevRealConstant := by
  unfold lowNormalSecondJetSobolevRealConstant
  positivity

theorem lowNormalSecondJetSobolevConstant_eq_ofReal :
    lowNormalSecondJetSobolevConstant =
      ENNReal.ofReal lowNormalSecondJetSobolevRealConstant := by
  unfold lowNormalSecondJetSobolevConstant lowNormalSecondJetSobolevRealConstant
  simp only [ENNReal.ofReal_coe_nnreal]

/-- Full real-valued 27-slot quartic Gagliardo–Nirenberg bound.
All 27 second jets and all 81 third jets remain, with no spurious factor
of 27; the only dimensional loss is the intrinsic three-coordinate factor. -/
theorem lowNormalRealSchwartz_secondJets_quarticGN_real
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2 ≤
      lowNormalRealSchwartzH3Energy2 f *
        ((lowNormalSecondJetSobolevRealConstant ^ 2 *
          ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3) := by
  have hE2 : 0 ≤ lowNormalRealSchwartzH3Energy2 f :=
    lowNormalRealSchwartzH3Energy2_nonneg f
  have hE3 : 0 ≤ lowNormalRealSchwartzH3Energy3 f :=
    lowNormalRealSchwartzH3Energy3_nonneg f
  have hS := lowNormalSecondJetSobolevRealConstant_nonneg
  have hCard : 0 ≤ (Fintype.card A3 : ℝ) := Nat.cast_nonneg _
  have hProduct : 0 ≤
      (Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f :=
    mul_nonneg hCard hE3
  have hRight :
      lowNormalSecondJetSobolevConstant ^ 2 *
          ENNReal.ofReal
            ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f) =
        ENNReal.ofReal
          (lowNormalSecondJetSobolevRealConstant ^ 2 *
            ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) := by
    rw [lowNormalSecondJetSobolevConstant_eq_ofReal]
    rw [← ENNReal.ofReal_pow hS]
    rw [← ENNReal.ofReal_mul (pow_nonneg hS 2)]
  have hCombined := lowNormalRealSchwartz_secondJets_quarticGN_ennreal f
  rw [hRight] at hCombined
  have hConverted :
      ENNReal.ofReal ((lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2) ≤
        ENNReal.ofReal
          (lowNormalRealSchwartzH3Energy2 f *
            ((lowNormalSecondJetSobolevRealConstant ^ 2 *
              ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3)) := by
    calc
      _ ≤ ENNReal.ofReal (lowNormalRealSchwartzH3Energy2 f) *
          (ENNReal.ofReal
            (lowNormalSecondJetSobolevRealConstant ^ 2 *
              ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f))) ^ 3 := hCombined
      _ = ENNReal.ofReal (lowNormalRealSchwartzH3Energy2 f) *
          ENNReal.ofReal
            ((lowNormalSecondJetSobolevRealConstant ^ 2 *
              ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3) := by
        rw [ENNReal.ofReal_pow (mul_nonneg (pow_nonneg hS 2) hProduct)]
      _ = _ := by
        rw [ENNReal.ofReal_mul hE2]
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hE2 (pow_nonneg (mul_nonneg (pow_nonneg hS 2) hProduct) 3))).mp
    hConverted

/-- Algebraically normalized: the Sobolev coefficient occurs to power six,
matching the classic integer-order Gagliardo–Nirenberg exponent. -/
theorem lowNormalRealSchwartz_secondJets_quarticGN_real_normalized
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzSecondJetsQuarticMass f) ^ 2 ≤
      lowNormalSecondJetSobolevRealConstant ^ 6 *
        (lowNormalRealSchwartzH3Energy2 f *
          (((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f) ^ 3)) := by
  calc
    _ ≤ lowNormalRealSchwartzH3Energy2 f *
      ((lowNormalSecondJetSobolevRealConstant ^ 2 *
        ((Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy3 f)) ^ 3) :=
      lowNormalRealSchwartz_secondJets_quarticGN_real f
    _ = _ := by ring

end
end PrimeTensor.FirstMonomialTriad
