import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzOrderwiseGraph244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SecondJetQuarticGN
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Exact derivative-difference energy identities and the quartic Sobolev bridge

The mixed 81+27 orderwise graph compares Schwartz jets by subtracting their
already differentiated representatives. This file connects those differences
to the ordinary physical H³ energies of the actual difference field `f - g`.

The key step is linearity of each Schwartz-space directional derivative:
`D_v (a - b) = D_v a - D_v b`. Thus the 81 integrated squares are *exactly*
`E₃(f-g)`, and the 27 integrated fourth powers are *exactly* `Q₄(f-g)`.

The pre-existing real Gagliardo--Nirenberg estimate then supplies

  Q₄(f-g)^2 <= S^6 E₂(f-g) (card(Axis 3) E₃(f-g))^3.

These are actual integrals on the physical Euclidean Schwartz carrier, not
symbolic seminorms. This does not yet establish physical Sobolev density or
identify the non-Schwartz transport pairing with its Schwartz limit.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeDifferenceBridge244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Subtraction commutes with the *actual* Schwartz directional derivative.
The derivative is instantiated through mathlib's continuous-linear-map API. -/
theorem schwartzLineDeriv_sub244
    (v : V3) (a b : SchwartzMap V3 ℝ) :
    ∂_{v} (a - b) = (∂_{v} a : SchwartzMap V3 ℝ) - ∂_{v} b := by
  simpa only [LineDeriv.lineDerivOpCLM_apply] using
    (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap V3 ℝ) v).map_sub a b

/-- Exactly two ordered Schwartz derivatives respect subtraction. -/
theorem schwartzTwoLineDerivs_sub244
    (v w : V3) (a b : SchwartzMap V3 ℝ) :
    ∂_{v} (∂_{w} (a - b)) =
      (∂_{v} (∂_{w} a) : SchwartzMap V3 ℝ) -
        ∂_{v} (∂_{w} b) := by
  simp only [schwartzLineDeriv_sub244]

/-- Exactly three ordered Schwartz derivatives respect subtraction. -/
theorem schwartzThreeLineDerivs_sub244
    (v w z : V3) (a b : SchwartzMap V3 ℝ) :
    ∂_{v} (∂_{w} (∂_{z} (a - b))) =
      (∂_{v} (∂_{w} (∂_{z} a)) : SchwartzMap V3 ℝ) -
        ∂_{v} (∂_{w} (∂_{z} b)) := by
  simp only [schwartzLineDeriv_sub244]

/-- The *actual* three-dimensional vector of Schwartz differences. -/
noncomputable def schwartzVelocityDifference244
    (f g : A3 → SchwartzMap V3 ℝ) : A3 → SchwartzMap V3 ℝ :=
  fun j => f j - g j

/-- The orderwise graph's 81 third-jet difference squares are exactly the
H³ third-order energy of the difference field, without an inequality or
unaccounted multiplicity. -/
theorem schwartzThirdJetDifference_squareMass_eq_energy3244
    (f g : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      ∫ x : V3,
        (((∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k}
               (∂_{h3FourierAxisDirection l} (f j)))) -
           (∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k}
               (∂_{h3FourierAxisDirection l} (g j))))) x) ^ 2) =
      lowNormalRealSchwartzH3Energy3 (schwartzVelocityDifference244 f g) := by
  unfold lowNormalRealSchwartzH3Energy3 schwartzVelocityDifference244
  simp only [schwartzThreeLineDerivs_sub244]

/-- The orderwise graph's 27 second-jet fourth-power integrals are exactly
the previously formalized total second-jet quartic mass of `f-g`. -/
theorem schwartzSecondJetDifference_quarticMass_eq244
    (f g : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∫ x : V3,
        (((∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k} (f j))) -
           (∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k} (g j)))) x) ^ 4) =
      lowNormalRealSchwartzSecondJetsQuarticMass
        (schwartzVelocityDifference244 f g) := by
  unfold lowNormalRealSchwartzSecondJetsQuarticMass schwartzVelocityDifference244
  simp only [schwartzTwoLineDerivs_sub244]

/-- The exact quartic second-jet difference mass satisfies the existing
quantitative H³ Gagliardo--Nirenberg estimate. This is the analytical
bridge from genuine graph differences to *ordinary* Schwartz E₂ and E₃
energy; no root convergence or Sobolev density is assumed. -/
theorem schwartzSecondJetDifference_quarticGN_energy244
    (f g : A3 → SchwartzMap V3 ℝ) :
    ((∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∫ x : V3,
        (((∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k} (f j))) -
           (∂_{h3FourierAxisDirection i}
             (∂_{h3FourierAxisDirection k} (g j)))) x) ^ 4)) ^ 2 ≤
      lowNormalSecondJetSobolevRealConstant ^ 6 *
        (lowNormalRealSchwartzH3Energy2
            (schwartzVelocityDifference244 f g) *
          (((Fintype.card A3 : ℝ) *
              lowNormalRealSchwartzH3Energy3
                (schwartzVelocityDifference244 f g)) ^ 3)) := by
  rw [schwartzSecondJetDifference_quarticMass_eq244]
  exact lowNormalRealSchwartz_secondJets_quarticGN_real_normalized
    (schwartzVelocityDifference244 f g)

end
end PrimeTensor.FirstMonomialTriad
