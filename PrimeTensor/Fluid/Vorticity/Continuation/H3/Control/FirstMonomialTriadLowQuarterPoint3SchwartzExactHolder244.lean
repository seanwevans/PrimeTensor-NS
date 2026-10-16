import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfSeventhPowerClosure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Holder.Real

/-!
# Actual 243-slot Schwartz first monomial: unconditional 2-4-4 Holder

This module discharges the literal spatial triple-product Holder step for
all 243 slots of `lowNormalRealSchwartzPoint3Monomial`.  It does not assume
incompressibility, a Navier--Stokes path, a fractional Sobolev inequality,
or a new axiom. Each physical slot equals its corresponding real Schwartz
integral. The pre-existing complex-real bridge retains the factor **two**
from `spatialEnergyPairing`.

The conclusion is an **extended nonnegative real** estimate against the
sum of products of the genuine raw L2/L4/L4 seminorms. Proving a finite
profile-independent critical-half coefficient from this requires the
quantitative homogeneous Sobolev and fractional interpolation estimates.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv ENNReal

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSchwartzExactHolder244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exactly the three-derivative factor in one physical first-monomial slot. -/
private abbrev firstMonomialThirdJet (f : A3 → SchwartzMap V3 ℝ)
    (i k l j : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- Exactly one of the two second-derivative factors. -/
private abbrev firstMonomialSecondJet (f : A3 → SchwartzMap V3 ℝ)
    (k l r : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection k}
    (∂_{h3FourierAxisDirection l} (f r))

/-- The other second-derivative factor, with the original physical indices. -/
private abbrev firstMonomialCrossJet (f : A3 → SchwartzMap V3 ℝ)
    (i r j : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection r} (f j))

/-- Real Schwartz product in one of the exact ordered 243 physical slots.
No factor of two is included here; that factor is outside the full sum. -/
noncomputable def lowNormalRealSchwartz_firstMonomialSlotIntegral
    (f : A3 → SchwartzMap V3 ℝ) (i k l r j : A3) : ℝ :=
  ∫ x : V3,
    (firstMonomialThirdJet f i k l j x) *
      ((firstMonomialSecondJet f k l r x) *
        (firstMonomialCrossJet f i r j x))

/-- The exact raw `L² × L⁴ × L⁴` seminorm product for one physical slot.
It lives in `ℝ≥0∞`, matching the existing verified Holder theorem. -/
noncomputable def lowNormalRealSchwartz_firstMonomialSlotHolderWeight
    (f : A3 → SchwartzMap V3 ℝ) (i k l r j : A3) : ℝ≥0∞ :=
  realLpEnorm volume 2 (firstMonomialThirdJet f i k l j) *
    (realLpEnorm volume 4 (firstMonomialSecondJet f k l r) *
      realLpEnorm volume 4 (firstMonomialCrossJet f i r j))

/-- Schwarz smoothness discharges ALL three measurability premises of the
already formalized real `2-4-4` Holder theorem. -/
theorem lowNormalRealSchwartz_firstMonomialSlot_holder244
    (f : A3 → SchwartzMap V3 ℝ) (i k l r j : A3) :
    ‖lowNormalRealSchwartz_firstMonomialSlotIntegral f i k l r j‖ₑ ≤
      lowNormalRealSchwartz_firstMonomialSlotHolderWeight f i k l r j := by
  unfold lowNormalRealSchwartz_firstMonomialSlotIntegral
    lowNormalRealSchwartz_firstMonomialSlotHolderWeight
  exact enorm_integral_three_mul_le_244 (volume : Measure V3)
    ((firstMonomialThirdJet f i k l j).continuous.aemeasurable.enorm)
    ((firstMonomialSecondJet f k l r).continuous.aemeasurable.enorm)
    ((firstMonomialCrossJet f i r j).continuous.aemeasurable.enorm)

/-- The actual physical monomial equals twice the sum of **all** ordered
real Schwarz triple integrals. The original factor two is retained. -/
theorem lowNormalRealSchwartz_firstMonomial_eq_twice_slotSum
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzPoint3Monomial f =
      2 * (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        lowNormalRealSchwartz_firstMonomialSlotIntegral f i k l r j) := by
  have hRe :
      (h3SchwartzFirstMonomialAggregate
        (fun j => h3SchwartzComplexify (f j))).re =
        ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
          lowNormalRealSchwartz_firstMonomialSlotIntegral f i k l r j := by
    unfold h3SchwartzFirstMonomialAggregate
    change Complex.reCLM
      (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        h3SchwartzFirstMonomialSlot
          (fun j => h3SchwartzComplexify (f j)) i k l r j) = _
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro j _
    rw [h3SchwartzFirstMonomialSlot_complexify f i k l r j]
    rfl
  rw [lowNormalRealSchwartzPoint3Monomial_eq_complex, hRe]

/-- The full **243-slot** physical first-monomial Holder inequality.
Every component/index is present; no cancellation or smallness is assumed.
The only remaining input for a finite critical-half coefficient is
quantitative Sobolev/interpolation control of the norms on the RHS. -/
theorem lowNormalRealSchwartz_fullFirstMonomial_holder244
    (f : A3 → SchwartzMap V3 ℝ) :
    ‖lowNormalRealSchwartzPoint3Monomial f‖ₑ ≤
      ‖(2 : ℝ)‖ₑ *
        (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
          lowNormalRealSchwartz_firstMonomialSlotHolderWeight f i k l r j) := by
  rw [lowNormalRealSchwartz_firstMonomial_eq_twice_slotSum, enorm_mul]
  have hSum :
      ‖∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        lowNormalRealSchwartz_firstMonomialSlotIntegral f i k l r j‖ₑ ≤
      ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        lowNormalRealSchwartz_firstMonomialSlotHolderWeight f i k l r j := by
    apply enorm_sum_le_of_le Finset.univ
    intro i _
    apply enorm_sum_le_of_le Finset.univ
    intro k _
    apply enorm_sum_le_of_le Finset.univ
    intro l _
    apply enorm_sum_le_of_le Finset.univ
    intro r _
    apply enorm_sum_le_of_le Finset.univ
    intro j _
    exact lowNormalRealSchwartz_firstMonomialSlot_holder244 f i k l r j
  exact mul_le_mul_of_nonneg_left hSum (by positivity)

end
end PrimeTensor.FirstMonomialTriad
