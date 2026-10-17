import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderNormIdentities244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3IntegerCriticalHalfBridge

/-!
# Homogeneous critical-half estimate from the unconditional 243-slot Holder bound

The unconditional Schwartz Holder/second-jet GN estimate now gives

    |M(f)|^4 <= C * E2(f) * E3(f)^5,
    C = 16 * card(Axis three)^9 * S^6.

The separately proved integer-order moment bridge gives

    E2(f) * E3(f)^5 <= E0(f) * E1(f) * D(f)^4.

Combining them and taking NONNEGATIVE fourth roots proves, with NO analytic
premises beyond the physical Schwartz field,

    |M(f)| <= C^(1/4) * (E0(f)*E1(f))^(1/4) * D(f).

The precise fourth roots are represented by nested `Real.sqrt`. This is
homogeneous under spatial dilations, in contrast with the weaker
sqrt(E0+E1) bound. Both are bounds on this particular actual signed
Schwartz first monomial; neither is an unconditional Navier--Stokes
continuation theorem or controls every nonlinear H3 energy term.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeCriticalHalfHolder244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuine nonnegative fourth root, including at zero. -/
theorem criticalHalf_fourthRoot_pow_four
    (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt (Real.sqrt x)) ^ 4 = x := by
  calc
    (Real.sqrt (Real.sqrt x)) ^ 4 =
        ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt x) ^ 2 := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg x)]
    _ = x := Real.sq_sqrt hx

/-- The universal real coefficient inherited from all 243 actual physical
slots and the already established whole-space second-jet Sobolev constant. -/
noncomputable def lowNormalRealSchwartz_holder244CriticalConstant : ℝ :=
  Real.sqrt (Real.sqrt
    ((16 : ℝ) * (Fintype.card A3 : ℝ) ^ 9 *
      lowNormalSecondJetSobolevRealConstant ^ 6))

theorem lowNormalRealSchwartz_holder244CriticalConstant_nonneg :
    0 ≤ lowNormalRealSchwartz_holder244CriticalConstant := by
  unfold lowNormalRealSchwartz_holder244CriticalConstant
  exact Real.sqrt_nonneg _

theorem lowNormalRealSchwartz_holder244CriticalConstant_pow_four :
    lowNormalRealSchwartz_holder244CriticalConstant ^ 4 =
      (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 9 *
        lowNormalSecondJetSobolevRealConstant ^ 6 := by
  unfold lowNormalRealSchwartz_holder244CriticalConstant
  apply criticalHalf_fourthRoot_pow_four
  positivity

/-- The unconditional 243-slot nonlinear fourth-power estimate, restated
in exactly the form consumed by the older integer-moment closure. -/
theorem lowNormalRealSchwartz_firstMonomial_holder244_integerQuartic
    (f : A3 → SchwartzMap V3 ℝ) :
    |lowNormalRealSchwartzPoint3Monomial f| ^ 4 ≤
      lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
        (lowNormalRealSchwartzH3Energy2 f *
          (lowNormalRealSchwartzH3Energy3 f) ^ 5) := by
  have hExisting :=
    lowNormalRealSchwartz_firstMonomial_holder244_energyGN_unconditional f
  calc
    |lowNormalRealSchwartzPoint3Monomial f| ^ 4 =
        (lowNormalRealSchwartzPoint3Monomial f) ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ (16 : ℝ) * (Fintype.card A3 : ℝ) ^ 9 *
          lowNormalSecondJetSobolevRealConstant ^ 6 *
          (lowNormalRealSchwartzH3Energy2 f *
            (lowNormalRealSchwartzH3Energy3 f) ^ 5) := hExisting
    _ = lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
          (lowNormalRealSchwartzH3Energy2 f *
            (lowNormalRealSchwartzH3Energy3 f) ^ 5) := by
      rw [lowNormalRealSchwartz_holder244CriticalConstant_pow_four]

/-- A sharp homogeneous algebraic consequence of the *integer* moment bridge.
No division by an energy is needed; zero masses are included. -/
theorem criticalHalf_integerMoments_quarticToHomogeneousHalf
    (M K E0 E1 E2 E3 D : ℝ)
    (hK : 0 ≤ K)
    (h0 : 0 ≤ E0) (h1 : 0 ≤ E1) (h2 : 0 ≤ E2)
    (h3 : 0 ≤ E3) (hD : 0 ≤ D)
    (h12 : E2 ^ 2 ≤ E1 * E3)
    (h23 : E3 ^ 2 ≤ E2 * D)
    (h02 : E2 ^ 2 ≤ E0 * D)
    (hGN : |M| ^ 4 ≤ K ^ 4 * (E2 * E3 ^ 5)) :
    |M| ≤ K * Real.sqrt (Real.sqrt (E0 * E1)) * D := by
  have hBridge := criticalHalf_integerMoments_E2_mul_E3_pow_five_le
    E0 E1 E2 E3 D h0 h1 h2 h3 hD h12 h23 h02
  have hMass : 0 ≤ E0 * E1 := mul_nonneg h0 h1
  have hRoot :
      (Real.sqrt (Real.sqrt (E0 * E1))) ^ 4 = E0 * E1 :=
    criticalHalf_fourthRoot_pow_four _ hMass
  have hPower :
      |M| ^ 4 ≤
        (K * Real.sqrt (Real.sqrt (E0 * E1)) * D) ^ 4 := by
    calc
      |M| ^ 4 ≤ K ^ 4 * (E2 * E3 ^ 5) := hGN
      _ ≤ K ^ 4 * (E0 * E1 * D ^ 4) :=
        mul_le_mul_of_nonneg_left hBridge (pow_nonneg hK 4)
      _ = (K * Real.sqrt (Real.sqrt (E0 * E1)) * D) ^ 4 := by
        calc
          K ^ 4 * (E0 * E1 * D ^ 4) =
              K ^ 4 * ((Real.sqrt (Real.sqrt (E0 * E1))) ^ 4 * D ^ 4) := by
            rw [hRoot]
          _ = _ := by ring
  by_contra hn
  have hlt : K * Real.sqrt (Real.sqrt (E0 * E1)) * D < |M| :=
    lt_of_not_ge hn
  have hStrict :
      (K * Real.sqrt (Real.sqrt (E0 * E1)) * D) ^ 4 < |M| ^ 4 :=
    pow_lt_pow_left₀ hlt (by positivity)
      (by norm_num : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge hPower) hStrict

/-- Unconditional homogeneous critical-half bound for the complete,
signed, actual 243-slot first monomial of a real Schwartz vector field. -/
theorem lowNormalRealSchwartz_firstMonomial_criticalHalfHomogeneous244
    (f : A3 → SchwartzMap V3 ℝ) :
    |lowNormalRealSchwartzPoint3Monomial f| ≤
      lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (lowNormalRealSchwartzH3Energy0 f *
            lowNormalRealSchwartzH3Energy1 f)) *
        lowNormalRealSchwartzH3TopDissipation f := by
  exact criticalHalf_integerMoments_quarticToHomogeneousHalf
    (lowNormalRealSchwartzPoint3Monomial f)
    lowNormalRealSchwartz_holder244CriticalConstant
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    (lowNormalRealSchwartzH3TopDissipation f)
    lowNormalRealSchwartz_holder244CriticalConstant_nonneg
    (lowNormalRealSchwartzH3Energy0_nonneg f)
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    (lowNormalRealSchwartzH3Energy3_nonneg f)
    (lowNormalRealSchwartzH3TopDissipation_nonneg f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3 f)
    (lowNormalRealSchwartzH3Energy3_sq_le_E2_mul_topDissipation f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E0_mul_topDissipation f)
    (lowNormalRealSchwartz_firstMonomial_holder244_integerQuartic f)

/-- The weaker inhomogeneous threshold is now also unconditional for this
physical Schwartz monomial; it follows from the preexisting integer bridge. -/
theorem lowNormalRealSchwartz_firstMonomial_criticalHalfInhomogeneous244
    (f : A3 → SchwartzMap V3 ℝ) :
    |lowNormalRealSchwartzPoint3Monomial f| ≤
      lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt
          (lowNormalRealSchwartzH3Energy0 f +
            lowNormalRealSchwartzH3Energy1 f) *
        lowNormalRealSchwartzH3TopDissipation f := by
  exact lowNormalRealSchwartz_criticalHalf_of_integerGNQuartic
    f lowNormalRealSchwartz_holder244CriticalConstant
    lowNormalRealSchwartz_holder244CriticalConstant_nonneg
    (lowNormalRealSchwartz_firstMonomial_holder244_integerQuartic f)

end
end PrimeTensor.FirstMonomialTriad
