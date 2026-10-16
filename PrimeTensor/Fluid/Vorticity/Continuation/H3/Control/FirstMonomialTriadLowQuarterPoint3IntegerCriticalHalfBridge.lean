import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzExactHolder244

/-!
# Integer-order critical-half moment bridge for the actual Schwartz H3 monomial

The known critical-half bound has a second route, avoiding a new fractional
Sobolev-space interface. In R3, the classical Gagliardo--Nirenberg estimate
for a second derivative g = D²u is

  ‖g‖₄ <= C ‖g‖₂^(1/4) ‖Dg‖₂^(3/4).

The *already formalized* 243-slot 2-4-4 Holder aggregation would then give,
after finite-sum Cauchy and GN aggregation,

  |M(u)|^4 <= K^4 E2(u) E3(u)^5.

This module establishes the decisive coefficient-one INTEGER-MOMENT bridge

  E2 E3^5 <= E0 E1 D^4

from the existing physical adjacent Cauchy estimates, using no Fourier
interpolation, solenoidality, PDE hypotheses or division by a possibly zero
energy. Together with one explicit quartic GN/Hölder bound it proves

  |M| <= K sqrt(E0+E1) D.

The quantitative Gagliardo--Nirenberg/Hölder aggregation is NOT proved here.
The terminal critical-half estimate is known analysis and does NOT imply
unconditional large-data Navier--Stokes regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeIntegerCriticalHalf (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The coefficient-one, integer-order form of critical-half interpolation.
This is a genuine consequence of adjacent Cauchy: it includes every zero
energy case and does not assume any nonlinear product inequality. -/
theorem criticalHalf_integerMoments_E2_mul_E3_pow_five_le
    (E0 E1 E2 E3 D : ℝ)
    (h0 : 0 ≤ E0) (h1 : 0 ≤ E1) (h2 : 0 ≤ E2)
    (h3 : 0 ≤ E3) (hD : 0 ≤ D)
    (h12 : E2 ^ 2 ≤ E1 * E3)
    (h23 : E3 ^ 2 ≤ E2 * D)
    (h02 : E2 ^ 2 ≤ E0 * D) :
    E2 * E3 ^ 5 ≤ E0 * E1 * D ^ 4 := by
  have h2D : 0 ≤ E2 * D := mul_nonneg h2 hD
  have h23nonneg : 0 ≤ E2 * E3 := mul_nonneg h2 h3
  calc
    E2 * E3 ^ 5 = (E3 ^ 2 * E3 ^ 2) * (E2 * E3) := by ring
    _ ≤ ((E2 * D) * E3 ^ 2) * (E2 * E3) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h23 (sq_nonneg E3)) h23nonneg
    _ ≤ ((E2 * D) * (E2 * D)) * (E2 * E3) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h23 h2D) h23nonneg
    _ = E2 ^ 2 * (E2 * E3 * D ^ 2) := by ring
    _ ≤ (E1 * E3) * (E2 * E3 * D ^ 2) := by
      exact mul_le_mul_of_nonneg_right h12 (by positivity)
    _ = (E1 * E2 * D ^ 2) * E3 ^ 2 := by ring
    _ ≤ (E1 * E2 * D ^ 2) * (E2 * D) := by
      exact mul_le_mul_of_nonneg_left h23 (by positivity)
    _ = (E1 * D ^ 3) * E2 ^ 2 := by ring
    _ ≤ (E1 * D ^ 3) * (E0 * D) := by
      exact mul_le_mul_of_nonneg_left h02 (by positivity)
    _ = E0 * E1 * D ^ 4 := by ring

/-- Exact integer-moment bridge for the genuine zero-through-fourth-order
physical Schwartz energy blocks, without any divergence-free hypothesis. -/
theorem lowNormalRealSchwartz_integerMoments_E2_mul_E3_pow_five_le
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2 f *
        (lowNormalRealSchwartzH3Energy3 f) ^ 5 ≤
      lowNormalRealSchwartzH3Energy0 f *
        lowNormalRealSchwartzH3Energy1 f *
        (lowNormalRealSchwartzH3TopDissipation f) ^ 4 := by
  exact criticalHalf_integerMoments_E2_mul_E3_pow_five_le
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    (lowNormalRealSchwartzH3TopDissipation f)
    (lowNormalRealSchwartzH3Energy0_nonneg f)
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    (lowNormalRealSchwartzH3Energy3_nonneg f)
    (lowNormalRealSchwartzH3TopDissipation_nonneg f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3 f)
    (lowNormalRealSchwartzH3Energy3_sq_le_E2_mul_topDissipation f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E0_mul_topDissipation f)

/-- The algebraic absorption of an INTEGER-energy Gagliardo--Nirenberg
bound. The quartic monomial hypothesis is left explicit and must eventually
be established by the real quantitative Gagliardo--Nirenberg inequality. -/
theorem criticalHalf_integerMoments_quarticToEnergy
    (M K E0 E1 E2 E3 D : ℝ)
    (hK : 0 ≤ K)
    (h0 : 0 ≤ E0) (h1 : 0 ≤ E1) (h2 : 0 ≤ E2)
    (h3 : 0 ≤ E3) (hD : 0 ≤ D)
    (h12 : E2 ^ 2 ≤ E1 * E3)
    (h23 : E3 ^ 2 ≤ E2 * D)
    (h02 : E2 ^ 2 ≤ E0 * D)
    (hGN : |M| ^ 4 ≤ K ^ 4 * (E2 * E3 ^ 5)) :
    |M| ≤ K * Real.sqrt (E0 + E1) * D := by
  have hBridge := criticalHalf_integerMoments_E2_mul_E3_pow_five_le
    E0 E1 E2 E3 D h0 h1 h2 h3 hD h12 h23 h02
  have hSumNonneg : 0 ≤ E0 + E1 := add_nonneg h0 h1
  have hRootSq : (Real.sqrt (E0 + E1)) ^ 2 = E0 + E1 :=
    Real.sq_sqrt hSumNonneg
  have hGeom : E0 * E1 ≤ (E0 + E1) ^ 2 := by
    nlinarith [sq_nonneg E0, sq_nonneg E1, mul_nonneg h0 h1]
  have hPower : |M| ^ 4 ≤ (K * Real.sqrt (E0 + E1) * D) ^ 4 := by
    calc
      |M| ^ 4 ≤ K ^ 4 * (E2 * E3 ^ 5) := hGN
      _ ≤ K ^ 4 * (E0 * E1 * D ^ 4) :=
        mul_le_mul_of_nonneg_left hBridge (by positivity)
      _ = (K ^ 4 * D ^ 4) * (E0 * E1) := by ring
      _ ≤ (K ^ 4 * D ^ 4) * (E0 + E1) ^ 2 :=
        mul_le_mul_of_nonneg_left hGeom (by positivity)
      _ = (K * Real.sqrt (E0 + E1) * D) ^ 4 := by
        calc
          _ = (K ^ 4 * D ^ 4) * ((Real.sqrt (E0 + E1)) ^ 2) ^ 2 := by
            rw [hRootSq]
          _ = _ := by ring
  by_contra hn
  have hlt : K * Real.sqrt (E0 + E1) * D < |M| :=
    lt_of_not_ge hn
  have hStrict : (K * Real.sqrt (E0 + E1) * D) ^ 4 < |M| ^ 4 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge hPower) hStrict

/-- Direct specialization to the actual physical 243-slot monomial. The
coefficient `K` is arbitrary but its quartic GN hypothesis is NOT asserted
without proof. -/
theorem lowNormalRealSchwartz_criticalHalf_of_integerGNQuartic
    (f : A3 → SchwartzMap V3 ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hGN : |lowNormalRealSchwartzPoint3Monomial f| ^ 4 ≤
      K ^ 4 * (lowNormalRealSchwartzH3Energy2 f *
        (lowNormalRealSchwartzH3Energy3 f) ^ 5)) :
    |lowNormalRealSchwartzPoint3Monomial f| ≤
      K * Real.sqrt
        (lowNormalRealSchwartzH3Energy0 f +
          lowNormalRealSchwartzH3Energy1 f) *
        lowNormalRealSchwartzH3TopDissipation f := by
  exact criticalHalf_integerMoments_quarticToEnergy
    (lowNormalRealSchwartzPoint3Monomial f) K
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    (lowNormalRealSchwartzH3TopDissipation f)
    hK
    (lowNormalRealSchwartzH3Energy0_nonneg f)
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    (lowNormalRealSchwartzH3Energy3_nonneg f)
    (lowNormalRealSchwartzH3TopDissipation_nonneg f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3 f)
    (lowNormalRealSchwartzH3Energy3_sq_le_E2_mul_topDissipation f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E0_mul_topDissipation f)
    hGN

end
end PrimeTensor.FirstMonomialTriad
