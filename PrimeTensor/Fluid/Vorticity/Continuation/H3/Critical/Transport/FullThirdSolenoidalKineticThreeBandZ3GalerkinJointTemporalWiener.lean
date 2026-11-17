import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongTemporalFTC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Joint finite-Galerkin Wiener FTC, with no Fourier cardinality loss

The previous module derived actual coefficientwise FTC from HasDerivAt of
Navier--Stokes Galerkin's complete Leray field. This module proves the
missing finite-sum / time-integral interchange, and then uses the uniform
spatial speed estimate to bound the FULL Wiener increment by 51000*(b-a).

All Fourier outputs and coefficients (including zero coefficients and
freshly generated modes in the Galerkin set) are retained. The cutoff is
not present in the constants. The theorem assumes a strong Galerkin path
and the W_(9/5) 100-ball along the time interval; it does not construct
such a path or prove the high-radius ball persists.

The final estimates bound actual nonlinear-source and full-vector-field
time variations linearly in t-a. This is the pointwise temporal integrand
needed for an O(h^2) exponential-Euler Duhamel error, not an assertion of
the Duhamel identity or an infinite-dimensional Navier--Stokes solution.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Set
open scoped Interval

noncomputable section

private abbrev JointIndex244 := thirdFullThreeBandZ3Index244
private abbrev JointBand244 := EuclideanSpace ℂ (Fin 3)

/-- A finite collection of real Bochner interval integrals commutes exactly
with its Fourier sum. There is no frequency-cardinality coefficient. -/
theorem thirdFullThreeBand_z3GalerkinFiniteTimeIntegralSum244
    (a b : ℝ) (s : Finset JointIndex244)
    (f : JointIndex244 → ℝ → ℝ)
    (hInt : ∀ n ∈ s, IntervalIntegrable (f n) volume a b) :
    (∑ n ∈ s, ∫ t in a..b, f n t) =
      ∫ t in a..b, ∑ n ∈ s, f n t := by
  classical
  exact (intervalIntegral.integral_finsetSum hInt).symm

/-- Exact weighted interchange for the ACTUAL NS Galerkin vector field,
not an abstract family of scalar majorants. -/
theorem thirdFullThreeBand_z3GalerkinFieldTimeIntegral_interchange244
    (mu a b r : ℝ) (s : Finset JointIndex244)
    (u : ℝ → JointIndex244 → JointBand244)
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable
        (fun t : ℝ => ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)
        volume a b) :
    (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
      (∫ t in a..b,
        ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)) =
      ∫ t in a..b,
        thirdFullThreeBandZ3GalerkinWienerMass244 r s
          (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t)) := by
  classical
  have hWeighted : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)
        volume a b := by
    intro n hn
    exact (hIntegrable n hn).const_mul _
  calc
    _ = ∑ n ∈ s,
        ∫ t in a..b,
          thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in a..b, ∑ n ∈ s,
          thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖ :=
        thirdFullThreeBand_z3GalerkinFiniteTimeIntegralSum244 a b s _ hWeighted
    _ = _ := by
      simp only [thirdFullThreeBandZ3GalerkinWienerMass244]

/-- Integrating the genuine W_(3/2) Galerkin speed ceiling costs exactly
elapsed time, with no factor depending on the number of retained modes. -/
theorem thirdFullThreeBand_z3GalerkinFieldTimeIntegral_51000_100Ball244
    (mu a b : ℝ) (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset JointIndex244)
    (u : ℝ → JointIndex244 → JointBand244)
    (hHighBall : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100)
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable
        (fun t : ℝ => ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)
        volume a b) :
    (∑ n ∈ s, thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n *
      (∫ t in a..b,
        ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)) ≤
      51000 * (b - a) := by
  classical
  let r : ℝ := Real.log (3 / 2 : ℝ)
  have hWeighted : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)
        volume a b := by
    intro n hn
    exact (hIntegrable n hn).const_mul _
  have hSumInt : IntervalIntegrable
      (fun t : ℝ => ∑ n ∈ s,
        thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)
      volume a b := by
    have hSumFun :
        (∑ n ∈ s, (fun t : ℝ =>
          thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)) =
        (fun t : ℝ => ∑ n ∈ s,
          thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖) := by
      funext t
      rw [Finset.sum_apply]
    rw [← hSumFun]
    exact IntervalIntegrable.sum s hWeighted
  have hCap (t : ℝ) (ht : t ∈ Set.Icc a b) :
      (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖) ≤
        51000 := by
    simpa only [r, thirdFullThreeBandZ3GalerkinWienerMass244] using
      (thirdFullThreeBand_z3GalerkinNSField_speed51000_100Ball244
        mu hmu hmuMax s (u t) (hHighBall t ht))
  have hConstInt : IntervalIntegrable
      (fun _t : ℝ => (51000 : ℝ)) volume a b := by
    exact intervalIntegrable_const
  have hTimeBound :
      (∫ t in a..b,
        ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖) ≤
      ∫ _t in a..b, (51000 : ℝ) :=
    intervalIntegral.integral_mono_on hab hSumInt hConstInt hCap
  calc
    _ = ∫ t in a..b,
          thirdFullThreeBandZ3GalerkinWienerMass244 r s
            (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t)) := by
        exact thirdFullThreeBand_z3GalerkinFieldTimeIntegral_interchange244
          mu a b r s u hIntegrable
    _ = ∫ t in a..b,
          ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
            ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖ := by
        simp only [thirdFullThreeBandZ3GalerkinWienerMass244]
    _ ≤ ∫ _t in a..b, (51000 : ℝ) := hTimeBound
    _ = 51000 * (b - a) := by
        simp [mul_comm]

/-- A cutoff-free temporal increment for a GENUINE strong Galerkin ODE.
The time-integrated Fourier sum is controlled by the actual NS field;
no separate postulated Wiener increment inequality is needed. -/
theorem thirdFullThreeBand_z3GalerkinStrongODE_WienerIncrement51000_100Ball244
    (mu a b : ℝ) (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset JointIndex244)
    (u : ℝ → JointIndex244 → JointBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n)
        volume a b)
    (hHighBall : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s (fun n => u b n - u a n) ≤
      51000 * (b - a) := by
  have hFTC := thirdFullThreeBand_z3GalerkinStrongODE_WienerIntegralBound244
    mu a b (Real.log (3 / 2 : ℝ)) hab s u hContinuous hODE hIntegrable
  have hNormIntegrable : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖)
        volume a b := by
    intro n hn
    exact (hIntegrable n hn).norm
  have hRate := thirdFullThreeBand_z3GalerkinFieldTimeIntegral_51000_100Ball244
    mu a b hab hmu hmuMax s u hHighBall hNormIntegrable
  exact hFTC.trans hRate

/-- The proven strong ODE increment and the exact full Leray polarization
bound the change in quadratic source at every elapsed time. No division by
a Fourier amplitude occurs, including newly created modes. -/
theorem thirdFullThreeBand_z3GalerkinSourceTimeVariation51000000_100Ball244
    (a t : ℝ)
    (s : Finset JointIndex244)
    (u : ℝ → JointIndex244 → JointBand244)
    (hHighA : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s (u a) ≤ 100)
    (hHighT : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100)
    (hIncrement : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) ≤
      51000 * (t - a)) :
    (∑ n ∈ s, thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
      ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n -
        thirdFullThreeBandZ3GalerkinQuadratic244 s s (u a) (u a) n‖) ≤
      51000000 * (t - a) := by
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hMiddleT := (thirdFullThreeBand_z3WienerMass_radius_mono244
    _ _ hRadius s (u t)).trans hHighT
  have hMiddleA := (thirdFullThreeBand_z3WienerMass_radius_mono244
    _ _ hRadius s (u a)).trans hHighA
  have hSource := thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244
    s s (u t) (u a) hMiddleT hMiddleA
  calc
    _ ≤ 1000 * thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) := hSource
    _ ≤ 1000 * (51000 * (t - a)) :=
      mul_le_mul_of_nonneg_left hIncrement (by norm_num)
    _ = 51000000 * (t - a) := by ring

/-- Viscosity plus exact quadratic transport has the corresponding 51,510,000
pointwise temporal modulus, obtained from the TRUE full Galerkin field. -/
theorem thirdFullThreeBand_z3GalerkinFieldTimeVariation51510000_100Ball244
    (mu a t : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset JointIndex244)
    (u : ℝ → JointIndex244 → JointBand244)
    (hHighA : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s (u a) ≤ 100)
    (hHighT : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100)
    (hIncrement : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) ≤
      51000 * (t - a)) :
    thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (5 / 4 : ℝ)) s
      (fun n => thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n -
        thirdFullThreeBandZ3GalerkinNSField244 mu s (u a) n) ≤
      51510000 * (t - a) := by
  have hField := thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_highBall244
    mu hmu hmuMax s (u t) (u a) hHighT hHighA
  calc
    _ ≤ 1010 * thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) := hField
    _ ≤ 1010 * (51000 * (t - a)) :=
      mul_le_mul_of_nonneg_left hIncrement (by norm_num)
    _ = 51510000 * (t - a) := by ring

end
end PrimeTensor.FirstMonomialTriad
