import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinExactPolarizationField
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Strong temporal FTC and cutoff-independent Lipschitz bound for the actual Galerkin field

The complete complex Leray convolution, including output collisions, is now
an exact bilinear source. This module proves that the *actual* viscous
Galerkin vector field is Lipschitz between the radii 3/2 and 5/4, with a
constant independent of the number of Fourier modes. Its linear Laplacian
part costs only 10 in this radius step when viscosity is at most 1/10; the
nonlinear part costs 1000, giving the genuine 1010 constant.

At each Fourier mode the strong Galerkin ODE identity (HasDerivAt of the
actual coefficient path equal to the actual Galerkin field), interval
integrability, and endpoint continuity are sufficient to DERIVE the exact
Bochner temporal increment by the fundamental theorem of calculus. Unlike
the earlier discrete residual gate, no arbitrary temporal increment equation
is postulated. This is valid when any coefficient vanishes.

The source path is not constructed here; existence of the finite-dimensional
ODE flow, a joint time-integrated Wiener norm bound, and passage to the
untruncated Navier--Stokes solution remain separate obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Set
open scoped Interval

noncomputable section

private abbrev TemporalBand244 := EuclideanSpace ℂ (Fin 3)
private abbrev TemporalIndex244 := thirdFullThreeBandZ3Index244

/-- The 5/4 analytic Wiener Laplacian is uniformly controlled by the
3/2 analytic mass, for any finite set of actual integer frequencies. -/
theorem thirdFullThreeBand_z3GalerkinLaplacianLowerReserve244
    (s : Finset TemporalIndex244)
    (u : TemporalIndex244 → TemporalBand244) :
    thirdFullThreeBandZ3GalerkinLaplacianWiener244
      (Real.log (5 / 4 : ℝ)) s u ≤
      100 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s u := by
  classical
  unfold thirdFullThreeBandZ3GalerkinLaplacianWiener244
    thirdFullThreeBandZ3GalerkinWienerMass244
  calc
    _ ≤ ∑ n ∈ s, 100 *
        (thirdFullThreeBandZ3Weight244 (Real.log (3 / 2 : ℝ)) n * ‖u n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_right
        (thirdFullThreeBand_z3TwoRadiusLaplacianEnvelope244 n)
        (norm_nonneg (u n))
      calc
        _ = (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 *
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n) * ‖u n‖ := by ring
        _ ≤ (100 * thirdFullThreeBandZ3Weight244
            (Real.log (3 / 2 : ℝ)) n) * ‖u n‖ := h
        _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

/-- The viscous-plus-complete-Leray Galerkin field difference is dominated
by the physical Laplacian of the difference and the genuine full-output
nonlinear source difference. No support factor or artificial scalar field
appears here. -/
theorem thirdFullThreeBand_z3GalerkinNSFieldDifference_mass_bound244
    (mu r : ℝ) (hmu : 0 ≤ mu)
    (s : Finset TemporalIndex244)
    (u v : TemporalIndex244 → TemporalBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (fun n => thirdFullThreeBandZ3GalerkinNSField244 mu s u n -
        thirdFullThreeBandZ3GalerkinNSField244 mu s v n) ≤
      mu * thirdFullThreeBandZ3GalerkinLaplacianWiener244 r s
        (fun n => u n - v n) +
      (∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) := by
  classical
  have hpoint (n : TemporalIndex244) :
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinNSField244 mu s u n -
          thirdFullThreeBandZ3GalerkinNSField244 mu s v n‖ ≤
      mu * (thirdFullThreeBandZ3Weight244 r n *
        (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 * ‖u n - v n‖)) +
      thirdFullThreeBandZ3Weight244 r n *
        ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖ := by
    have hmuN : 0 ≤ mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 :=
      mul_nonneg hmu (sq_nonneg _)
    have hfield :
        thirdFullThreeBandZ3GalerkinNSField244 mu s u n -
          thirdFullThreeBandZ3GalerkinNSField244 mu s v n =
        (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
            (u n - v n) +
        (thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
          thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n) := by
      unfold thirdFullThreeBandZ3GalerkinNSField244
      rw [smul_sub]
      abel
    have hheat :
        ‖(-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
          (u n - v n)‖ =
        (mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2) *
          ‖u n - v n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hmuN]
    rw [hfield]
    calc
      thirdFullThreeBandZ3Weight244 r n *
          ‖(-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
             (u n - v n) +
            (thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
             thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n)‖ ≤
        thirdFullThreeBandZ3Weight244 r n *
          (‖(-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
             (u n - v n)‖ +
           ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
             thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (thirdFullThreeBand_z3Weight_pos244 r n).le
      _ = _ := by rw [hheat]; ring
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
    thirdFullThreeBandZ3GalerkinLaplacianWiener244
  calc
    _ ≤ ∑ n ∈ s,
        (mu * (thirdFullThreeBandZ3Weight244 r n *
          (‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2 * ‖u n - v n‖)) +
        thirdFullThreeBandZ3Weight244 r n *
          ‖thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n -
            thirdFullThreeBandZ3GalerkinQuadratic244 s s v v n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hpoint n
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Genuine cutoff-independent Lipschitz constant for the ACTUAL periodic
Galerkin NS field, from radius 3/2 to radius 5/4. The 1010 consists of
1000 for the exact projected quadratic source and 10 for viscosity.
Neither the Fourier mode count nor the output collision count appears. -/
theorem thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_100Ball244
    (mu : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset TemporalIndex244)
    (u v : TemporalIndex244 → TemporalBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s u ≤ 100)
    (hV : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ)) s v ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) s
        (fun n => thirdFullThreeBandZ3GalerkinNSField244 mu s u n -
          thirdFullThreeBandZ3GalerkinNSField244 mu s v n) ≤
      1010 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s (fun n => u n - v n) := by
  let M := thirdFullThreeBandZ3GalerkinWienerMass244
    (Real.log (3 / 2 : ℝ)) s (fun n => u n - v n)
  have hnonneg : 0 ≤ M := by
    dsimp [M, thirdFullThreeBandZ3GalerkinWienerMass244]
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le
      (norm_nonneg _)
  have hLap := thirdFullThreeBand_z3GalerkinLaplacianLowerReserve244
    s (fun n => u n - v n)
  have hVisc : mu * thirdFullThreeBandZ3GalerkinLaplacianWiener244
        (Real.log (5 / 4 : ℝ)) s (fun n => u n - v n) ≤ 10 * M := by
    calc
      _ ≤ mu * (100 * M) := mul_le_mul_of_nonneg_left hLap hmu
      _ ≤ (1 / 10 : ℝ) * (100 * M) :=
        mul_le_mul_of_nonneg_right hmuMax
          (mul_nonneg (by norm_num) hnonneg)
      _ = 10 * M := by ring
  have hSource := thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244
    s s u v hU hV
  have hField := thirdFullThreeBand_z3GalerkinNSFieldDifference_mass_bound244
    mu (Real.log (5 / 4 : ℝ)) hmu s u v
  dsimp only [M] at hVisc
  linarith

/-- A stronger W_(9/5) ball supplies the middle W_(3/2) ball without a
cardinality constant; therefore the preceding field Lipschitz bound
holds on the actual analytical 100-ball used in the Galerkin bootstrap. -/
theorem thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_highBall244
    (mu : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset TemporalIndex244)
    (u v : TemporalIndex244 → TemporalBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s u ≤ 100)
    (hV : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s v ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (5 / 4 : ℝ)) s
        (fun n => thirdFullThreeBandZ3GalerkinNSField244 mu s u n -
          thirdFullThreeBandZ3GalerkinNSField244 mu s v n) ≤
      1010 * thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s (fun n => u n - v n) := by
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  exact thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_100Ball244
    mu hmu hmuMax s u v
    ((thirdFullThreeBand_z3WienerMass_radius_mono244
      _ _ hRadius s u).trans hU)
    ((thirdFullThreeBand_z3WienerMass_radius_mono244
      _ _ hRadius s v).trans hV)

/-- Actual strong Galerkin ODE temporal FTC, at EVERY selected Fourier mode.
This is a deduction from the strong time derivative of the actual NS field,
not an assumed temporal increment identity. It remains true at zero modes
and when the Fourier coefficient passes through the origin. -/
theorem thirdFullThreeBand_z3GalerkinStrongODE_FTC244
    (mu a b : ℝ) (hab : a ≤ b)
    (s : Finset TemporalIndex244)
    (u : ℝ → TemporalIndex244 → TemporalBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n)
        volume a b) :
    ∀ n ∈ s,
      u b n - u a n =
        ∫ t in a..b,
          thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n := by
  intro n hn
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab (hContinuous n hn) (hODE n hn) (hIntegrable n hn)).symm

/-- A genuinely proved per-frequency integral rate estimate for a strong
Galerkin ODE path. This controls the norm across zeros without invoking
any coefficientwise logarithmic derivative. No frequency-cardinality
claim is hidden in this per-frequency inequality. -/
theorem thirdFullThreeBand_z3GalerkinStrongODE_normIncrement244
    (mu a b : ℝ) (hab : a ≤ b)
    (s : Finset TemporalIndex244)
    (u : ℝ → TemporalIndex244 → TemporalBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n)
        volume a b) :
    ∀ n ∈ s,
      ‖u b n - u a n‖ ≤
        ∫ t in a..b,
          ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖ := by
  intro n hn
  have hFTC := thirdFullThreeBand_z3GalerkinStrongODE_FTC244
    mu a b hab s u hContinuous hODE hIntegrable n hn
  rw [hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- Summing the exact per-frequency norm increments yields the Wiener
increment estimate with the TIME INTEGRALS still explicit. This is the
correct precursor to an integral of a full weighted Galerkin field; no
unjustified interchange or cardinality factor is introduced. -/
theorem thirdFullThreeBand_z3GalerkinStrongODE_WienerIntegralBound244
    (mu a b r : ℝ) (hab : a ≤ b)
    (s : Finset TemporalIndex244)
    (u : ℝ → TemporalIndex244 → TemporalBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hIntegrable : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n)
        volume a b) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (fun n => u b n - u a n) ≤
    ∑ n ∈ s, thirdFullThreeBandZ3Weight244 r n *
      (∫ t in a..b,
        ‖thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n‖) := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left
    (thirdFullThreeBand_z3GalerkinStrongODE_normIncrement244
      mu a b hab s u hContinuous hODE hIntegrable n hn)
    (thirdFullThreeBand_z3Weight_pos244 r n).le

end
end PrimeTensor.FirstMonomialTriad
