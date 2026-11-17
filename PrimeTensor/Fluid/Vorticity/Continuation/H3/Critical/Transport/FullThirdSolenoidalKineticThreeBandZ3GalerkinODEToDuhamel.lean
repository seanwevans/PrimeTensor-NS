import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinDuhamelResidual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Genuine strong Z3 Galerkin ODE implies its retarded heat Duhamel formula

For each physical integer Fourier mode of the complete complex Leray Galerkin
convolution, the strong Navier--Stokes ODE gives the exact heat integrating-
factor derivative. Bochner FTC and cancellation of exponential factors then
recover the true retarded heat equation, rather than assuming a mild identity.

The nonlinear source remains the exact full-output ordered-pair convolution;
newly generated Fourier modes and modes whose initial coefficient is zero
are retained. No frequency-cardinality factor enters the argument.

The quantitative corollary applies the previously proved cutoff-uniform
25,750,000 h^2 consistency estimate. A strong coefficientwise ODE, path
continuity, interval integrability of the retarded source, the high-radius
100-ball, and the Wiener increment estimate remain explicit hypotheses.
The time-integrability and existence of the finite-dimensional ODE flow and
preservation of the high-radius ball remain distinct analytic tasks.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Set
open scoped Interval

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

private abbrev ODEIndex244 := thirdFullThreeBandZ3Index244
private abbrev ODEBand244 := EuclideanSpace ℂ (Fin 3)

/-- The actual integrating-factor derivative for a three-complex-coordinate
heat ODE, including its additive source. It uses the real vector space on
the complex Euclidean band; no assumption that any component is nonzero. -/
theorem thirdFullThreeBand_z3HeatIntegratingFactor_hasDerivAt244
    (lambda t : ℝ) (F Q : ℝ → ODEBand244)
    (hODE : HasDerivAt F ((-lambda) • F t + Q t) t) :
    HasDerivAt (fun z : ℝ => Real.exp (lambda * z) • F z)
      (Real.exp (lambda * t) • Q t) t := by
  have hLinear : HasDerivAt (fun z : ℝ => lambda * z) lambda t := by
    simpa using (hasDerivAt_const_mul (x := t) lambda)
  have hExp : HasDerivAt (fun z : ℝ => Real.exp (lambda * z))
      (Real.exp (lambda * t) * lambda) t := hLinear.exp
  have hProduct := hExp.smul hODE
  have hValue :
      Real.exp (lambda * t) • ((-lambda) • F t + Q t) +
          (Real.exp (lambda * t) * lambda) • F t =
        Real.exp (lambda * t) • Q t := by
    rw [smul_add, smul_smul, mul_neg, neg_smul]
    abel
  change HasDerivAt (fun z : ℝ => Real.exp (lambda * z) • F z)
    (Real.exp (lambda * t) • ((-lambda) • F t + Q t) +
      (Real.exp (lambda * t) * lambda) • F t) t at hProduct
  rw [hValue] at hProduct
  exact hProduct

/-- Retarded Duhamel from genuine strong ODE derivatives on an arbitrary
ordered time interval. Integrability is only required of the actual
retarded source; it is converted algebraically to integrating-factor
integrability, and is not an assumed Duhamel equation. -/
theorem thirdFullThreeBand_z3HeatODE_retardedDuhamel244
    (lambda a b : ℝ) (hab : a ≤ b) (F Q : ℝ → ODEBand244)
    (hContinuous : ContinuousOn F (Set.Icc a b))
    (hODE : ∀ t ∈ Set.Ioo a b,
      HasDerivAt F ((-lambda) • F t + Q t) t)
    (hRetardedInt : IntervalIntegrable
      (fun t : ℝ => Real.exp (-(lambda * (b - t))) • Q t)
      volume a b) :
    F b = Real.exp (-(lambda * (b - a))) • F a +
      ∫ t in a..b, Real.exp (-(lambda * (b - t))) • Q t := by
  let H : ℝ → ODEBand244 := fun t => Real.exp (lambda * t) • Q t
  have hFactor (t : ℝ) :
      Real.exp (lambda * b) •
          (Real.exp (-(lambda * (b - t))) • Q t) = H t := by
    dsimp only [H]
    rw [smul_smul, ← Real.exp_add]
    have hArg : lambda * b + -(lambda * (b - t)) = lambda * t := by ring
    rw [hArg]
  have hWeightedInt : IntervalIntegrable H volume a b := by
    have hScaled := hRetardedInt.smul (Real.exp (lambda * b))
    have hEq :
        (Real.exp (lambda * b)) •
          (fun t : ℝ => Real.exp (-(lambda * (b - t))) • Q t) = H := by
      funext t
      exact hFactor t
    rw [hEq] at hScaled
    exact hScaled
  have hExpContinuous : Continuous (fun t : ℝ => Real.exp (lambda * t)) := by
    fun_prop
  have hProductContinuous :
      ContinuousOn (fun t : ℝ => Real.exp (lambda * t) • F t)
        (Set.Icc a b) :=
    hExpContinuous.continuousOn.smul hContinuous
  have hProductDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => Real.exp (lambda * z) • F z)
        (H t) t := by
    intro t ht
    exact thirdFullThreeBand_z3HeatIntegratingFactor_hasDerivAt244
      lambda t F Q (hODE t ht)
  have hFTC :
      (∫ t in a..b, H t) =
        Real.exp (lambda * b) • F b - Real.exp (lambda * a) • F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab hProductContinuous hProductDeriv hWeightedInt
  have hScaled := congrArg
    (fun z : ODEBand244 => Real.exp (-(lambda * b)) • z) hFTC
  have hCancel : Real.exp (-(lambda * b)) * Real.exp (lambda * b) = 1 := by
    rw [← Real.exp_add]
    have heq : -(lambda * b) + lambda * b = 0 := by ring
    rw [heq, Real.exp_zero]
  have hHeat :
      Real.exp (-(lambda * b)) * Real.exp (lambda * a) =
        Real.exp (-(lambda * (b - a))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [smul_sub, smul_smul, smul_smul, hCancel, hHeat, one_smul] at hScaled
  have hKernel :
      (∫ t in a..b, Real.exp (-(lambda * (b - t))) • Q t) =
      Real.exp (-(lambda * b)) • (∫ t in a..b, H t) := by
    dsimp only [H]
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t ht
    -- Expose the nested scalar multiplication beneath the two applications.
    change Real.exp (-(lambda * (b - t))) • Q t =
      Real.exp (-(lambda * b)) • (Real.exp (lambda * t) • Q t)
    rw [smul_smul, ← Real.exp_add]
    have heq : -(lambda * b) + lambda * t = -(lambda * (b - t)) := by
      ring
    rw [heq]
  calc
    F b = Real.exp (-(lambda * (b - a))) • F a +
          (F b - Real.exp (-(lambda * (b - a))) • F a) := by abel
    _ = Real.exp (-(lambda * (b - a))) • F a +
          Real.exp (-(lambda * b)) • (∫ t in a..b, H t) := by rw [hScaled]
    _ = _ := by rw [← hKernel]

/-- The selected Fourier coefficients of the ACTUAL complex Leray Galerkin
NS field satisfy the heat Duhamel formula once their true strong ODE holds.
The heat multiplier and source are exactly those of the earlier residual
module; no mild-equation hypothesis occurs here. -/
theorem thirdFullThreeBand_z3GalerkinStrongODE_Duhamel244
    (mu a b : ℝ) (hab : a ≤ b)
    (s : Finset ODEIndex244)
    (u : ℝ → ODEIndex244 → ODEBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hRetardedInt : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume a b) :
    ∀ n ∈ s,
      u b n = thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - a) n • u a n +
        ∫ t in a..b,
          thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n •
            thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n := by
  intro n hn
  let lambda : ℝ := mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2
  let F : ℝ → ODEBand244 := fun t => u t n
  let Q : ℝ → ODEBand244 := fun t =>
    thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n
  have hFactor (t : ℝ) :
      thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n =
        Real.exp (-(lambda * (b - t))) := by
    unfold thirdFullThreeBandZ3GalerkinHeatFactor244
    dsimp only [lambda]
    congr 1
    ring
  have hFactorA :
      thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - a) n =
        Real.exp (-(lambda * (b - a))) := hFactor a
  have hODE' : ∀ t ∈ Set.Ioo a b,
      HasDerivAt F ((-lambda) • F t + Q t) t := by
    intro t ht
    have hh := hODE n hn t ht
    change HasDerivAt F ((-lambda) • F t + Q t) t at hh
    exact hh
  have hRetarded' : IntervalIntegrable
      (fun t : ℝ => Real.exp (-(lambda * (b - t))) • Q t)
      volume a b := by
    simpa only [Q, hFactor] using hRetardedInt n hn
  have hD := thirdFullThreeBand_z3HeatODE_retardedDuhamel244
    lambda a b hab F Q (hContinuous n hn) hODE' hRetarded'
  simpa only [F, Q, hFactorA, hFactor] using hD

/-- No separately assumed Duhamel identity: the actual strong Galerkin
Navier--Stokes ODE plus its retarded-source integrability imply the prior
cutoff-independent quadratic local consistency bound. The upper Wiener
100-ball and temporal increment remain visible quantitative hypotheses. -/
theorem thirdFullThreeBand_z3GalerkinStrongODE_Residual25750000_100Ball244
    (mu a b : ℝ) (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset ODEIndex244)
    (u : ℝ → ODEIndex244 → ODEBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hRetardedInt : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume a b)
    (hHighBall : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100)
    (hIncrements : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) ≤
        51000 * (t - a)) :
    thirdFullThreeBandZ3GalerkinStepResidual244 mu (b - a)
        (Real.log (5 / 4 : ℝ)) s (u a) (u b) ≤
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * (b - a) ^ 2 := by
  have hDuhamel := thirdFullThreeBand_z3GalerkinStrongODE_Duhamel244
    mu a b hab s u hContinuous hODE hRetardedInt
  exact thirdFullThreeBand_z3GalerkinDuhamelResidual25750000_100Ball244
    mu a b hab hmu hmuMax s u hHighBall hIncrements
    hRetardedInt hDuhamel

/-- Both the Duhamel identity and the 51,000 Wiener increment are now derived
from one genuine strong Galerkin ODE. Coefficientwise integrability of the
true vector field on each initial subinterval remains explicit; it is not a
postulated increment bound. This reaches the cutoff-uniform O(h^2) residual
from ODE data and the high-radius 100-ball alone. -/
theorem thirdFullThreeBand_z3GalerkinStrongODE_fullResidual25750000_100Ball244
    (mu a b : ℝ) (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : Finset ODEIndex244)
    (u : ℝ → ODEIndex244 → ODEBand244)
    (hContinuous : ∀ n ∈ s,
      ContinuousOn (fun t : ℝ => u t n) (Set.Icc a b))
    (hODE : ∀ n ∈ s, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun z : ℝ => u z n)
        (thirdFullThreeBandZ3GalerkinNSField244 mu s (u t) n) t)
    (hFieldInt : ∀ t ∈ Set.Icc a b, ∀ n ∈ s,
      IntervalIntegrable
        (fun z : ℝ => thirdFullThreeBandZ3GalerkinNSField244 mu s (u z) n)
        volume a t)
    (hRetardedInt : ∀ n ∈ s,
      IntervalIntegrable (fun t : ℝ =>
        thirdFullThreeBandZ3GalerkinHeatFactor244 mu (b - t) n •
          thirdFullThreeBandZ3GalerkinQuadratic244 s s (u t) (u t) n)
        volume a b)
    (hHighBall : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) s (u t) ≤ 100) :
    thirdFullThreeBandZ3GalerkinStepResidual244 mu (b - a)
        (Real.log (5 / 4 : ℝ)) s (u a) (u b) ≤
      thirdFullThreeBandZ3GalerkinLocalConsistencyCap244 * (b - a) ^ 2 := by
  have hIncrements : ∀ t ∈ Set.Icc a b,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (3 / 2 : ℝ)) s (fun n => u t n - u a n) ≤
        51000 * (t - a) := by
    intro t ht
    have hContinuous' : ∀ n ∈ s,
        ContinuousOn (fun z : ℝ => u z n) (Set.Icc a t) := by
      intro n hn
      apply (hContinuous n hn).mono
      intro z hz
      exact ⟨hz.1, hz.2.trans ht.2⟩
    have hODE' : ∀ n ∈ s, ∀ z ∈ Set.Ioo a t,
        HasDerivAt (fun x : ℝ => u x n)
          (thirdFullThreeBandZ3GalerkinNSField244 mu s (u z) n) z := by
      intro n hn z hz
      exact hODE n hn z ⟨hz.1, lt_of_lt_of_le hz.2 ht.2⟩
    have hHigh' : ∀ z ∈ Set.Icc a t,
        thirdFullThreeBandZ3GalerkinWienerMass244
          (Real.log (9 / 5 : ℝ)) s (u z) ≤ 100 := by
      intro z hz
      exact hHighBall z ⟨hz.1, hz.2.trans ht.2⟩
    exact thirdFullThreeBand_z3GalerkinStrongODE_WienerIncrement51000_100Ball244
      mu a t ht.1 hmu hmuMax s u hContinuous' hODE' (hFieldInt t ht) hHigh'
  exact thirdFullThreeBand_z3GalerkinStrongODE_Residual25750000_100Ball244
    mu a b hab hmu hmuMax s u hContinuous hODE hRetardedInt
    hHighBall hIncrements

end
end PrimeTensor.FirstMonomialTriad
