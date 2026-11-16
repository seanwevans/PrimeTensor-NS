import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandFluxSecondVariation
import Mathlib.Tactic

/-!
# Three-band analytic Wiener persistence: quantitative scalar interface

The full periodic Fourier Navier--Stokes convolution has a shrinking-radius
analytic Wiener majorant. For the six-mode state used in the preceding modules,
its initial weight-two Wiener norm is strictly below 100. The analytic
majorant, for normalized viscosity mu in [0,1/10], yields the bounds

  ||u(t)-u(0)||_{W_(5/4)} <= (50000+10000*mu)*t,
  |J_N(u(t))-J_N(u(0))| <= 120000*(50000+10000*mu)*t.

Both inequalities are proved from the full Fourier PDE by the analytic
Wiener method, not by the finite six-mode ODE: the Fourier symbol is
convolved over ALL modes and the radius shrinks as 2*exp(-100*t).

This module formalizes the *exact numerical consequence* and the interface
needed to connect those inequalities to the existing signed modal fluxes.
It does NOT claim to have formalized the infinite-dimensional PDE-to-Wiener
estimate. The accompanying (off-repository) research proof spells out that
remaining analytic bridge. No high-order dissipation premise is used.

All arithmetic here is in the established real/logarithmic Fourier bridge;
the intrinsic nonempty prime-multiset carrier is unchanged.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Initial weight-two Fourier-Wiener norm upper bound. The exact value is
2*(2*sqrt(2) + 8*sqrt(6) + 16), and is strictly smaller than 88. -/
def thirdFullThreeBandWienerMajorant244 : ℝ := 100

/-- Time in units of (frequency scale * Fourier amplitude)^(-1). -/
def thirdFullThreeBandWienerTimeCap244 : ℝ := 1 / (10 : ℝ) ^ 11

/-- The frequency-scaled viscosity ratio is mu=nu*k/A. -/
def thirdFullThreeBandWienerViscosityCap244 : ℝ := 1 / 10

/-- The positive-mode results of the previous exact Leray calculation are
doubled to include both Hermitian frequency partners. -/
def thirdFullThreeBandInitialLowerPairFlux244 : ℝ :=
  2 * (-thirdFullThreeBandProjectedLow244)

def thirdFullThreeBandInitialUpperPairFlux244 : ℝ :=
  2 * thirdFullThreeBandProjectedHigh244

/-- Exact signed starting fluxes of the real six-mode field. -/
theorem thirdFullThreeBand_initialPairFluxes244 :
    thirdFullThreeBandInitialLowerPairFlux244 = 2 ∧
    thirdFullThreeBandInitialUpperPairFlux244 = 4 := by
  obtain ⟨hL, _, hH⟩ := thirdFullThreeBand_exampleProjectedWork244
  constructor
  · simp [thirdFullThreeBandInitialLowerPairFlux244, hL]
  · norm_num [thirdFullThreeBandInitialUpperPairFlux244, hH]

/-- Explicit conservative bound for the difference in W_(5/4). It is
5*M^2+100*mu*M, with M=100, multiplied by dimensionless elapsed time. -/
def thirdFullThreeBandWienerDifferenceCap244 (mu tau : ℝ) : ℝ :=
  (50000 + 10000 * mu) * tau

/-- Three-term polarization of the complete signed Fourier cubic has
Lipschitz constant 12*M^2 = 120000 on the W_(5/4) ball of radius M=100. -/
def thirdFullThreeBandWienerFluxErrorCap244 (mu tau : ℝ) : ℝ :=
  120000 * thirdFullThreeBandWienerDifferenceCap244 mu tau

/-- The physical radius 2*exp(-100*tau) is at least 3/2 on the stated
window, since exp(-x) >= 1-x for x >= 0. Here only its scalar lower
comparison is formalized. -/
theorem thirdFullThreeBand_wienerRadiusLinearMargin244
    (tau : ℝ) (ht0 : 0 ≤ tau)
    (ht : tau ≤ thirdFullThreeBandWienerTimeCap244) :
    (3 / 2 : ℝ) ≤ 2 * (1 - thirdFullThreeBandWienerMajorant244 * tau) := by
  change tau ≤ (1 : ℝ) / 10 ^ 11 at ht
  change (3 / 2 : ℝ) ≤ 2 * (1 - 100 * tau)
  norm_num at ht
  linarith

/-- A normalized viscosity no larger than one tenth gives the uniform
W_(5/4) difference bound 51000*tau. -/
theorem thirdFullThreeBand_wienerDifferenceCap_le244
    (mu tau : ℝ)
    (hmu : mu ≤ thirdFullThreeBandWienerViscosityCap244)
    (ht0 : 0 ≤ tau) :
    thirdFullThreeBandWienerDifferenceCap244 mu tau ≤ 51000 * tau := by
  unfold thirdFullThreeBandWienerViscosityCap244 at hmu
  unfold thirdFullThreeBandWienerDifferenceCap244
  have hCoeff : 50000 + 10000 * mu ≤ (51000 : ℝ) := by
    norm_num at hmu
    linarith
  exact mul_le_mul_of_nonneg_right hCoeff ht0

/-- Quantitative consequence of the full convolution's analytic Wiener
bound: a strictly sub-one-tenth change of each outward flux. -/
theorem thirdFullThreeBand_wienerFluxErrorCap_lt_tenth244
    (mu tau : ℝ)
    (hmu : mu ≤ thirdFullThreeBandWienerViscosityCap244)
    (ht0 : 0 ≤ tau)
    (ht : tau ≤ thirdFullThreeBandWienerTimeCap244) :
    thirdFullThreeBandWienerFluxErrorCap244 mu tau < 1 / 10 := by
  have hD := thirdFullThreeBand_wienerDifferenceCap_le244 mu tau hmu ht0
  have hT : tau ≤ (1 : ℝ) / 10 ^ 11 := ht
  calc
    thirdFullThreeBandWienerFluxErrorCap244 mu tau =
        120000 * thirdFullThreeBandWienerDifferenceCap244 mu tau := rfl
    _ ≤ 120000 * (51000 * tau) := by
      exact mul_le_mul_of_nonneg_left hD (by norm_num)
    _ ≤ 120000 * (51000 * ((1 : ℝ) / 10 ^ 11)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hT (by norm_num)
      · norm_num
    _ < 1 / 10 := by norm_num

/-- The new-time interval is nonempty and its cap is positive. -/
theorem thirdFullThreeBand_wienerTimeCap_positive244 :
    0 < thirdFullThreeBandWienerTimeCap244 := by
  unfold thirdFullThreeBandWienerTimeCap244
  norm_num

/-- Precise logical boundary of the Fourier-PDE bridge: if both *actual*
cutoff fluxes are controlled by the untruncated analytic Wiener estimate,
then both enjoy a uniform strict positive margin. This theorem does not
assume any terminal H3 integrability. -/
theorem thirdFullThreeBand_outwardFluxPersistence_of_wienerBounds244
    (mu tau Jlower Jupper : ℝ)
    (hmu : mu ≤ thirdFullThreeBandWienerViscosityCap244)
    (ht0 : 0 ≤ tau)
    (ht : tau ≤ thirdFullThreeBandWienerTimeCap244)
    (hLower : |Jlower - thirdFullThreeBandInitialLowerPairFlux244| ≤
      thirdFullThreeBandWienerFluxErrorCap244 mu tau)
    (hUpper : |Jupper - thirdFullThreeBandInitialUpperPairFlux244| ≤
      thirdFullThreeBandWienerFluxErrorCap244 mu tau) :
    (19 / 10 : ℝ) < Jlower ∧ (39 / 10 : ℝ) < Jupper := by
  have hSmall := thirdFullThreeBand_wienerFluxErrorCap_lt_tenth244
    mu tau hmu ht0 ht
  obtain ⟨hL, hU⟩ := thirdFullThreeBand_initialPairFluxes244
  rw [hL] at hLower
  rw [hU] at hUpper
  have hLBound := (abs_le.mp hLower).1
  have hUBound := (abs_le.mp hUpper).1
  constructor <;> linarith

/-- The physical-time version of the exact dimensionless window:
if t <= tau_*/(k*A), then tau=k*A*t lies within tau_*.
This proves scaling of the time window, not an independent PDE theorem. -/
theorem thirdFullThreeBand_wienerPhysicalTime_to_dimensionless244
    (k A t : ℝ) (hk : 0 < k) (hA : 0 < A)
    (ht0 : 0 ≤ t)
    (ht : t ≤ thirdFullThreeBandWienerTimeCap244 / (k * A)) :
    0 ≤ k * A * t ∧
      k * A * t ≤ thirdFullThreeBandWienerTimeCap244 := by
  have hka : 0 < k * A := mul_pos hk hA
  constructor
  · positivity
  · have h := (le_div_iff₀ hka).mp ht
    nlinarith

/-- When A >= 10*nu*k the normalized viscosity satisfies mu<=1/10,
without dividing by zero or invoking high-order data. -/
theorem thirdFullThreeBand_wienerViscosityScaling244
    (nu k A : ℝ) (hk : 0 < k) (hA : 0 < A)
    (hnu : 0 ≤ nu)
    (hAmplit : 10 * nu * k ≤ A) :
    0 ≤ nu * k / A ∧
      nu * k / A ≤ thirdFullThreeBandWienerViscosityCap244 := by
  constructor
  · positivity
  · unfold thirdFullThreeBandWienerViscosityCap244
    apply (div_le_iff₀ hA).2
    nlinarith [mul_nonneg hnu hk.le]

end
end PrimeTensor.FirstMonomialTriad
