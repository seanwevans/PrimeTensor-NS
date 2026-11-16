import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandGeneratedModesFluxSlope
import Mathlib.Tactic

/-!
# Second temporal variation of the exact three-band nonlinear flux

The independent exact Gaussian-rational convolution audit computes the
second time derivatives of the actual unforced Navier--Stokes Fourier
fluxes at the original six-mode datum, retaining every first- and
second-generation Fourier mode.  The expressions are polynomial in
viscosity nu, wavevector scale k, and Fourier amplitude A:

  Jlow''(0) = -1792/425*k^3*A^5 + 1148/5*nu*k^4*A^4
               + 512*nu^2*k^5*A^3;
  Jhigh''(0) = -615688/12325*k^3*A^5 - 728/5*nu*k^4*A^4
               + 1024*nu^2*k^5*A^3.

The audit also verifies both expressions from the third derivative of the
kinetic-energy ledger and from exact polynomial interpolation of the cubic
Fourier flux along the second-order PDE jet. The formal declarations below
prove the scalar factorization and sign consequences of these audited
coefficients, NOT a new PDE-to-ODE bridge or quantitative persistence window.

In particular, for nu,k>0 and A=10*nu*k, the outer nonlinear flux is
initially increasing but its second derivative is strictly negative.
The lower flux is initially decreasing and has positive curvature.

All additive operations in this file are in the existing real Fourier
bridge; no addition, subtraction, or zero is introduced into PrimeMultiset.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Full-convolution second derivative of outward flux through 3*k/2,
recorded as an exact scalar polynomial from the independent audit. -/
def thirdFullThreeBandLowerFluxCurvature244 (nu k A : ℝ) : ℝ :=
  -(1792 / 425) * k ^ 3 * A ^ 5 +
    (1148 / 5) * nu * k ^ 4 * A ^ 4 +
    512 * nu ^ 2 * k ^ 5 * A ^ 3

/-- Full-convolution second derivative of outward flux through 3*k,
including second-generation modes and the temporal Leray feedback. -/
def thirdFullThreeBandUpperFluxCurvature244 (nu k A : ℝ) : ℝ :=
  -(615688 / 12325) * k ^ 3 * A ^ 5 -
    (728 / 5) * nu * k ^ 4 * A ^ 4 +
    1024 * nu ^ 2 * k ^ 5 * A ^ 3

/-- Dimensionless lower-curvature coefficient, with r=nu*k/A.
This is a polynomial; no division by A is introduced in its definition. -/
def thirdFullThreeBandLowerCurvatureShape244 (r : ℝ) : ℝ :=
  -(1792 / 425) + (1148 / 5) * r + 512 * r ^ 2

/-- Dimensionless upper-curvature coefficient. -/
def thirdFullThreeBandUpperCurvatureShape244 (r : ℝ) : ℝ :=
  -(615688 / 12325) - (728 / 5) * r + 1024 * r ^ 2

/-- Both second temporal variations have the exact scale
k^3*A^3 times a quadratic in A and nu*k. -/
theorem thirdFullThreeBand_curvatures_factor244 (nu k A : ℝ) :
    thirdFullThreeBandLowerFluxCurvature244 nu k A =
      k ^ 3 * A ^ 3 *
        (-(1792 / 425) * A ^ 2 +
          (1148 / 5) * (nu * k) * A + 512 * (nu * k) ^ 2) ∧
    thirdFullThreeBandUpperFluxCurvature244 nu k A =
      k ^ 3 * A ^ 3 *
        (-(615688 / 12325) * A ^ 2 -
          (728 / 5) * (nu * k) * A + 1024 * (nu * k) ^ 2) := by
  constructor
  · unfold thirdFullThreeBandLowerFluxCurvature244
    ring
  · unfold thirdFullThreeBandUpperFluxCurvature244
    ring

/-- In the inviscid limit both outward fluxes bend down at the
initial instant, even though the upper flux has positive first slope. -/
theorem thirdFullThreeBand_inviscidCurvatures_negative244
    (k A : ℝ) (hk : 0 < k) (hA : 0 < A) :
    thirdFullThreeBandLowerFluxCurvature244 0 k A < 0 ∧
    thirdFullThreeBandUpperFluxCurvature244 0 k A < 0 := by
  constructor
  · unfold thirdFullThreeBandLowerFluxCurvature244
    have hp : (0 : ℝ) < (1792 / 425) * k ^ 3 * A ^ 5 := by
      positivity
    nlinarith
  · unfold thirdFullThreeBandUpperFluxCurvature244
    have hp : (0 : ℝ) < (615688 / 12325) * k ^ 3 * A ^ 5 := by
      positivity
    nlinarith

/-- Exact curvature values at the amplitude A=10*nu*k, where the
upper first derivative is already known to be strictly positive. -/
theorem thirdFullThreeBand_curvatures_at_ten_formula244 (nu k : ℝ) :
    thirdFullThreeBandLowerFluxCurvature244 nu k (10 * nu * k) =
      (40568000 / 17) * nu ^ 5 * k ^ 8 ∧
    thirdFullThreeBandUpperFluxCurvature244 nu k (10 * nu * k) =
      -(2675728000 / 493) * nu ^ 5 * k ^ 8 := by
  constructor
  · unfold thirdFullThreeBandLowerFluxCurvature244
    ring
  · unfold thirdFullThreeBandUpperFluxCurvature244
    ring

/-- At a positive viscosity/frequency and the amplitude ten times
nu*k, the lower flux bends up but the upper flux bends down. -/
theorem thirdFullThreeBand_curvatures_at_ten_signs244
    (nu k : ℝ) (hnu : 0 < nu) (hk : 0 < k) :
    0 < thirdFullThreeBandLowerFluxCurvature244 nu k (10 * nu * k) ∧
    thirdFullThreeBandUpperFluxCurvature244 nu k (10 * nu * k) < 0 := by
  obtain ⟨hLow, hHigh⟩ :=
    thirdFullThreeBand_curvatures_at_ten_formula244 nu k
  rw [hLow, hHigh]
  constructor
  · positivity
  · have hp : (0 : ℝ) < (2675728000 / 493) * nu ^ 5 * k ^ 8 := by
      positivity
    linarith

/-- A fully quantitative *initial-jet* sign contrast: at A=10*nu*k
both nonlinear cutoff fluxes are outward, the lower is slowing in
magnitude while bending up, and the upper is rising while bending down.
No persistence-time bound is asserted. -/
theorem thirdFullThreeBand_opposedFluxCurvatures_at_ten244
    (nu k : ℝ) (hnu : 0 < nu) (hk : 0 < k) :
    thirdFullThreeBandLowerFluxSlope244 nu k (10 * nu * k) < 0 ∧
    0 < thirdFullThreeBandLowerFluxCurvature244 nu k (10 * nu * k) ∧
    0 < thirdFullThreeBandUpperFluxSlope244 nu k (10 * nu * k) ∧
    thirdFullThreeBandUpperFluxCurvature244 nu k (10 * nu * k) < 0 := by
  have hA : 0 < 10 * nu * k := by positivity
  obtain ⟨hLow, hHigh⟩ :=
    thirdFullThreeBand_curvatures_at_ten_signs244 nu k hnu hk
  exact ⟨thirdFullThreeBand_lowerFluxSlope_negative244
    nu k (10 * nu * k) hnu.le hk hA,
    hLow,
    thirdFullThreeBand_upperFluxSlope_positive_at_ten244 nu k hnu hk,
    hHigh⟩

end
end PrimeTensor.FirstMonomialTriad
