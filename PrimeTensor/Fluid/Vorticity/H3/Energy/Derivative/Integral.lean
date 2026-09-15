import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating one canonical H³ square-energy integral

Every block of the canonical H³ energy is a finite sum of terms

    ∫ x, F(t,x)^2.

The remaining analytic issue is exchanging the time derivative with the
whole-space spatial integral.  This file isolates that operation in exactly
the form used by the H³ energy functional.

Mathlib's local dominated parametric-integral theorem gives the derivative once
we have

* local strong measurability of the square integrand;
* integrability at the base time;
* strong measurability of the candidate derivative;
* one locally uniform integrable dominator;
* the pointwise-in-space derivative identity.

No Navier--Stokes structure is used here.  The subsequent orderwise files only
have to provide these hypotheses for the concrete velocity derivatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The integral of the pointwise square derivative is exactly the previously
defined energy pairing. -/
theorem integral_two_mul_eq_spatialEnergyPairing
    (f ft : ScalarField3) :
    (∫ x : Point3, 2 * f x * ft x ∂volume)
      =
    spatialEnergyPairing f ft := by
  unfold spatialEnergyPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- Local dominated differentiation for one scalar square-energy term.

This is the reusable analytic engine for orders `0`, `1`, `2`, and `3`. -/
theorem hasDerivAt_spatialSquareEnergy_of_dominated
    {f ft : ℝ → ScalarField3}
    {t : ℝ}
    {S : Set ℝ}
    {bound : Point3 → ℝ}
    (hS : S ∈ 𝓝 t)
    (hMeas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (fun x : Point3 => (f s x) ^ 2)
          (volume : Measure Point3))
    (hInt :
      Integrable
        (fun x : Point3 => (f t x) ^ 2)
        (volume : Measure Point3))
    (hDerivMeas :
      AEStronglyMeasurable
        (fun x : Point3 => 2 * f t x * ft t x)
        (volume : Measure Point3))
    (hBound :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ S,
          ‖2 * f s x * ft s x‖ ≤ bound x)
    (hBoundInt :
      Integrable
        bound
        (volume : Measure Point3))
    (hDiff :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ S,
          HasDerivAt
            (fun r : ℝ => (f r x) ^ 2)
            (2 * f s x * ft s x)
            s) :
    HasDerivAt
      (fun s : ℝ => spatialSquareEnergy (f s))
      (spatialEnergyPairing (f t) (ft t))
      t := by
  let F : ℝ → Point3 → ℝ :=
    fun s x => (f s x) ^ 2

  let F' : ℝ → Point3 → ℝ :=
    fun s x => 2 * f s x * ft s x

  have hMain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F)
      (F' := F')
      (x₀ := t)
      (s := S)
      (bound := bound)
      (μ := (volume : Measure Point3))
      hS
      hMeas
      hInt
      hDerivMeas
      hBound
      hBoundInt
      hDiff

  have hRaw :
      HasDerivAt
        (fun s : ℝ => spatialSquareEnergy (f s))
        (∫ x : Point3, 2 * f t x * ft t x ∂volume)
        t := by
    simpa only [
      F,
      F',
      spatialSquareEnergy
    ] using hMain.2

  rw [integral_two_mul_eq_spatialEnergyPairing] at hRaw

  exact hRaw

/-- Squaring a scalar time path gives the pointwise derivative required by the
dominated-integral theorem. -/
theorem hasDerivAt_sq_two_mul
    {f ft : ℝ → ScalarField3}
    {s : ℝ}
    {x : Point3}
    (h :
      HasDerivAt
        (fun r : ℝ => f r x)
        (ft s x)
        s) :
    HasDerivAt
      (fun r : ℝ => (f r x) ^ 2)
      (2 * f s x * ft s x)
      s := by
  have hMul :
      HasDerivAt
        (fun r : ℝ => f r x * f r x)
        (ft s x * f s x + f s x * ft s x)
        s :=
    h.mul h

  have hValue :
      ft s x * f s x + f s x * ft s x
        =
      2 * f s x * ft s x := by
    ring

  simpa only [pow_two, hValue] using hMul

end

end Euclidean
end Bridge
end PrimeTensor
