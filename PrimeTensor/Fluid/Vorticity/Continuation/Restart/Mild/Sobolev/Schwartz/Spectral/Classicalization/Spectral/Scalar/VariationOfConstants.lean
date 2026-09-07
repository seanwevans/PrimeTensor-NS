import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classicalization: scalar spectral variation of constants

The remaining old-branch evolution frontier contains a restarted heat--Leray
mild identity.  Before connecting the concrete preterminal Navier--Stokes PDE
to that Banach-valued identity, isolate the scalar Fourier-mode calculus that
drives variation of constants.

For a complex path `F` satisfying the real-time ODE

    F'(s) = -a • F(s) - G(s),

the integrating factor `exp(a s)` has derivative

    d/ds [exp(a s) • F(s)]
      = - exp(a s) • G(s).

The second theorem integrates this identity on `[0,t]` with Mathlib's
Banach-valued fundamental theorem of calculus.

This file is deliberately independent of the preterminal path representation.
The next bridge can instantiate `a` with the heat frequency generator and `G`
with the Leray-projected nonlinear forcing of one Fourier coordinate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/- Complex-valued paths are differentiated over real time.  This is the same
restriction-of-scalars instance used by the selected time-derivative stack. -/
attribute [local instance 1100] NormedSpace.complexToReal

/-- The integrating-factor derivative for one complex scalar heat mode. -/
theorem h3ComplexHeatIntegratingFactor_hasDerivAt
    {a s : ℝ}
    {F G : ℝ → ℂ}
    (hODE :
      HasDerivAt
        F
        ((-a) • F s - G s)
        s) :
    HasDerivAt
      (fun r : ℝ =>
        Real.exp (a * r) • F r)
      (-(Real.exp (a * s) • G s))
      s := by
  have hLinear :
      HasDerivAt
        (fun r : ℝ => a * r)
        a
        s := by
    simpa using
      (hasDerivAt_const_mul (x := s) a)

  have hExp :
      HasDerivAt
        (fun r : ℝ => Real.exp (a * r))
        (Real.exp (a * s) * a)
        s :=
    hLinear.exp

  have hProduct :=
    hExp.smul hODE

  change
    HasDerivAt
      ((fun r : ℝ => Real.exp (a * r)) • F)
      (-(Real.exp (a * s) • G s))
      s

  have hValue :
      Real.exp (a * s) • ((-a) • F s - G s)
          +
        (Real.exp (a * s) * a) • F s
        =
      -(Real.exp (a * s) • G s) := by
    rw [smul_sub, smul_smul]

    have hCoeff :
        Real.exp (a * s) * (-a)
          =
        -(Real.exp (a * s) * a) := by
      ring

    rw [hCoeff, neg_smul]
    abel

  rw [hValue] at hProduct
  exact hProduct

/-- Fundamental-theorem-of-calculus form of scalar heat variation of
constants.

The only analytic input beyond the pointwise ODE is integrability of the
weighted forcing.  Continuity of `F` supplies continuity of the integrating
factor product. -/
theorem h3ComplexHeatIntegratingFactor_intervalIntegral
    {a t : ℝ}
    (ht : 0 ≤ t)
    (F G : ℝ → ℂ)
    (hFContinuous :
      ContinuousOn F (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        HasDerivAt
          F
          ((-a) • F s - G s)
          s)
    (hWeightedForcing :
      IntervalIntegrable
        (fun s : ℝ =>
          Real.exp (a * s) • G s)
        volume
        0
        t) :
    (∫ s in (0 : ℝ)..t,
      -(Real.exp (a * s) • G s))
      =
    Real.exp (a * t) • F t - F 0 := by
  have hExpContinuous :
      Continuous
        (fun s : ℝ =>
          Real.exp (a * s)) := by
    fun_prop

  have hProductContinuous :
      ContinuousOn
        (fun s : ℝ =>
          Real.exp (a * s) • F s)
        (Set.Icc (0 : ℝ) t) := by
    exact
      hExpContinuous.continuousOn.smul
        hFContinuous

  have hProductDeriv :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        HasDerivAt
          (fun r : ℝ =>
            Real.exp (a * r) • F r)
          (-(Real.exp (a * s) • G s))
          s := by
    intro s hs
    exact
      h3ComplexHeatIntegratingFactor_hasDerivAt
        (hODE s hs)

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      ht
      hProductContinuous
      hProductDeriv
      hWeightedForcing.neg

  simpa using hFTC

end

end Euclidean
end Bridge
end PrimeTensor
