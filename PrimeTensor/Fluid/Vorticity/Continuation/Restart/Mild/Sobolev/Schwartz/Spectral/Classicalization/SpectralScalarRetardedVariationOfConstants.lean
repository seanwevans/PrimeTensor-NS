import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralScalarVariationOfConstants

/-!
# Classicalization: retarded scalar spectral variation of constants

`SpectralScalarVariationOfConstants` proves the integrating-factor FTC identity

    ∫₀ᵗ -e^{as} G(s) ds = e^{at} F(t) - F(0).

This file rewrites that identity into the retarded heat-kernel form used by the
spectral mild equation,

    F(t)
      =
    e^{-at} F(0)
      -
    ∫₀ᵗ e^{-a(t-s)} G(s) ds.

The proof is split into two small algebraic bridges:

1. cancel the terminal integrating factor `e^{at}`;
2. move the constant `e^{-at}` through the interval integral and combine the
   exponentials.

The next step can instantiate `a` with the concrete H³ heat frequency
generator and `G` with the Leray-projected nonlinear forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

/-- Cancel the terminal integrating factor in the FTC identity. -/
theorem h3ComplexHeatVariationOfConstants_factored
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
    F t
      =
    Real.exp (-(a * t)) • F 0
      +
    Real.exp (-(a * t)) •
      (∫ s in (0 : ℝ)..t,
        -(Real.exp (a * s) • G s)) := by
  have hFTC :=
    h3ComplexHeatIntegratingFactor_intervalIntegral
      ht F G hFContinuous hODE hWeightedForcing

  have hScaled :=
    congrArg
      (fun z : ℂ =>
        Real.exp (-(a * t)) • z)
      hFTC

  have hCancel :
      Real.exp (-(a * t)) * Real.exp (a * t)
        =
      1 := by
    calc
      Real.exp (-(a * t)) * Real.exp (a * t)
          =
        Real.exp (-(a * t) + a * t) := by
          rw [Real.exp_add]
      _ = 1 := by
        simp

  rw [smul_sub, smul_smul, hCancel, one_smul] at hScaled

  calc
    F t
        =
      (F t - Real.exp (-(a * t)) • F 0)
        +
      Real.exp (-(a * t)) • F 0 := by
          abel
    _ =
      Real.exp (-(a * t)) •
          (∫ s in (0 : ℝ)..t,
            -(Real.exp (a * s) • G s))
        +
      Real.exp (-(a * t)) • F 0 := by
          rw [← hScaled]
    _ =
      Real.exp (-(a * t)) • F 0
        +
      Real.exp (-(a * t)) •
        (∫ s in (0 : ℝ)..t,
          -(Real.exp (a * s) • G s)) := by
          abel

/-- Moving the terminal factor through the integral turns the weighted
integrating-factor integrand into the retarded heat kernel. -/
theorem h3ComplexHeatRetardedKernel_neg_intervalIntegral_eq_scaledWeightedNeg
    (a t : ℝ)
    (G : ℝ → ℂ) :
    (∫ s in (0 : ℝ)..t,
      -(Real.exp (-(a * (t - s))) • G s))
      =
    Real.exp (-(a * t)) •
      (∫ s in (0 : ℝ)..t,
        -(Real.exp (a * s) • G s)) := by
  rw [← intervalIntegral.integral_smul]

  apply intervalIntegral.integral_congr

  intro s hs

  change
    -(Real.exp (-(a * (t - s))) • G s)
      =
    Real.exp (-(a * t)) •
      -(Real.exp (a * s) • G s)

  rw [smul_neg, smul_smul]

  have hExp :
      Real.exp (-(a * t)) * Real.exp (a * s)
        =
      Real.exp (-(a * (t - s))) := by
    calc
      Real.exp (-(a * t)) * Real.exp (a * s)
          =
        Real.exp (-(a * t) + a * s) := by
          rw [Real.exp_add]
      _ =
        Real.exp (-(a * (t - s))) := by
          congr 1
          ring

  rw [hExp]

/-- Scalar retarded heat variation of constants in exactly the sign convention
of the Navier--Stokes mild equation. -/
theorem h3ComplexHeatVariationOfConstants_retarded
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
    F t
      =
    Real.exp (-(a * t)) • F 0
      -
    ∫ s in (0 : ℝ)..t,
      Real.exp (-(a * (t - s))) • G s := by
  have hFactored :=
    h3ComplexHeatVariationOfConstants_factored
      ht F G hFContinuous hODE hWeightedForcing

  have hKernel :=
    h3ComplexHeatRetardedKernel_neg_intervalIntegral_eq_scaledWeightedNeg
      a t G

  rw [← hKernel] at hFactored
  rw [intervalIntegral.integral_neg] at hFactored

  simpa only [sub_eq_add_neg] using hFactored

end

end Euclidean
end Bridge
end PrimeTensor
