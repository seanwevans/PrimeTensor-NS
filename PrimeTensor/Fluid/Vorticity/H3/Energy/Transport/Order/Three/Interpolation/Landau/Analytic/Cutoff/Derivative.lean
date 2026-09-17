import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Cutoff
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Fréchet derivative of the Landau cutoff approximation

For the smooth compactly-supported approximation

    g_R(x) = χ_R(x) g(x),

the next whole-space Sobolev step needs the ordinary Fréchet Leibniz rule

    Dg_R = χ_R Dg + g Dχ_R.

This file records that identity on PrimeTensor's physical `Point3`, derives the
corresponding pointwise norm estimate

    ‖Dg_R(x)‖ ≤ ‖Dg(x)‖ + |g(x)| ‖Dχ_R(x)‖,

and proves that for each fixed positive radius the cutoff derivative is
globally bounded.

The radius dependence of that derivative bound is intentionally left to the
next increment.  The cutoff family was constructed by scaling one fixed bump,
so the next file can sharpen the present existential bound to `C / R`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function
open scoped Topology ContDiff NNReal

noncomputable section

noncomputable local instance axisFintypeH3LandauCutoffDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact Fréchet Leibniz rule for the smooth cutoff approximation. -/
theorem fderiv_h3LandauCutoffField
    {R : ℝ}
    (hR : 0 < R)
    {g : ScalarField3}
    (hg : SpatialC1 g)
    (x : Point3) :
    fderiv ℝ
        (h3LandauCutoffField R hR g)
        x
      =
    (h3LandauCutoffBump R hR x)
        •
      fderiv ℝ g x
      +
    (g x)
        •
      fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump R hR y)
        x := by
  unfold h3LandauCutoffField

  exact
    fderiv_fun_mul
      ((h3LandauCutoffBump_spatialC1 hR).differentiable_one.differentiableAt)
      (hg.differentiable_one.differentiableAt)

/-- Pointwise derivative estimate for the cutoff approximation.  The cutoff
factor itself costs no constant because `0 ≤ χ_R ≤ 1`. -/
theorem norm_fderiv_h3LandauCutoffField_le
    {R : ℝ}
    (hR : 0 < R)
    {g : ScalarField3}
    (hg : SpatialC1 g)
    (x : Point3) :
    ‖fderiv ℝ
        (h3LandauCutoffField R hR g)
        x‖
      ≤
    ‖fderiv ℝ g x‖
      +
    |g x|
      *
    ‖fderiv ℝ
        (fun y : Point3 =>
          h3LandauCutoffBump R hR y)
        x‖ := by
  rw [
    fderiv_h3LandauCutoffField
      hR hg x
  ]

  have hχ0 :
      0 ≤ h3LandauCutoffBump R hR x :=
    h3LandauCutoffBump_nonneg hR x

  have hχ1 :
      h3LandauCutoffBump R hR x ≤ 1 :=
    h3LandauCutoffBump_le_one hR x

  calc
    ‖(
      (h3LandauCutoffBump R hR x) • fderiv ℝ g x
        +
      (g x) •
        fderiv ℝ
          (fun y : Point3 => h3LandauCutoffBump R hR y)
          x
    )‖
        ≤
      ‖((h3LandauCutoffBump R hR x) • fderiv ℝ g x)‖
        +
      ‖((g x) •
        fderiv ℝ
          (fun y : Point3 => h3LandauCutoffBump R hR y)
          x)‖ :=
      norm_add_le _ _

    _ =
      |h3LandauCutoffBump R hR x|
          *
        ‖fderiv ℝ g x‖
        +
      |g x|
          *
        ‖fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x‖ := by
      simp only [
        norm_smul,
        Real.norm_eq_abs
      ]

    _ =
      (h3LandauCutoffBump R hR x)
          *
        ‖fderiv ℝ g x‖
        +
      |g x|
          *
        ‖fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x‖ := by
      rw [abs_of_nonneg hχ0]

    _ ≤
      ‖fderiv ℝ g x‖
        +
      |g x|
        *
      ‖fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x‖ := by
      have hDNonneg :
          0 ≤ ‖fderiv ℝ g x‖ :=
        norm_nonneg _

      nlinarith

/-- Every fixed positive-radius cutoff is globally Lipschitz.  Compact support
plus `C¹` regularity is enough for this qualitative bound. -/
theorem exists_lipschitzWith_h3LandauCutoffBump
    {R : ℝ}
    (hR : 0 < R) :
    ∃ C : ℝ≥0,
      LipschitzWith C
        (fun x : Point3 =>
          h3LandauCutoffBump R hR x) := by
  exact
    ContDiff.lipschitzWith_of_hasCompactSupport
      (h3LandauCutoffBump_hasCompactSupport hR)
      (h3LandauCutoffBump_spatialC1 hR)
      (by norm_num)

/-- Consequently the Fréchet derivative of every fixed cutoff has a global
operator-norm bound. -/
theorem exists_norm_fderiv_h3LandauCutoffBump_le
    {R : ℝ}
    (hR : 0 < R) :
    ∃ C : ℝ≥0,
      ∀ x : Point3,
        ‖fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x‖
          ≤
        (C : ℝ) := by
  obtain ⟨C, hLip⟩ :=
    exists_lipschitzWith_h3LandauCutoffBump hR

  refine ⟨C, ?_⟩

  intro x

  exact
    norm_fderiv_le_of_lipschitz
      ℝ
      hLip

end

end Euclidean
end Bridge
end PrimeTensor
