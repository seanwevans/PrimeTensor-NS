import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.Integrability
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Compactly-supported quartic Landau integration by parts

For a positive radius `R`, define

    F_R = χ_R v,
    G   = g³.

The cutoff makes `F_R` compactly supported.  Since `F_R` is `C¹`, its Fréchet
derivative is also compactly supported after evaluation on any fixed
direction.  Consequently all three products required by Mathlib's
whole-space Fréchet integration-by-parts theorem are integrable:

    (D F_R · eₐ) G,
    F_R (D G · eₐ),
    F_R G.

This file applies that theorem in the coordinate direction `eₐ` and records

    ∫ F_R (D G · eₐ)
      =
    - ∫ (D F_R · eₐ) G.

The next increment expands the two Fréchet derivatives into the Landau
quantities `g`, `dg`, and the cutoff derivative, producing the explicit
boundary-error identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticCutoffIBP
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The compactly-supported factor used in the quartic IBP argument. -/
noncomputable def h3LandauQuarticCutoffFactor
    (R : ℝ)
    (hR : 0 < R)
    (v : ScalarField3) :
    ScalarField3 :=
  fun x : Point3 =>
    h3LandauCutoffBump R hR x * v x

/-- The cubic factor whose coordinate derivative gives the quartic Landau
terms. -/
noncomputable def h3LandauQuarticCube
    (g : ScalarField3) :
    ScalarField3 :=
  fun x : Point3 =>
    (g x) ^ 3

theorem h3LandauQuarticCutoffFactor_spatialC1
    {R : ℝ}
    (hR : 0 < R)
    {v : ScalarField3}
    (hv : SpatialC1 v) :
    SpatialC1
      (h3LandauQuarticCutoffFactor R hR v) := by
  unfold h3LandauQuarticCutoffFactor

  exact
    (h3LandauCutoffBump_spatialC1 hR).mul hv

theorem h3LandauQuarticCutoffFactor_hasCompactSupport
    {R : ℝ}
    (hR : 0 < R)
    (v : ScalarField3) :
    HasCompactSupport
      (h3LandauQuarticCutoffFactor R hR v) := by
  unfold h3LandauQuarticCutoffFactor

  exact
    (h3LandauCutoffBump_hasCompactSupport hR).mul_right

theorem h3LandauQuarticCube_spatialC1
    {g : ScalarField3}
    (hg : SpatialC1 g) :
    SpatialC1
      (h3LandauQuarticCube g) := by
  unfold h3LandauQuarticCube

  exact
    hg.pow 3

/-- Evaluating the Fréchet derivative of a compactly-supported scalar field on
a fixed direction preserves compact support. -/
theorem hasCompactSupport_fderiv_apply
    {f : ScalarField3}
    (hf : HasCompactSupport f)
    (w : Point3) :
    HasCompactSupport
      (fun x : Point3 =>
        fderiv ℝ f x w) := by
  refine
    HasCompactSupport.intro
      hf
      ?_

  intro x hx

  rw [← Function.notMem_support]

  intro hxSupport

  apply hx

  exact
    (tsupport_fderiv_apply_subset
      (𝕜 := ℝ)
      (f := f)
      w)
      (subset_tsupport _ hxSupport)

/-- The three integrability hypotheses required by the Fréchet
integration-by-parts theorem for `F_R = χ_R v` and `G = g³`. -/
theorem h3LandauQuarticCutoffIBP_integrable
    {R : ℝ}
    (hR : 0 < R)
    {v g : ScalarField3}
    (hv : SpatialC1 v)
    (hg : SpatialC1 g)
    (a : Axis Depth.three) :
    MeasureTheory.Integrable
        (fun x : Point3 =>
          fderiv ℝ
              (h3LandauQuarticCutoffFactor R hR v)
              x
              (axisDirection a)
            *
          h3LandauQuarticCube g x)
        volume
      ∧
    MeasureTheory.Integrable
        (fun x : Point3 =>
          h3LandauQuarticCutoffFactor R hR v x
            *
          fderiv ℝ
              (h3LandauQuarticCube g)
              x
              (axisDirection a))
        volume
      ∧
    MeasureTheory.Integrable
        (fun x : Point3 =>
          h3LandauQuarticCutoffFactor R hR v x
            *
          h3LandauQuarticCube g x)
        volume := by
  have hF1 :
      SpatialC1
        (h3LandauQuarticCutoffFactor R hR v) :=
    h3LandauQuarticCutoffFactor_spatialC1
      hR hv

  have hG1 :
      SpatialC1
        (h3LandauQuarticCube g) :=
    h3LandauQuarticCube_spatialC1
      hg

  have hFSupport :
      HasCompactSupport
        (h3LandauQuarticCutoffFactor R hR v) :=
    h3LandauQuarticCutoffFactor_hasCompactSupport
      hR v

  have hDFSupport :
      HasCompactSupport
        (fun x : Point3 =>
          fderiv ℝ
              (h3LandauQuarticCutoffFactor R hR v)
              x
              (axisDirection a)) :=
    hasCompactSupport_fderiv_apply
      hFSupport
      (axisDirection a)

  have hDFContinuous :
      Continuous
        (fun x : Point3 =>
          fderiv ℝ
              (h3LandauQuarticCutoffFactor R hR v)
              x
              (axisDirection a)) :=
    (
      hF1.continuous_fderiv
        (by norm_num)
    ).clm_apply
      continuous_const

  have hDGContinuous :
      Continuous
        (fun x : Point3 =>
          fderiv ℝ
              (h3LandauQuarticCube g)
              x
              (axisDirection a)) :=
    (
      hG1.continuous_fderiv
        (by norm_num)
    ).clm_apply
      continuous_const

  have hGContinuous :
      Continuous
        (h3LandauQuarticCube g) :=
    hG1.continuous

  have hFContinuous :
      Continuous
        (h3LandauQuarticCutoffFactor R hR v) :=
    hF1.continuous

  refine ⟨?_, ?_, ?_⟩

  · exact
      (hDFContinuous.mul hGContinuous).integrable_of_hasCompactSupport
        hDFSupport.mul_right

  · exact
      (hFContinuous.mul hDGContinuous).integrable_of_hasCompactSupport
        hFSupport.mul_right

  · exact
      (hFContinuous.mul hGContinuous).integrable_of_hasCompactSupport
        hFSupport.mul_right

/-- Raw compact-cutoff Fréchet integration by parts in the coordinate direction
`a`.  No derivative expansion is performed here. -/
theorem h3LandauQuarticCutoff_rawIBP
    {R : ℝ}
    (hR : 0 < R)
    {v g : ScalarField3}
    (hv : SpatialC1 v)
    (hg : SpatialC1 g)
    (a : Axis Depth.three) :
    (
      ∫ x : Point3,
        h3LandauQuarticCutoffFactor R hR v x
          *
        fderiv ℝ
            (h3LandauQuarticCube g)
            x
            (axisDirection a)
    )
      =
    -
    (
      ∫ x : Point3,
        fderiv ℝ
            (h3LandauQuarticCutoffFactor R hR v)
            x
            (axisDirection a)
          *
        h3LandauQuarticCube g x
    ) := by
  obtain
    ⟨hDFG, hFDG, hFG⟩ :=
    h3LandauQuarticCutoffIBP_integrable
      hR hv hg a

  exact
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume)
      (f := h3LandauQuarticCutoffFactor R hR v)
      (g := h3LandauQuarticCube g)
      (v := axisDirection a)
      hDFG
      hFDG
      hFG
      (fun x hx =>
        (
          h3LandauQuarticCutoffFactor_spatialC1
            hR hv
        ).differentiable_one.differentiableAt)
      (fun x hx =>
        (
          h3LandauQuarticCube_spatialC1
            hg
        ).differentiable_one.differentiableAt)

end

end Euclidean
end Bridge
end PrimeTensor
