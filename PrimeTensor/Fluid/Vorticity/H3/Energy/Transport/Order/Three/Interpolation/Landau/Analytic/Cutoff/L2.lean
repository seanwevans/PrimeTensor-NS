import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Cutoff.Scaling

/-!
# L² derivative control for the Landau cutoff approximation

Let

    g_R = χ_R g.

For `g ∈ L²` with `Dg ∈ L²`, the cutoff derivative estimate gives

    ‖Dg_R(x)‖
      ≤ ‖Dg(x)‖ + |g(x)| ‖Dχ_R(x)‖
      ≤ ‖Dg(x)‖ + (C / R) |g(x)|.

The right-hand side belongs to `L²`, so `Dg_R ∈ L²`.

Combining this with the compact-support Sobolev theorem already specialized to
`Point3` yields

    g_R ∈ L⁶

for every positive radius.

This is the last local/cutoff estimate needed before passing `R → ∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauCutoffL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The Fréchet derivative of every positive-radius cutoff approximation is in
`L²` whenever both the original field and its Fréchet derivative are in `L²`. -/
theorem memLp_two_fderiv_h3LandauCutoffField
    {R : ℝ}
    (hR : 0 < R)
    {g : ScalarField3}
    (hC1 : SpatialC1 g)
    (hg2 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 2)
        volume)
    (hDg2 :
      MeasureTheory.MemLp
        (fun x : Point3 => fderiv ℝ g x)
        (ENNReal.ofReal 2)
        volume) :
    MeasureTheory.MemLp
      (fun x : Point3 =>
        fderiv ℝ
          (h3LandauCutoffField R hR g)
          x)
      (ENNReal.ofReal 2)
      volume := by
  obtain ⟨C, hCutoffDeriv⟩ :=
    exists_uniform_norm_fderiv_h3LandauCutoffBump_le_div

  have hDgNorm :
      MeasureTheory.MemLp
        (fun x : Point3 =>
          ‖fderiv ℝ g x‖)
        (ENNReal.ofReal 2)
        volume :=
    hDg2.norm

  have hgAbs :
      MeasureTheory.MemLp
        (fun x : Point3 =>
          |g x|)
        (ENNReal.ofReal 2)
        volume := by
    simpa [Real.norm_eq_abs] using
      hg2.norm

  have hgScaled :
      MeasureTheory.MemLp
        (fun x : Point3 =>
          ((C : ℝ) / R) * |g x|)
        (ENNReal.ofReal 2)
        volume := by
    exact
      hgAbs.const_mul ((C : ℝ) / R)

  let majorant : Point3 → ℝ :=
    (fun x : Point3 =>
      ‖fderiv ℝ g x‖)
      +
    (fun x : Point3 =>
      ((C : ℝ) / R) * |g x|)

  have hMajorant :
      MeasureTheory.MemLp
        majorant
        (ENNReal.ofReal 2)
        volume := by
    dsimp [majorant]
    exact
      hDgNorm.add hgScaled

  have hCutoffC1 :
      SpatialC1
        (h3LandauCutoffField R hR g) :=
    h3LandauCutoffField_spatialC1
      hR hC1

  have hFDerivMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : Point3 =>
          fderiv ℝ
            (h3LandauCutoffField R hR g)
            x)
        volume :=
    (
      hCutoffC1.continuous_fderiv
        (by norm_num)
    ).aestronglyMeasurable

  apply
    hMajorant.mono
      hFDerivMeas

  filter_upwards with x

  have hProductBound :=
    norm_fderiv_h3LandauCutoffField_le
      hR hC1 x

  have hCutoffBound :
      ‖fderiv ℝ
          (fun y : Point3 =>
            h3LandauCutoffBump R hR y)
          x‖
        ≤
      (C : ℝ) / R :=
    hCutoffDeriv
      hR x

  have hAbsNonneg :
      0 ≤ |g x| :=
    abs_nonneg _

  have hError :
      |g x|
          *
        ‖fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x‖
        ≤
      ((C : ℝ) / R) * |g x| := by
    calc
      |g x|
          *
        ‖fderiv ℝ
            (fun y : Point3 =>
              h3LandauCutoffBump R hR y)
            x‖
          ≤
        |g x| * ((C : ℝ) / R) := by
            exact
              mul_le_mul_of_nonneg_left
                hCutoffBound
                hAbsNonneg

      _ =
        ((C : ℝ) / R) * |g x| := by
          exact mul_comm _ _

  have hCoeffNonneg :
      0 ≤ (C : ℝ) / R := by
    exact
      div_nonneg
        C.coe_nonneg
        hR.le

  have hMajorantNonneg :
      0 ≤ majorant x := by
    dsimp [majorant]

    exact
      add_nonneg
        (norm_nonneg _)
        (mul_nonneg
          hCoeffNonneg
          hAbsNonneg)

  have hPointwise :
      ‖fderiv ℝ
          (h3LandauCutoffField R hR g)
          x‖
        ≤
      majorant x := by
    dsimp [majorant]

    exact
      hProductBound.trans
        (add_le_add_right
          hError
          ‖fderiv ℝ g x‖)

  simpa [
    Real.norm_eq_abs,
    abs_of_nonneg hMajorantNonneg
  ] using
    hPointwise

/-- Every positive-radius cutoff approximation belongs to `L⁶`. -/
theorem memLp_six_h3LandauCutoffField
    {R : ℝ}
    (hR : 0 < R)
    {g : ScalarField3}
    (hC1 : SpatialC1 g)
    (hg2 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 2)
        volume)
    (hDg2 :
      MeasureTheory.MemLp
        (fun x : Point3 => fderiv ℝ g x)
        (ENNReal.ofReal 2)
        volume) :
    MeasureTheory.MemLp
      (h3LandauCutoffField R hR g)
      (ENNReal.ofReal 6)
      volume := by
  exact
    memLp_six_of_spatialC1_of_hasCompactSupport_of_fderiv_memLp_two
      (h3LandauCutoffField_spatialC1 hR hC1)
      (h3LandauCutoffField_hasCompactSupport hR g)
      (memLp_two_fderiv_h3LandauCutoffField
        hR
        hC1
        hg2
        hDg2)

end

end Euclidean
end Bridge
end PrimeTensor
