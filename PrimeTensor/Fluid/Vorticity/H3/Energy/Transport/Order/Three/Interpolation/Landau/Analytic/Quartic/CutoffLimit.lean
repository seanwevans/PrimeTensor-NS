import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.BoundaryLimit

/-!
# Removing the expanding Landau cutoff from integrable scalar fields

For the canonical radii

    Rₙ = n + 1,

the smooth Landau cutoff is eventually exactly one at every fixed physical
point.  Since `0 ≤ χ_R ≤ 1`, every integrable scalar field supplies its own
dominating function.

This file packages the resulting dominated-convergence statement

    ∫ χ_{Rₙ} f → ∫ f.

The quartic integration-by-parts closure will use it twice: once with `f = g⁴`
and once with `f = v g² dg`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticCutoffLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical expanding positive radius used to remove the quartic cutoff. -/
def h3LandauQuarticRadius
    (n : ℕ) : ℝ :=
  (n : ℝ) + 1

theorem h3LandauQuarticRadius_pos
    (n : ℕ) :
    0 < h3LandauQuarticRadius n := by
  unfold h3LandauQuarticRadius
  positivity

/-- Weighted integral along the canonical expanding cutoff sequence. -/
noncomputable def h3LandauQuarticCutoffIntegral
    (f : ScalarField3)
    (n : ℕ) : ℝ :=
  ∫ x : Point3,
    h3LandauCutoffBump
        (h3LandauQuarticRadius n)
        (h3LandauQuarticRadius_pos n)
        x
      *
    f x

/-- Every fixed point is eventually inside the unit region of the expanding
canonical cutoff. -/
theorem eventually_h3LandauQuarticCutoffBump_eq_one
    (x : Point3) :
    ∀ᶠ n : ℕ in atTop,
      h3LandauCutoffBump
          (h3LandauQuarticRadius n)
          (h3LandauQuarticRadius_pos n)
          x
        =
      1 := by
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ‖x‖

  filter_upwards [
    eventually_ge_atTop N
  ] with n hn

  apply
    h3LandauCutoffBump_eq_one_of_norm_le
      (h3LandauQuarticRadius_pos n)

  calc
    ‖x‖
        ≤
      (N : ℝ) :=
        le_of_lt hN

    _ ≤
      (n : ℝ) := by
        exact_mod_cast hn

    _ ≤
      h3LandauQuarticRadius n := by
        unfold h3LandauQuarticRadius
        linarith

/-- Dominated convergence removes the canonical expanding cutoff from any
integrable real scalar field. -/
theorem tendsto_h3LandauQuarticCutoffIntegral
    {f : ScalarField3}
    (hf : MeasureTheory.Integrable f volume) :
    Tendsto
      (h3LandauQuarticCutoffIntegral f)
      atTop
      (𝓝
        (
          ∫ x : Point3,
            f x
        )) := by
  let F : ℕ → Point3 → ℝ :=
    fun n x =>
      h3LandauCutoffBump
          (h3LandauQuarticRadius n)
          (h3LandauQuarticRadius_pos n)
          x
        *
      f x

  have hFMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (F n)
          volume := by
    intro n
    dsimp [F]

    exact
      (
        (h3LandauCutoffBump_spatialC1
          (h3LandauQuarticRadius_pos n)).continuous.aestronglyMeasurable
      ).mul
        hf.aestronglyMeasurable

  have hBound :
      ∀ n : ℕ,
        ∀ᵐ x : Point3 ∂volume,
          ‖F n x‖
            ≤
          ‖f x‖ := by
    intro n

    exact
      Filter.Eventually.of_forall
        (fun x => by
          have hNonneg :=
            h3LandauCutoffBump_nonneg
              (h3LandauQuarticRadius_pos n)
              x

          have hLeOne :=
            h3LandauCutoffBump_le_one
              (h3LandauQuarticRadius_pos n)
              x

          dsimp [F]

          rw [
            abs_mul,
            abs_of_nonneg hNonneg
          ]

          exact
            mul_le_of_le_one_left
              (abs_nonneg (f x))
              hLeOne)

  have hPointwise :
      ∀ᵐ x : Point3 ∂volume,
        Tendsto
          (fun n : ℕ =>
            F n x)
          atTop
          (𝓝 (f x)) := by
    filter_upwards with x

    have hEventually :=
      eventually_h3LandauQuarticCutoffBump_eq_one
        x

    have hEq :
        (fun n : ℕ =>
          F n x)
          =ᶠ[atTop]
        (fun _ : ℕ =>
          f x) := by
      filter_upwards [hEventually] with n hn
      dsimp [F]
      rw [hn, one_mul]

    exact
      tendsto_const_nhds.congr'
        hEq.symm

  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume)
      (l := atTop)
      (F := F)
      (f := f)
      (bound := fun x : Point3 => ‖f x‖)
      (Filter.Eventually.of_forall hFMeas)
      (Filter.Eventually.of_forall hBound)
      hf.norm
      hPointwise

  change
    Tendsto
      (fun n : ℕ =>
        ∫ x : Point3,
          h3LandauCutoffBump
              (h3LandauQuarticRadius n)
              (h3LandauQuarticRadius_pos n)
              x
            *
          f x)
      atTop
      (𝓝
        (
          ∫ x : Point3,
            f x
        ))

  simpa [F] using
    hDCT

end

end Euclidean
end Bridge
end PrimeTensor
