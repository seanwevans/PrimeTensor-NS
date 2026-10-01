import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Cutoff.L2
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Whole-space C¹ ∩ H¹ to L⁶ on Point3

This file removes compact support from the Point3 Sobolev endpoint.

For a spatially `C¹` scalar field `g` with

    g ∈ L²,
    Dg ∈ L²,

we use the expanding cutoff sequence

    gₙ = χ_{n+1} g.

The uniform cutoff derivative estimate gives one fixed `L²` majorant

    M(x) = ‖Dg(x)‖ + C |g(x)|

for every `‖Dgₙ(x)‖`.  Thus the `L²` norms of all cutoff derivatives are
uniformly bounded by `‖M‖₂`.  Compact-support Sobolev then gives a uniform
`L⁶` bound on `gₙ`.

At each fixed point, the sequence is eventually exactly equal to `g`.
Mathlib's Fatou/lower-semicontinuity theorem
`Lp.eLpNorm_le_of_ae_tendsto` transfers the uniform `L⁶` bound to `g`.

This closes the standard whole-space analytic frontier
`WholeSpaceC1FDerivL2ToL6`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauWholeSpaceSobolev
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Whole-space `C¹ ∩ H¹(Point3) → L⁶(Point3)`, by smooth cutoff
approximation and lower semicontinuity of the `L⁶` seminorm. -/
theorem wholeSpaceC1FDerivL2ToL6_cutoff :
    WholeSpaceC1FDerivL2ToL6 := by
  intro g hC1 hg2 hDg2

  obtain ⟨C, hCutoffDeriv⟩ :=
    exists_uniform_norm_fderiv_h3LandauCutoffBump_le_div

  let majorant : Point3 → ℝ :=
    (fun x : Point3 =>
      ‖fderiv ℝ g x‖)
      +
    (fun x : Point3 =>
      (C : ℝ) * |g x|)

  have hDgNorm2 :
      MeasureTheory.MemLp
        (fun x : Point3 =>
          ‖fderiv ℝ g x‖)
        (ENNReal.ofReal 2)
        volume :=
    hDg2.norm

  have hgAbs2 :
      MeasureTheory.MemLp
        (fun x : Point3 =>
          |g x|)
        (ENNReal.ofReal 2)
        volume := by
    simpa [Real.norm_eq_abs] using
      hg2.norm

  have hgScaled2 :
      MeasureTheory.MemLp
        (fun x : Point3 =>
          (C : ℝ) * |g x|)
        (ENNReal.ofReal 2)
        volume := by
    exact
      hgAbs2.const_mul (C : ℝ)

  have hMajorant2 :
      MeasureTheory.MemLp
        majorant
        (ENNReal.ofReal 2)
        volume := by
    dsimp [majorant]

    exact
      hDgNorm2.add hgScaled2

  let derivBound : ℝ≥0∞ :=
    eLpNorm
      majorant
      (ENNReal.ofReal 2)
      volume

  have hDerivBoundTop :
      derivBound < (⊤ : ℝ≥0∞) := by
    dsimp [derivBound]

    exact
      hMajorant2.eLpNorm_lt_top

  let sobolevConst : ℝ≥0∞ :=
    ((MeasureTheory.SNormLESNormFDerivOfEqConst
      ℝ
      (volume : Measure Point3)
      (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞)

  let globalBound : ℝ≥0∞ :=
    sobolevConst * derivBound

  have hGlobalBoundTop :
      globalBound < (⊤ : ℝ≥0∞) := by
    dsimp [globalBound, sobolevConst]

    exact
      ENNReal.mul_lt_top
        ENNReal.coe_lt_top
        hDerivBoundTop

  let radius : ℕ → ℝ :=
    fun n => (n : ℝ) + 1

  have hRadiusPos :
      ∀ n : ℕ,
        0 < radius n := by
    intro n
    dsimp [radius]
    positivity

  have hRadiusOne :
      ∀ n : ℕ,
        1 ≤ radius n := by
    intro n
    dsimp [radius]

    have hn :
        0 ≤ (n : ℝ) := by
      positivity

    linarith

  let cutoffSeq : ℕ → Point3 → ℝ :=
    fun n =>
      h3LandauCutoffField
        (radius n)
        (hRadiusPos n)
        g

  have hCutoffSeqMeas :
      ∀ n : ℕ,
        MeasureTheory.AEStronglyMeasurable
          (cutoffSeq n)
          volume := by
    intro n

    exact
      (
        h3LandauCutoffField_spatialC1
          (hRadiusPos n)
          hC1
      ).continuous.aestronglyMeasurable

  have hUniformDerivative :
      ∀ n : ℕ,
        eLpNorm
            (fun x : Point3 =>
              fderiv ℝ
                (cutoffSeq n)
                x)
            (ENNReal.ofReal 2)
            volume
          ≤
        derivBound := by
    intro n

    have hPointwise :
        ∀ x : Point3,
          ‖fderiv ℝ
              (cutoffSeq n)
              x‖
            ≤
          ‖majorant x‖ := by
      intro x

      have hProductBound :
          ‖fderiv ℝ
              (cutoffSeq n)
              x‖
            ≤
          ‖fderiv ℝ g x‖
            +
          |g x|
            *
          ‖fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump
                  (radius n)
                  (hRadiusPos n)
                  y)
              x‖ := by
        simpa [cutoffSeq] using
          norm_fderiv_h3LandauCutoffField_le
            (hRadiusPos n)
            hC1
            x

      have hScaled :
          ‖fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump
                  (radius n)
                  (hRadiusPos n)
                  y)
              x‖
            ≤
          (C : ℝ) / radius n :=
        hCutoffDeriv
          (hRadiusPos n)
          x

      have hDivLe :
          (C : ℝ) / radius n
            ≤
          (C : ℝ) := by
        exact
          div_le_self
            C.coe_nonneg
            (hRadiusOne n)

      have hCutoffLe :
          ‖fderiv ℝ
              (fun y : Point3 =>
                h3LandauCutoffBump
                  (radius n)
                  (hRadiusPos n)
                  y)
              x‖
            ≤
          (C : ℝ) :=
        hScaled.trans hDivLe

      have hError :
          |g x|
              *
            ‖fderiv ℝ
                (fun y : Point3 =>
                  h3LandauCutoffBump
                    (radius n)
                    (hRadiusPos n)
                    y)
                x‖
            ≤
          (C : ℝ) * |g x| := by
        calc
          |g x|
              *
            ‖fderiv ℝ
                (fun y : Point3 =>
                  h3LandauCutoffBump
                    (radius n)
                    (hRadiusPos n)
                    y)
                x‖
              ≤
            |g x| * (C : ℝ) := by
              exact
                mul_le_mul_of_nonneg_left
                  hCutoffLe
                  (abs_nonneg _)

          _ =
            (C : ℝ) * |g x| := by
              exact mul_comm _ _

      have hRaw :
          ‖fderiv ℝ
              (cutoffSeq n)
              x‖
            ≤
          majorant x := by
        dsimp [majorant]

        exact
          hProductBound.trans
            (add_le_add_right
              hError
              ‖fderiv ℝ g x‖)

      have hMajorantNonneg :
          0 ≤ majorant x := by
        dsimp [majorant]

        exact
          add_nonneg
            (norm_nonneg _)
            (
              mul_nonneg
                C.coe_nonneg
                (abs_nonneg _)
            )

      simpa [
        Real.norm_eq_abs,
        abs_of_nonneg hMajorantNonneg
      ] using
        hRaw

    dsimp [derivBound]

    exact
      eLpNorm_mono_ae
        (ae_of_all
          volume
          hPointwise)

  have hUniformSix :
      ∀ n : ℕ,
        eLpNorm
            (cutoffSeq n)
            (ENNReal.ofReal 6)
            volume
          ≤
        globalBound := by
    intro n

    have hSobolev :=
      MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
        (μ := (volume : Measure Point3))
        (F := ℝ)
        (h3LandauCutoffField_spatialC1
          (hRadiusPos n)
          hC1)
        (h3LandauCutoffField_hasCompactSupport
          (hRadiusPos n)
          g)
        (p := (2 : ℝ≥0))
        (p' := (6 : ℝ≥0))
        (by norm_num)
        (by
          rw [point3_finrank_eq_three_landau]
          norm_num)
        (by
          rw [point3_finrank_eq_three_landau]
          norm_num)

    have hSobolev' :
        eLpNorm
            (cutoffSeq n)
            (ENNReal.ofReal 6)
            volume
          ≤
        sobolevConst
          *
        eLpNorm
            (fun x : Point3 =>
              fderiv ℝ
                (cutoffSeq n)
                x)
            (ENNReal.ofReal 2)
            volume := by
      simpa [cutoffSeq, sobolevConst] using
        hSobolev

    calc
      eLpNorm
          (cutoffSeq n)
          (ENNReal.ofReal 6)
          volume
        ≤
      sobolevConst
        *
      eLpNorm
          (fun x : Point3 =>
            fderiv ℝ
              (cutoffSeq n)
              x)
          (ENNReal.ofReal 2)
          volume :=
        hSobolev'

      _ ≤
        sobolevConst * derivBound := by
          gcongr
          exact hUniformDerivative n

      _ =
        globalBound := by
          rfl

  have hPointwiseTendsto :
      ∀ᵐ x : Point3 ∂volume,
        Tendsto
          (fun n : ℕ =>
            cutoffSeq n x)
          atTop
          (𝓝 (g x)) := by
    filter_upwards with x

    obtain ⟨N, hN⟩ :=
      exists_nat_gt ‖x‖

    have hEventually :
        (fun n : ℕ =>
          cutoffSeq n x)
          =ᶠ[atTop]
        (fun _ : ℕ => g x) := by
      exact
        eventually_atTop.2
          ⟨N, by
            intro n hn

            apply
              h3LandauCutoffField_eq_of_norm_le
                (hRadiusPos n)

            calc
              ‖x‖
                  ≤
                (N : ℝ) :=
                le_of_lt hN

              _ ≤
                (n : ℝ) := by
                  exact_mod_cast hn

              _ ≤
                radius n := by
                  dsimp [radius]
                  linarith
          ⟩

    exact
      tendsto_const_nhds.congr'
        hEventually.symm

  have hGlobalNormBound :
      eLpNorm
          g
          (ENNReal.ofReal 6)
          volume
        ≤
      globalBound := by
    exact
      MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
        (u := atTop)
        (f := cutoffSeq)
        (g := g)
        (C := globalBound)
        (Filter.Eventually.of_forall
          hUniformSix)
        hCutoffSeqMeas
        hPointwiseTendsto

  unfold MeasureTheory.MemLp

  constructor

  · exact
      hC1.continuous.aestronglyMeasurable

  · exact
      hGlobalNormBound.trans_lt
        hGlobalBoundTop

end

end Euclidean
end Bridge
end PrimeTensor
