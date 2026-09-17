import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.WholeSpaceSobolev

/-!
# Integrability facts for the whole-space quartic Landau identity

The remaining standard analytic frontier is

    ∫ g⁴ = -3 ∫ v g² dg,

with `|v|` bounded, `g ∈ L⁴`, and `dg ∈ L²`.

Before introducing a cutoff into the integration-by-parts identity, this file
records the two whole-space integrability facts that genuinely follow from
those hypotheses:

* `g ∈ L⁴` gives `|g|² ∈ L²` and `g⁴ ∈ L¹`;
* together with `dg ∈ L²` and the scalar envelope on `v`, the already existing
  Landau Hölder lemma gives integrability of
  `|v g² dg|` and of its envelope majorant.

No claim is made that `v g³ ∈ L¹`; that stronger statement is not implied by
the frontier hypotheses on all of `ℝ³` and is precisely why the subsequent
integration-by-parts proof uses a compactly-supported cutoff.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- `L⁴` membership is exactly enough to put the square of the absolute value
in `L²`. -/
theorem landauQuarticSquareMemLp_of_memLp_four
    {g : ScalarField3}
    (hg4 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 4)
        volume) :
    LandauQuarticSquareMemLp g := by
  have hFourDivTwo :
      (ENNReal.ofReal 4) / (ENNReal.ofReal 2)
        =
      ENNReal.ofReal 2 := by
    have hTwo_ne_zero :
        ENNReal.ofReal 2 ≠ 0 := by
      norm_num

    have hTwo_ne_top :
        ENNReal.ofReal 2 ≠ ⊤ := by
      simp

    symm

    apply
      (
        ENNReal.eq_div_iff
          hTwo_ne_zero
          hTwo_ne_top
      ).2

    norm_num

  have hSquare :=
    hg4.norm_rpow_div
      (ENNReal.ofReal 2)

  rw [hFourDivTwo] at hSquare

  unfold LandauQuarticSquareMemLp

  simpa [Real.norm_eq_abs] using
    hSquare

/-- An `L⁴` real field has integrable fourth power. -/
theorem integrable_pow_four_of_memLp_four
    {g : ScalarField3}
    (hg4 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 4)
        volume) :
    MeasureTheory.Integrable
      (fun x : Point3 =>
        (g x) ^ 4)
      volume := by
  have hFourDivFour :
      (ENNReal.ofReal 4) / (ENNReal.ofReal 4)
        =
      (1 : ENNReal) := by
    have hFour_ne_zero :
        ENNReal.ofReal 4 ≠ 0 := by
      norm_num

    have hFour_ne_top :
        ENNReal.ofReal 4 ≠ ⊤ := by
      simp

    symm

    apply
      (
        ENNReal.eq_div_iff
          hFour_ne_zero
          hFour_ne_top
      ).2

    norm_num

  have hAbsPow4Lp :=
    hg4.norm_rpow_div
      (ENNReal.ofReal 4)

  rw [hFourDivFour] at hAbsPow4Lp

  have hAbsPow4Int :
      MeasureTheory.Integrable
        (fun x : Point3 =>
          |g x| ^ 4)
        volume := by
    apply
      MeasureTheory.memLp_one_iff_integrable.mp

    simpa [Real.norm_eq_abs] using
      hAbsPow4Lp

  have hPowMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : Point3 =>
          (g x) ^ 4)
        volume :=
    hg4.aestronglyMeasurable.pow 4

  apply
    (
      MeasureTheory.integrable_norm_iff
        hPowMeas
    ).mp

  simpa [
    Real.norm_eq_abs,
    abs_pow
  ] using
    hAbsPow4Int

/-- The `L⁴ × L²` frontier hypotheses reconstruct the older Landau Cauchy
package. -/
theorem landauCauchyMemLp_of_memLp_four_two
    {g dg : ScalarField3}
    (hg4 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 4)
        volume)
    (hdg2 :
      MeasureTheory.MemLp
        dg
        (ENNReal.ofReal 2)
        volume) :
    LandauCauchyMemLp g dg := by
  have hSquare :
      LandauQuarticSquareMemLp g :=
    landauQuarticSquareMemLp_of_memLp_four
      hg4

  have hDgAbs2 :
      MeasureTheory.MemLp
        (fun x : Point3 =>
          abs (dg x))
        (ENNReal.ofReal 2)
        volume := by
    simpa [Real.norm_eq_abs] using
      hdg2.norm

  exact
    ⟨
      hSquare,
      hDgAbs2
    ⟩

/-- Bounded `v`, `g ∈ L⁴`, and `dg ∈ L²` imply the integrability package used
by the Landau quartic estimate. -/
theorem landauQuarticEnvelopeIntegrable_of_memLp_four_two
    {v g dg : ScalarField3}
    {h : ℝ}
    (hVMeas :
      MeasureTheory.AEStronglyMeasurable
        v
        volume)
    (hEnv :
      LandauScalarEnvelope
        v h)
    (hg4 :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 4)
        volume)
    (hdg2 :
      MeasureTheory.MemLp
        dg
        (ENNReal.ofReal 2)
        volume) :
    LandauQuarticEnvelopeIntegrable
      v g dg h := by
  exact
    landauQuarticEnvelopeIntegrable_of_cauchy_of_envelope_of_measurable
      hVMeas
      hEnv
      (
        landauCauchyMemLp_of_memLp_four_two
          hg4
          hdg2
      )

end

end Euclidean
end Bridge
end PrimeTensor
