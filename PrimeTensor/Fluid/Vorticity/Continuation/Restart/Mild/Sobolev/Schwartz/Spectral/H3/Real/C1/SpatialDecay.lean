import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Point3Derivative
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Spatial decay of first derivatives of arbitrary spectral H³ states

The arbitrary spectral H³ reconstruction already provides:

* an `L¹` raw Fourier amplitude;
* an `L¹` first coordinate derivative multiplier;
* a classical real `C¹` representative on `Point3`;
* the exact identity identifying `spatial3.d` with the real part of the
  inverse Fourier transform of the derivative multiplier.

Mathlib's Riemann--Lebesgue lemma therefore gives the missing spatial
asymptotic statement directly.

For every weighted spectral H³ scalar state `G`, every first coordinate
derivative of its real `Point3` representative tends to zero along every
sequence escaping to spatial infinity.

The proof is split into two reusable steps.

1. The inverse Fourier transform of the raw derivative multiplier tends to
   zero along the cocompact filter of the Euclidean Fourier carrier.
2. `WithLp.toLp` is the inverse of a homeomorphism between `Point3` and the
   Euclidean carrier, hence carries cocompact escape to cocompact escape.
   The exact Point3 derivative bridge and continuity of complex real-part
   finish the result.

This is a fixed-slice H³ theorem.  It does not use terminal-time continuity.
The next terminal step can combine it with the already-isolated uniform
endpoint temporal modulus to transfer the decay to time `T`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SpectralFirstDerivativeSpatialDecay
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Riemann--Lebesgue for the raw derivative multiplier -/

/--
The inverse Fourier transform of one raw H³ coordinate-derivative multiplier
vanishes at spatial infinity on the Euclidean Fourier carrier.
-/
theorem h3SpectralScalarRawFourierCoordinateDerivative_fourierInv_tendsto_zero_cocompact
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    Tendsto
      (
        FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourierCoordinateDerivative G i)
      )
      (cocompact H3FourierPoint3)
      (𝓝 0) := by

  let D : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourierCoordinateDerivative G i

  have hFourier :
      Tendsto
        (𝓕 D)
        (cocompact H3FourierPoint3)
        (𝓝 0) := by

    change
      Tendsto
        (
          fun w : H3FourierPoint3 =>
            ∫ v : H3FourierPoint3,
              𝐞 (-⟪v, w⟫) • D v
        )
        (cocompact H3FourierPoint3)
        (𝓝 0)

    exact
      tendsto_integral_exp_inner_smul_cocompact
        D

  have hNeg :
      Tendsto
        (fun ξ : H3FourierPoint3 => -ξ)
        (cocompact H3FourierPoint3)
        (cocompact H3FourierPoint3) := by

    exact
      (Homeomorph.neg H3FourierPoint3).toCocompactMap.cocompact_tendsto'

  have hComposed :
      Tendsto
        (
          (𝓕 D) ∘
            (fun ξ : H3FourierPoint3 => -ξ)
        )
        (cocompact H3FourierPoint3)
        (𝓝 0) :=
    hFourier.comp
      hNeg

  have hInvEq :
      (
        fun ξ : H3FourierPoint3 =>
          FourierTransformInv.fourierInv
            D
            ξ
      )
        =
      (
        (𝓕 D) ∘
          (fun ξ : H3FourierPoint3 => -ξ)
      ) := by

    funext ξ

    rw [
      Real.fourierInv_eq_fourier_neg
    ]

    rfl

  have hInv :
      Tendsto
        (
          fun ξ : H3FourierPoint3 =>
            FourierTransformInv.fourierInv
              D
              ξ
        )
        (cocompact H3FourierPoint3)
        (𝓝 0) := by

    rw [hInvEq]

    exact
      hComposed

  simpa only [D] using
    hInv

/-! ## Transport cocompact escape from Point3 to the Euclidean carrier -/

/--
A `Point3` sequence escaping to infinity is carried by `WithLp.toLp` to the
cocompact filter of the Euclidean Fourier carrier.
-/
theorem h3Point3_toFourier_tendsto_cocompact_of_dist_tendsto_atTop
    {y : ℕ → Point3}
    (hEscape :
      Tendsto
        (fun n : ℕ =>
          dist
            (0 : Point3)
            (y n))
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          (WithLp.toLp 2 : Point3 → H3FourierPoint3)
            (y n)
      )
      atTop
      (cocompact H3FourierPoint3) := by

  have hPointCocompact :
      Tendsto
        y
        atTop
        (cocompact Point3) := by

    apply
      tendsto_cocompact_of_tendsto_dist_comp_atTop
        (0 : Point3)

    simpa only [dist_comm] using
      hEscape

  have hToFourierCocompact :
      Tendsto
        (WithLp.toLp 2 : Point3 → H3FourierPoint3)
        (cocompact Point3)
        (cocompact H3FourierPoint3) := by

    change
      Tendsto
        ⇑(
          (
            PiLp.homeomorph
              2
              (fun _ : PrimeTensor.Axis Depth.three => ℝ)
          ).symm
        )
        (cocompact Point3)
        (cocompact H3FourierPoint3)

    exact
      (
        (
          PiLp.homeomorph
            2
            (fun _ : PrimeTensor.Axis Depth.three => ℝ)
        ).symm
      ).toCocompactMap.cocompact_tendsto'

  exact
    hToFourierCocompact.comp
      hPointCocompact

/-! ## First derivative decay on Point3 -/

/--
Every first spatial coordinate derivative of the real `C¹` representative of
an arbitrary spectral H³ scalar state vanishes along every `Point3` sequence
escaping to infinity.
-/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_tendsto_zero_of_escape
    (G : H3SpectralScalarState)
    (i : Fin 3)
    {y : ℕ → Point3}
    (hEscape :
      Tendsto
        (fun n : ℕ =>
          dist
            (0 : Point3)
            (y n))
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          spatial3.d
            (h3AxisOfFin3 i)
            (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
            (y n)
      )
      atTop
      (𝓝 0) := by

  let D : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourierCoordinateDerivative G i

  have hFourierEscape :
      Tendsto
        (
          fun n : ℕ =>
            (WithLp.toLp 2 : Point3 → H3FourierPoint3)
              (y n)
        )
        atTop
        (cocompact H3FourierPoint3) :=
    h3Point3_toFourier_tendsto_cocompact_of_dist_tendsto_atTop
      hEscape

  have hComplex :
      Tendsto
        (
          fun n : ℕ =>
            FourierTransformInv.fourierInv
              D
              (
                (WithLp.toLp 2 : Point3 → H3FourierPoint3)
                  (y n)
              )
        )
        atTop
        (𝓝 0) := by

    exact
      (
        h3SpectralScalarRawFourierCoordinateDerivative_fourierInv_tendsto_zero_cocompact
          G i
      ).comp
        hFourierEscape

  have hReal :
      Tendsto
        (
          fun n : ℕ =>
            (
              FourierTransformInv.fourierInv
                D
                (
                  (WithLp.toLp 2 : Point3 → H3FourierPoint3)
                    (y n)
                )
            ).re
        )
        atTop
        (𝓝 0) := by

    have hRe :
        Tendsto
          (fun z : ℂ => z.re)
          (𝓝 (0 : ℂ))
          (𝓝 (0 : ℝ)) :=
      Complex.continuous_re.continuousAt

    exact
      hRe.comp
        hComplex

  simpa only [
    D,
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
  ] using
    hReal

end

end Euclidean
end Bridge
end PrimeTensor
