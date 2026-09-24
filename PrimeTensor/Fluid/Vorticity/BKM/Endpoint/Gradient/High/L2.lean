import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Low.Physical.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1.Bound

/-!
# BKM endpoint: high-frequency gradient as an L² multiplier tail

The low-frequency term is now tied to the physical zeroth-order velocity `L²`
mass.  The high-frequency term needs the complementary structure: it should be
the weighted H³ state multiplied by a cutoff-dependent `L²` deweighting
multiplier.

For one upper dyadic index and derivative coordinate define

    m_hi,i(ξ)
      = χ_hi(ξ) d_i(ξ) W₃(ξ)⁻¹.

The first-moment H³ deweighting estimate already proves that

    ‖ξ‖ W₃(ξ)⁻¹ ∈ L²(R³).

Since the high cutoff is bounded by one and `‖d_i(ξ)‖ ≤ 2π ‖ξ‖`, the multiplier
`m_hi,i` is in `L²`.  Hölder against the weighted spectral state gives an `L¹`
high-frequency gradient with bound

    ‖m_hi,i G‖₁ ≤ ‖m_hi,i‖₂ ‖G‖₂.

This file isolates the entire upper-cutoff dependence in the single scalar
quantity `‖m_hi,i‖₂`.  The next checkpoint can prove that this tail norm decays
with the dyadic cutoff without reopening the Fourier reconstruction layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointHighFrequencyGradientL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## High-frequency H³ deweighting multiplier -/

/--
The high-frequency derivative multiplier after extracting the weighted H³
state itself.
-/
noncomputable def h3BKMHighGradientDeweightingMultiplier
    (hi : ℕ)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ℂ :=
  (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
    *
  h3FourierDerivativeSymbol i ξ
    *
  h3SobolevFrequencyWeightInvComplex ξ

theorem h3BKMHighGradientDeweightingMultiplier_aestronglyMeasurable
    (hi : ℕ)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3BKMHighGradientDeweightingMultiplier hi i)
      (volume : Measure H3FourierPoint3) := by

  have hHigh :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)) :=
    Complex.continuous_ofReal.comp
      (h3BKMDyadicHighFrequencyFactor_continuous hi)

  have hInv :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          h3SobolevFrequencyWeightInvComplex ξ) := by
    unfold h3SobolevFrequencyWeightInvComplex
    exact
      Complex.continuous_ofReal.comp
        continuous_h3SobolevFrequencyWeightInv

  unfold h3BKMHighGradientDeweightingMultiplier

  exact
    ((hHigh.mul
      (h3FourierDerivativeSymbol_continuous i)).mul hInv).aestronglyMeasurable

/--
Pointwise majorization by the already-integrable first-moment reciprocal H³
weight.
-/
theorem norm_h3BKMHighGradientDeweightingMultiplier_le
    (hi : ℕ)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖
      ≤
    (2 * Real.pi)
      *
    h3SobolevFrequencyFirstMomentInv ξ := by

  have hInvNonneg :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  calc
    ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖
        =
      ‖(h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
          *
        (h3FourierDerivativeSymbol i ξ
          *
        h3SobolevFrequencyWeightInvComplex ξ)‖ := by
          unfold h3BKMHighGradientDeweightingMultiplier
          rw [mul_assoc]

    _ ≤
      ‖h3FourierDerivativeSymbol i ξ
          *
        h3SobolevFrequencyWeightInvComplex ξ‖ :=
      norm_h3BKMDyadicHighFrequencyFactor_mul_le
        hi ξ
        (h3FourierDerivativeSymbol i ξ
          *
        h3SobolevFrequencyWeightInvComplex ξ)

    _ =
      ‖h3FourierDerivativeSymbol i ξ‖
        *
      h3SobolevFrequencyWeightInv ξ := by
        unfold h3SobolevFrequencyWeightInvComplex
        rw [
          norm_mul,
          Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg hInvNonneg
        ]

    _ ≤
      h3FourierGradientMagnitude ξ
        *
      h3SobolevFrequencyWeightInv ξ :=
      mul_le_mul_of_nonneg_right
        (norm_h3FourierDerivativeSymbol_le_gradientMagnitude i ξ)
        hInvNonneg

    _ =
      (2 * Real.pi)
        *
      h3SobolevFrequencyFirstMomentInv ξ := by
        unfold
          h3FourierGradientMagnitude
          h3SobolevFrequencyFirstMomentInv
        ring

theorem h3BKMHighGradientDeweightingMultiplier_memLp2
    (hi : ℕ)
    (i : Fin 3) :
    MemLp
      (h3BKMHighGradientDeweightingMultiplier hi i)
      2
      (volume : Measure H3FourierPoint3) := by

  have hMajorant :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          (((2 * Real.pi : ℝ) : ℂ)
            *
          h3SobolevFrequencyFirstMomentInvComplex ξ))
        2
        (volume : Measure H3FourierPoint3) :=
    h3SobolevFrequencyFirstMomentInvComplex_memLp2.const_mul
      (((2 * Real.pi : ℝ) : ℂ))

  refine
    hMajorant.of_le
      (h3BKMHighGradientDeweightingMultiplier_aestronglyMeasurable hi i)
      ?_

  filter_upwards with ξ

  have hFirstNonneg :
      0 ≤ h3SobolevFrequencyFirstMomentInv ξ := by
    unfold
      h3SobolevFrequencyFirstMomentInv
      h3SobolevFrequencyWeightInv
    exact
      mul_nonneg
        (norm_nonneg ξ)
        (inv_nonneg.mpr
          (h3SobolevFrequencyWeight_pos ξ).le)

  calc
    ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖
        ≤
      (2 * Real.pi)
        *
      h3SobolevFrequencyFirstMomentInv ξ :=
      norm_h3BKMHighGradientDeweightingMultiplier_le
        hi i ξ

    _ =
      ‖(((2 * Real.pi : ℝ) : ℂ)
          *
        h3SobolevFrequencyFirstMomentInvComplex ξ)‖ := by
        unfold h3SobolevFrequencyFirstMomentInvComplex
        rw [
          norm_mul,
          Complex.norm_real,
          Complex.norm_real,
          Real.norm_eq_abs,
          Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
          abs_of_nonneg hFirstNonneg
        ]

/-- The high-frequency deweighting multiplier as a genuine Fourier `L²` state. -/
noncomputable def h3BKMHighGradientDeweightingMultiplierL2
    (hi : ℕ)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (h3BKMHighGradientDeweightingMultiplier_memLp2 hi i).toLp
    (h3BKMHighGradientDeweightingMultiplier hi i)

theorem h3BKMHighGradientDeweightingMultiplierL2_ae
    (hi : ℕ)
    (i : Fin 3) :
    (h3BKMHighGradientDeweightingMultiplierL2 hi i :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMHighGradientDeweightingMultiplier hi i := by

  exact
    MemLp.coeFn_toLp
      (h3BKMHighGradientDeweightingMultiplier_memLp2 hi i)

/-! ## Hölder package against the weighted H³ state -/

/--
Canonical `L¹` high-frequency gradient obtained by multiplying the
cutoff-dependent deweighting multiplier with the weighted H³ state.
-/
noncomputable def h3BKMHighGradientHolderL1
    (hi : ℕ)
    (i : Fin 3)
    (G : H3SpectralScalarState) :
    H3FourierComplexL1 :=
  h3BKMHighGradientDeweightingMultiplierL2 hi i • G

theorem norm_h3BKMHighGradientHolderL1_le
    (hi : ℕ)
    (i : Fin 3)
    (G : H3SpectralScalarState) :
    ‖h3BKMHighGradientHolderL1 hi i G‖
      ≤
    ‖h3BKMHighGradientDeweightingMultiplierL2 hi i‖
      * ‖G‖ := by

  unfold h3BKMHighGradientHolderL1

  exact
    MeasureTheory.Lp.norm_smul_le
      (h3BKMHighGradientDeweightingMultiplierL2 hi i)
      G

/--
The Hölder package is exactly the previously defined concrete high-frequency
gradient amplitude almost everywhere.
-/
theorem h3BKMHighGradientHolderL1_ae
    (hi : ℕ)
    (i : Fin 3)
    (G : H3SpectralScalarState) :
    (h3BKMHighGradientHolderL1 hi i G :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMHighGradientAmplitude hi G i := by

  have hMul :
      (h3BKMHighGradientHolderL1 hi i G :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (
        (h3BKMHighGradientDeweightingMultiplierL2 hi i :
          H3FourierPoint3 → ℂ)
          •
        (G : H3FourierPoint3 → ℂ)
      ) := by

    simpa [h3BKMHighGradientHolderL1] using
      (
        MeasureTheory.Lp.coeFn_lpSMul
          (r := (1 : ENNReal))
          (h3BKMHighGradientDeweightingMultiplierL2 hi i)
          G
      )

  filter_upwards [
    hMul,
    h3BKMHighGradientDeweightingMultiplierL2_ae hi i
  ] with ξ hMulξ hMultiplierξ

  rw [hMulξ]
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [hMultiplierξ]

  unfold
    h3BKMHighGradientDeweightingMultiplier
    h3BKMHighGradientAmplitude
    h3SpectralScalarRawFourierCoordinateDerivative
    h3SpectralScalarRawFourier

  ring

/-! ## Pointwise inverse-Fourier tail estimate -/

/--
The high-frequency inverse-Fourier contribution is controlled by the
cutoff-dependent multiplier `L²` norm times the weighted H³ norm.
-/
theorem norm_fourierInv_h3BKMHighGradientAmplitude_le_multiplierL2
    (hi : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude hi G i)
        x‖
      ≤
    ‖h3BKMHighGradientDeweightingMultiplierL2 hi i‖
      * ‖G‖ := by

  have hHolderInt :
      Integrable
        ((h3BKMHighGradientHolderL1 hi i G :
            H3FourierComplexL1) :
          H3FourierPoint3 → ℂ) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.Lp.memLp
        (h3BKMHighGradientHolderL1 hi i G))

  have hHighInt :
      Integrable
        (h3BKMHighGradientAmplitude hi G i)
        (volume : Measure H3FourierPoint3) :=
    hHolderInt.congr
      (h3BKMHighGradientHolderL1_ae hi i G)

  calc
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude hi G i)
        x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3BKMHighGradientAmplitude hi G i ξ‖ := by

          change
            ‖VectorFourier.fourierIntegral
                Real.fourierChar
                (volume : Measure H3FourierPoint3)
                (-(innerₗ H3FourierPoint3))
                (h3BKMHighGradientAmplitude hi G i)
                x‖
              ≤
            ∫ ξ : H3FourierPoint3,
              ‖h3BKMHighGradientAmplitude hi G i ξ‖

          exact
            VectorFourier.norm_fourierIntegral_le_integral_norm
              Real.fourierChar
              (volume : Measure H3FourierPoint3)
              (-(innerₗ H3FourierPoint3))
              (h3BKMHighGradientAmplitude hi G i)
              x

    _ =
      ‖h3BKMHighGradientHolderL1 hi i G‖ := by

        rw [L1.norm_eq_integral_norm]
        apply integral_congr_ae

        filter_upwards [
          h3BKMHighGradientHolderL1_ae hi i G
        ] with ξ hξ

        rw [hξ]

    _ ≤
      ‖h3BKMHighGradientDeweightingMultiplierL2 hi i‖
        * ‖G‖ :=
      norm_h3BKMHighGradientHolderL1_le
        hi i G

end

end Euclidean
end Bridge
end PrimeTensor
