import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Frequency.Trichotomy.Gradient.Mass

/-!
# BKM endpoint: low-frequency gradient from base L² velocity

The previous file gives a coarse low-frequency estimate using the full weighted
H³ norm.  For the BKM logarithmic estimate that is not the correct low term:
the fixed low-frequency contribution should depend only on the zeroth-order
velocity `L²` mass.

For each dyadic lower scale and derivative coordinate define the compactly
supported multiplier

    m_lo,i(ξ) = χ_lo(ξ) d_i(ξ).

Because the cutoff is continuous and compactly supported and the derivative
symbol is continuous, `m_lo,i ∈ L²`.  Hölder against an arbitrary Fourier
`L²` state therefore gives an `L¹` localized gradient with norm

    ‖m_lo,i F‖₁ ≤ ‖m_lo,i‖₂ ‖F‖₂.

At the fixed BKM lower scale `lo = 0`, the finite sum of the three multiplier
norms is one absolute constant.  This isolates the low-frequency term from the
growing H³ energy and prepares the later kinetic-energy bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLowFrequencyGradientL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Compactly supported low-gradient multiplier -/

/-- Fourier multiplier `χ_lo d_i` for one low-frequency gradient coordinate. -/
noncomputable def h3BKMLowGradientMultiplier
    (lo : ℕ)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ℂ :=
  (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
    *
  h3FourierDerivativeSymbol i ξ

theorem h3BKMLowGradientMultiplier_continuous
    (lo : ℕ)
    (i : Fin 3) :
    Continuous
      (h3BKMLowGradientMultiplier lo i) := by

  unfold h3BKMLowGradientMultiplier

  exact
    (
      Complex.continuous_ofReal.comp
        (h3BKMDyadicLowFrequencyFactor_continuous lo)
    ).mul
      (h3FourierDerivativeSymbol_continuous i)

theorem h3BKMLowGradientMultiplier_hasCompactSupport
    (lo : ℕ)
    (i : Fin 3) :
    HasCompactSupport
      (h3BKMLowGradientMultiplier lo i) := by

  have hReal :
      HasCompactSupport
        (h3BKMDyadicLowFrequencyFactor lo) := by
    unfold h3BKMDyadicLowFrequencyFactor
    exact
      h3BKMFrequencyCutoffBump_hasCompactSupport
        (h3BKMDyadicRadius_pos lo)

  have hComplex :
      HasCompactSupport
        (fun ξ : H3FourierPoint3 =>
          (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)) := by

    have hComp :=
      hReal.comp_left
        (show ((0 : ℝ) : ℂ) = 0 by norm_num)

    simpa [Function.comp_def] using hComp

  unfold h3BKMLowGradientMultiplier

  exact
    hComplex.mul_right

theorem h3BKMLowGradientMultiplier_memLp2
    (lo : ℕ)
    (i : Fin 3) :
    MemLp
      (h3BKMLowGradientMultiplier lo i)
      2
      (volume : Measure H3FourierPoint3) := by

  exact
    (h3BKMLowGradientMultiplier_continuous lo i).memLp_of_hasCompactSupport
      (h3BKMLowGradientMultiplier_hasCompactSupport lo i)

/-- The compact low-gradient multiplier as a genuine Fourier `L²` state. -/
noncomputable def h3BKMLowGradientMultiplierL2
    (lo : ℕ)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (h3BKMLowGradientMultiplier_memLp2 lo i).toLp
    (h3BKMLowGradientMultiplier lo i)

theorem h3BKMLowGradientMultiplierL2_ae
    (lo : ℕ)
    (i : Fin 3) :
    (h3BKMLowGradientMultiplierL2 lo i :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMLowGradientMultiplier lo i := by

  exact
    MemLp.coeFn_toLp
      (h3BKMLowGradientMultiplier_memLp2 lo i)

/-! ## Fixed unit-scale low-frequency constant -/

/--
Absolute low-frequency constant obtained by summing the three coordinate
multiplier `L²` norms at the fixed dyadic scale `lo = 0`.
-/
noncomputable def h3BKMLowGradientUnitL2Constant : ℝ :=
  ∑ i : Fin 3,
    ‖h3BKMLowGradientMultiplierL2 0 i‖

theorem h3BKMLowGradientUnitL2Constant_nonneg :
    0 ≤ h3BKMLowGradientUnitL2Constant := by

  unfold h3BKMLowGradientUnitL2Constant

  exact
    Finset.sum_nonneg
      (fun i hi => norm_nonneg _)

theorem norm_h3BKMLowGradientMultiplierL2_zero_le_constant
    (i : Fin 3) :
    ‖h3BKMLowGradientMultiplierL2 0 i‖
      ≤
    h3BKMLowGradientUnitL2Constant := by

  unfold h3BKMLowGradientUnitL2Constant

  exact
    Finset.single_le_sum
      (fun k hk => norm_nonneg
        (h3BKMLowGradientMultiplierL2 0 k))
      (Finset.mem_univ i)

/-! ## Hölder package against an arbitrary base Fourier L² state -/

/--
`L¹` low-frequency gradient obtained by multiplying the compact `L²`
multiplier with an arbitrary Fourier `L²` state.
-/
noncomputable def h3BKMLowGradientHolderL1
    (lo : ℕ)
    (i : Fin 3)
    (F : H3FourierComplexL2) :
    H3FourierComplexL1 :=
  h3BKMLowGradientMultiplierL2 lo i • F

theorem norm_h3BKMLowGradientHolderL1_le
    (lo : ℕ)
    (i : Fin 3)
    (F : H3FourierComplexL2) :
    ‖h3BKMLowGradientHolderL1 lo i F‖
      ≤
    ‖h3BKMLowGradientMultiplierL2 lo i‖
      * ‖F‖ := by

  unfold h3BKMLowGradientHolderL1

  exact
    MeasureTheory.Lp.norm_smul_le
      (h3BKMLowGradientMultiplierL2 lo i)
      F

theorem h3BKMLowGradientHolderL1_ae
    (lo : ℕ)
    (i : Fin 3)
    (F : H3FourierComplexL2) :
    (h3BKMLowGradientHolderL1 lo i F :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMLowGradientMultiplier lo i ξ
        * F ξ := by

  have hMul :
      (h3BKMLowGradientHolderL1 lo i F :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (
        (h3BKMLowGradientMultiplierL2 lo i :
          H3FourierPoint3 → ℂ)
          •
        (F : H3FourierPoint3 → ℂ)
      ) := by

    simpa [h3BKMLowGradientHolderL1] using
      (
        MeasureTheory.Lp.coeFn_lpSMul
          (r := (1 : ENNReal))
          (h3BKMLowGradientMultiplierL2 lo i)
          F
      )

  filter_upwards [
    hMul,
    h3BKMLowGradientMultiplierL2_ae lo i
  ] with ξ hMulξ hMultiplierξ

  rw [hMulξ]

  simp only [Pi.smul_apply', smul_eq_mul]

  rw [hMultiplierξ]

/-! ## Fixed-scale quantitative bound -/

theorem norm_h3BKMLowGradientHolderL1_zero_le
    (i : Fin 3)
    (F : H3FourierComplexL2) :
    ‖h3BKMLowGradientHolderL1 0 i F‖
      ≤
    h3BKMLowGradientUnitL2Constant * ‖F‖ := by

  calc
    ‖h3BKMLowGradientHolderL1 0 i F‖
        ≤
      ‖h3BKMLowGradientMultiplierL2 0 i‖ * ‖F‖ :=
        norm_h3BKMLowGradientHolderL1_le
          0 i F

    _ ≤
      h3BKMLowGradientUnitL2Constant * ‖F‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_h3BKMLowGradientMultiplierL2_zero_le_constant i)
            (norm_nonneg F)

/--
The fixed-scale low-gradient ordinary inverse Fourier integral is bounded
pointwise by the base Fourier `L²` norm times one absolute constant.
-/
theorem norm_fourierInv_h3BKMLowGradientHolderL1_zero_le
    (i : Fin 3)
    (F : H3FourierComplexL2)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3BKMLowGradientMultiplier 0 i ξ * F ξ)
        x‖
      ≤
    h3BKMLowGradientUnitL2Constant * ‖F‖ := by

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3BKMLowGradientMultiplier 0 i ξ * F ξ)
        (volume : Measure H3FourierPoint3) := by

    have hHolderInt :
        Integrable
          ((h3BKMLowGradientHolderL1 0 i F :
              H3FourierComplexL1) :
            H3FourierPoint3 → ℂ) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (MeasureTheory.Lp.memLp
          (h3BKMLowGradientHolderL1 0 i F))

    exact
      hHolderInt.congr
        (h3BKMLowGradientHolderL1_ae 0 i F)

  calc
    ‖FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3BKMLowGradientMultiplier 0 i ξ * F ξ)
        x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3BKMLowGradientMultiplier 0 i ξ * F ξ‖ := by

          change
            ‖VectorFourier.fourierIntegral
                Real.fourierChar
                (volume : Measure H3FourierPoint3)
                (-(innerₗ H3FourierPoint3))
                (fun ξ : H3FourierPoint3 =>
                  h3BKMLowGradientMultiplier 0 i ξ * F ξ)
                x‖
              ≤
            ∫ ξ : H3FourierPoint3,
              ‖h3BKMLowGradientMultiplier 0 i ξ * F ξ‖

          exact
            VectorFourier.norm_fourierIntegral_le_integral_norm
              Real.fourierChar
              (volume : Measure H3FourierPoint3)
              (-(innerₗ H3FourierPoint3))
              (fun ξ : H3FourierPoint3 =>
                h3BKMLowGradientMultiplier 0 i ξ * F ξ)
              x

    _ =
      ‖h3BKMLowGradientHolderL1 0 i F‖ := by

        rw [L1.norm_eq_integral_norm]

        apply integral_congr_ae

        filter_upwards [
          h3BKMLowGradientHolderL1_ae 0 i F
        ] with ξ hξ

        rw [hξ]

    _ ≤
      h3BKMLowGradientUnitL2Constant * ‖F‖ :=
        norm_h3BKMLowGradientHolderL1_zero_le
          i F

end

end Euclidean
end Bridge
end PrimeTensor
