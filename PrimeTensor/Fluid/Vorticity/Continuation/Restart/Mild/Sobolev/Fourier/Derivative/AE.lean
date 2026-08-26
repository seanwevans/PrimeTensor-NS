import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Derivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# A.e. Fourier multiplier identity for H³ spatial derivatives

`FourierDerivative` proves the coordinate derivative identity at the level of
tempered distributions.  This file identifies the locally integrable
representative of the multiplier distribution.

The point is important: the coordinate symbol `ξ ↦ 2 π i ξ_j` is unbounded, so
we do not pretend that multiplication by the symbol is a bounded `L² → L²`
operator.  Instead:

* the Fourier transform of the derivative is already known to be in `L²`;
* the Fourier transform of the undifferentiated field is locally integrable;
* multiplication by the continuous coordinate symbol preserves local
  integrability;
* equality of the resulting tempered distributions forces equality of their
  locally integrable representatives almost everywhere.

This produces the exact a.e. identity required by
`VelocityH3FourierCompatibleAt`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

noncomputable section

noncomputable local instance axisFintypeH3FourierDerivativeAE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Local integrability of continuous multipliers -/

/--
Multiplying an `L²` representative by a continuous scalar function preserves
local integrability.

No global boundedness of the multiplier is assumed.
-/
theorem h3Continuous_mul_l2_locallyIntegrable
    {m : H3FourierPoint3 → ℂ}
    (hm : Continuous m)
    (F : H3FourierComplexL2) :
    LocallyIntegrable
      (fun ξ : H3FourierPoint3 => m ξ * F ξ)
      volume := by
  have hF :
      LocallyIntegrable
        (F : H3FourierPoint3 → ℂ)
        volume := by
    exact
      (MeasureTheory.Lp.memLp F).locallyIntegrable
        (by norm_num)

  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK

  exact
    MeasureTheory.IntegrableOn.continuousOn_mul
      hm.continuousOn
      (hF.integrableOn_isCompact hK)
      hK

/-! ## Uniqueness of the multiplier representative -/

/--
If an `L²` tempered distribution is equal to multiplication of another `L²`
tempered distribution by a continuous temperate-growth symbol, then the
corresponding raw representatives agree almost everywhere.

This is the bridge from the distributional multiplier statement to the
pointwise-a.e. statement used by the H³ Fourier jet.
-/
theorem h3L2_distribution_multiplier_ae
    {m : H3FourierPoint3 → ℂ}
    (hmContinuous : Continuous m)
    (hmGrowth : m.HasTemperateGrowth)
    (F G : H3FourierComplexL2)
    (hDist :
      ((G : H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ))
        =
      TemperedDistribution.smulLeftCLM ℂ m
        ((F : H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ))) :
    (G : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 => m ξ * F ξ) := by
  have hGLocal :
      LocallyIntegrable
        (G : H3FourierPoint3 → ℂ)
        volume := by
    exact
      (MeasureTheory.Lp.memLp G).locallyIntegrable
        (by norm_num)

  have hMulLocal :
      LocallyIntegrable
        (fun ξ : H3FourierPoint3 => m ξ * F ξ)
        volume :=
    h3Continuous_mul_l2_locallyIntegrable
      hmContinuous F

  apply
    ae_eq_of_integral_contDiff_smul_eq
      hGLocal hMulLocal

  intro g hgSmooth hgCompact

  have hgComplexCompact :
      HasCompactSupport
        (Complex.ofRealCLM ∘ g) :=
    hgCompact.comp_left rfl

  have hgComplexSmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (Complex.ofRealCLM ∘ g) := by
    simpa [Function.comp_def] using
      (hgSmooth.continuousLinearMap_comp
        Complex.ofRealCLM)

  let φ : 𝓢(H3FourierPoint3, ℂ) :=
    hgComplexCompact.toSchwartzMap
      hgComplexSmooth

  have hEval :
      (((G : H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)) φ)
        =
      (TemperedDistribution.smulLeftCLM ℂ m
        ((F : H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ))) φ := by
    exact congrArg
      (fun T : 𝓢'(H3FourierPoint3, ℂ) => T φ)
      hDist

  simpa [
    φ,
    MeasureTheory.Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hmGrowth,
    Function.comp_apply,
    smul_eq_mul,
    mul_assoc,
    mul_left_comm,
    mul_comm
  ] using hEval

/-! ## Coordinate symbols -/

/-- The first-order PrimeTensor Fourier symbol is continuous. -/
theorem h3FourierDerivativeSymbol_continuous
    (i : Fin 3) :
    Continuous
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol i ξ) := by
  rw [show
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol i ξ)
      =
    (fun ξ : H3FourierPoint3 =>
      (2 * Real.pi * Complex.I) *
        (inner ℝ ξ
          (h3FourierAxisDirection
            (h3AxisOfFin3 i)) : ℂ)) by
      funext ξ
      exact h3FourierDerivativeSymbol_eq_inner i ξ]
  fun_prop

/-- The first-order PrimeTensor Fourier symbol has temperate growth. -/
theorem h3FourierDerivativeSymbol_hasTemperateGrowth
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol i ξ).HasTemperateGrowth := by
  rw [show
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol i ξ)
      =
    (fun ξ : H3FourierPoint3 =>
      (2 * Real.pi * Complex.I) *
        (inner ℝ ξ
          (h3FourierAxisDirection
            (h3AxisOfFin3 i)) : ℂ)) by
      funext ξ
      exact h3FourierDerivativeSymbol_eq_inner i ξ]
  fun_prop

/-! ## PrimeTensor coordinate derivative: a.e. Fourier identity -/

/--
A classical PrimeTensor coordinate derivative which is `L²` has exactly the
expected Fourier multiplier almost everywhere.
-/
theorem h3ScalarFourierL2_spatialDerivative_fin_ae
    {f : ScalarField3}
    (hfC1 : SpatialC1 f)
    (i : Fin 3)
    (hf : MemLp f 2 volume)
    (hdi :
      MemLp
        (spatial3.d (h3AxisOfFin3 i) f)
        2 volume) :
    (h3ScalarFourierL2
        (hdi.toLp
          (spatial3.d (h3AxisOfFin3 i) f)) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol i ξ *
        h3ScalarFourierL2 (hf.toLp f) ξ) := by
  apply
    h3L2_distribution_multiplier_ae
      (h3FourierDerivativeSymbol_continuous i)
      (h3FourierDerivativeSymbol_hasTemperateGrowth i)
      (h3ScalarFourierL2 (hf.toLp f))
      (h3ScalarFourierL2
        (hdi.toLp
          (spatial3.d (h3AxisOfFin3 i) f)))

  exact
    h3ScalarFourierL2_spatialDerivative_fin_eq_distribution_multiplier
      hfC1 i hf hdi

end

end Euclidean
end Bridge
end PrimeTensor
