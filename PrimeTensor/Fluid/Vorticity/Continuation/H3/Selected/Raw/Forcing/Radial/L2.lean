import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2

/-!
# Public radial L² bridge for the unprojected selected forcing

`H3PathSelectedForcingRadialL2` already proves the raw finite outer-product
 divergence radial `L²` estimate internally, but the theorem is private because
 only the Leray-projected consequence was needed there.

The pressure branch now needs the unprojected half as well.  This file exports
 exactly the same estimate with no new analytic input, then specializes it to
 every strict positive selected restart time using the already-proved arbitrary
 raw Fourier moments of the selected mild state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedRawForcingRadialL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedRawForcingRadialL2 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One Fourier derivative shifts radial `L²` weight by one.  This is the
 public-module copy of the private helper already used by the Leray radial
 theorem. -/
private theorem h3RawPublic_fourierDerivative_mul_rawProductConvolution_radialWeight_memLp2
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
            h3RawProductConvolution F G ξ)
        2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          (h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            (h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ))
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow m)).aestronglyMeasurable.mul
        (h3FourierDerivative_mul_rawProductConvolution_integrable
          F G j).1

  have hMajor :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          (((2 * Real.pi : ℝ) : ℂ) *
            (((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
              h3RawProductConvolution F G ξ)))
        2
        (volume : Measure H3FourierPoint3) :=
    hConv.const_mul (((2 * Real.pi : ℝ) : ℂ))

  refine hMajor.of_le hMeas ?_

  filter_upwards with ξ

  have hr0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  have hrm0 : 0 ≤ ‖ξ‖ ^ m :=
    pow_nonneg hr0 m

  have hrSucc0 : 0 ≤ ‖ξ‖ ^ (m + 1) :=
    pow_nonneg hr0 (m + 1)

  have hDeriv :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    calc
      ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          j ξ
      _ =
        (2 * Real.pi) * ‖ξ‖ := by
        unfold h3FourierGradientMagnitude
        rfl

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrm0,
    norm_mul,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hTwoPi,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrSucc0
  ]

  calc
    ‖ξ‖ ^ m *
        (‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ‖ξ‖ ^ m *
        (((2 * Real.pi) * ‖ξ‖) *
          ‖h3RawProductConvolution F G ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDeriv
            (norm_nonneg _))
          hrm0
    _ =
      (2 * Real.pi) *
        (‖ξ‖ ^ (m + 1) *
          ‖h3RawProductConvolution F G ξ‖) := by
      rw [pow_succ]
      ring

/-- If every input coordinate has the required doubled raw moment, the
 unprojected finite outer-product divergence has order-`m` radial Fourier
 `L²`. -/
theorem h3RawFinOuterProductDivergence_radialWeight_memLp2_export
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U k))
    (hV :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V k)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinOuterProductDivergence U V i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  have hTerm :
      ∀ j : Fin 3,
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
              (h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ))
          2
          (volume : Measure H3FourierPoint3) := by
    intro j

    have hConv :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
              h3RawProductConvolution (U i) (V j) ξ)
          2
          (volume : Measure H3FourierPoint3) :=
      h3RawProductConvolution_radialWeight_memLp2_of_doubleMoment
        (m + 1)
        (U i)
        (V j)
        (by
          simpa only [
            Nat.mul_add,
            Nat.mul_one
          ] using hU i)
        (by
          simpa only [
            Nat.mul_add,
            Nat.mul_one
          ] using hV j)

    exact
      h3RawPublic_fourierDerivative_mul_rawProductConvolution_radialWeight_memLp2
        m (U i) (V j) j hConv

  have hSum :=
    MeasureTheory.memLp_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hTerm j)

  unfold h3RawFinOuterProductDivergence

  simpa only [
    Finset.mul_sum
  ] using hSum

/-- At every positive selected restart time, every finite radial weight of the
 unprojected nonlinear forcing belongs to Fourier `L²`. -/
theorem h3RawFinOuterProductDivergence_selectedRestart_radialWeight_memLp2
    {ν A s : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinOuterProductDivergence
            (W s) (W s) i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hMoment :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (W s k) := by
    intro k
    unfold H3RawFourierMomentIntegrable
    dsimp only [W]

    have hNat :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        (2 * (m + 1))
        hν U₀ hA hU₀ hs hsR k

    simpa only [
      h3FourierMomentWeight_natCast
    ] using hNat

  exact
    h3RawFinOuterProductDivergence_radialWeight_memLp2_export
      m (W s) (W s) i hMoment hMoment

end

end Euclidean
end Bridge
end PrimeTensor
