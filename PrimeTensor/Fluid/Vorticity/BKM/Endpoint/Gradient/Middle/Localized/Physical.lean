import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Gradient.Localized.Physical
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Gradient.Middle

/-!
# BKM endpoint: logarithmic physical bounds for middle localized gradient states

The previous checkpoint constructed the exact one-shell inverse-gradient `L²`
states and proved the scale-uniform a.e. estimate

    ‖Gⱼ,R(x)‖ ≤ 2 * (g(t) * C_BKM).

The middle-frequency state is the finite `L²` sum over dyadic radii
`Rₙ = 2ⁿ`.  This file performs that finite summation directly at the level of
`L²` classes.

Two generic bookkeeping lemmas are isolated first:

* the coercion of a finite sum of `L²` classes agrees almost everywhere with
  the finite sum of their representatives;
* if every summand is a.e. bounded by the same constant `C`, then the pulled
  physical representative of the finite sum is a.e. bounded by
  `J.card * C`.

Applying these to the three one-shell BKM gradient states and then using the
already-proved identity

    #(Icc lo hi) = h3BKMMiddleDyadicLogWidth lo hi

gives the logarithmic middle-frequency estimate

    ‖Gⱼ,[lo,hi](x)‖
      ≤ 2 * h3BKMMiddleDyadicLogWidth lo hi
          * (g(t) * C_BKM)

almost everywhere in physical space.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointMiddleLocalizedGradientPhysical
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointMiddleLocalizedGradientPhysical :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic finite sums of complex `L²` states -/

/--
A finite sum of complex `L²` classes is represented almost everywhere by the
pointwise finite sum of their chosen `Lp` representatives.
-/
theorem h3FourierComplexL2_finsetSum_ae
    (J : Finset ℕ)
    (F : ℕ → H3FourierComplexL2) :
    (((∑ n ∈ J, F n : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ∑ n ∈ J,
        (F n : H3FourierPoint3 → ℂ) ξ) := by

  classical
  induction J using Finset.induction_on with
  | empty =>
      filter_upwards [
        MeasureTheory.Lp.coeFn_zero
          ℂ
          (2 : ℝ≥0∞)
          (volume : Measure H3FourierPoint3)
      ] with ξ hZero

      simpa using hZero

  | @insert a J ha ih =>
      have hAdd :=
        MeasureTheory.Lp.coeFn_add
          (F a)
          (∑ n ∈ J, F n)

      filter_upwards [hAdd, ih] with ξ hAddξ ihξ

      rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha]

      calc
        (((F a + ∑ n ∈ J, F n : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ)
            =
          (F a : H3FourierPoint3 → ℂ) ξ
            +
          ((∑ n ∈ J, F n : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ := by
              simpa only [Pi.add_apply] using hAddξ

        _ =
          (F a : H3FourierPoint3 → ℂ) ξ
            +
          ∑ n ∈ J,
            (F n : H3FourierPoint3 → ℂ) ξ := by
              rw [ihξ]

/--
Pulling the preceding finite-sum representative identity back to `Point3`
through `WithLp.toLp`.
-/
theorem h3FourierComplexL2_finsetSum_toLp_ae
    (J : Finset ℕ)
    (F : ℕ → H3FourierComplexL2) :
    (fun x : Point3 =>
      ((∑ n ∈ J, F n : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      ∑ n ∈ J,
        (F n : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)) := by

  have hPull :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (h3FourierComplexL2_finsetSum_ae J F)

  change
    (fun x : Point3 =>
      ((∑ n ∈ J, F n : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      ∑ n ∈ J,
        (F n : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
    at hPull

  exact hPull

/--
Uniform a.e. bounds on finitely many pulled physical `L²` representatives sum
with the expected cardinality factor.
-/
theorem ae_norm_h3FourierComplexL2_finsetSum_toLp_le_card_mul
    (J : Finset ℕ)
    (F : ℕ → H3FourierComplexL2)
    (C : ℝ)
    (hBound :
      ∀ n ∈ J,
        ∀ᵐ x ∂(volume : Measure Point3),
          ‖(F n : H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)‖
            ≤
          C) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖((∑ n ∈ J, F n : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      (J.card : ℝ) * C := by

  have hRep :=
    h3FourierComplexL2_finsetSum_toLp_ae J F

  have hAll :
      ∀ᵐ x ∂(volume : Measure Point3),
        ∀ n ∈ J,
          ‖(F n : H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)‖
            ≤
          C := by
    exact
      (Finset.eventually_all J).2 hBound

  filter_upwards [hRep, hAll] with x hRepx hAllx

  rw [hRepx]

  calc
    ‖∑ n ∈ J,
        (F n : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖
        ≤
      ∑ n ∈ J,
        ‖(F n : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ := by
          exact
            norm_sum_le
              J
              (fun n =>
                (F n : H3FourierPoint3 → ℂ)
                  ((WithLp.toLp 2 :
                    Point3 → H3FourierPoint3) x))

    _ ≤
      ∑ _n ∈ J, C := by
        exact
          Finset.sum_le_sum
            (fun n hn => hAllx n hn)

    _ =
      (J.card : ℝ) * C := by
        simp

/-! ## Middle-window localized gradient `L²` states -/

noncomputable def h3BKMMiddleLocalizedGradientComponent0InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  ∑ n ∈ Finset.Icc lo hi,
    h3BKMDyadicLocalizedGradientComponent0InverseL2
      hFourier
      (h3BKMDyadicRadius n)
      (h3BKMDyadicRadius_pos n)
      i

noncomputable def h3BKMMiddleLocalizedGradientComponent1InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  ∑ n ∈ Finset.Icc lo hi,
    h3BKMDyadicLocalizedGradientComponent1InverseL2
      hFourier
      (h3BKMDyadicRadius n)
      (h3BKMDyadicRadius_pos n)
      i

noncomputable def h3BKMMiddleLocalizedGradientComponent2InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (lo hi : ℕ)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  ∑ n ∈ Finset.Icc lo hi,
    h3BKMDyadicLocalizedGradientComponent2InverseL2
      hFourier
      (h3BKMDyadicRadius n)
      (h3BKMDyadicRadius_pos n)
      i

/-! ## Exact logarithmic physical bounds -/

theorem ae_norm_h3BKMMiddleLocalizedGradientComponent0InverseL2_toLp_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier lo hi i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have h :=
    ae_norm_h3FourierComplexL2_finsetSum_toLp_le_card_mul
      (Finset.Icc lo hi)
      (fun n =>
        h3BKMDyadicLocalizedGradientComponent0InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)
      (2 * (g t * h3BKMDyadicKernelUnitMassConstant))
      (fun n _hn =>
        ae_norm_h3BKMDyadicLocalizedGradientComponent0InverseL2_toLp_le
          hInt hMeas hFourier hEnvelope
          (h3BKMDyadicRadius_pos n)
          i)

  unfold h3BKMMiddleLocalizedGradientComponent0InverseL2

  rw [h3BKMMiddleDyadicShellCount lo hi] at h
  rw [← h3BKMMiddleDyadicLogWidth_eq_shellCount hlohi] at h

  filter_upwards [h] with x hx

  calc
    ‖((∑ n ∈ Finset.Icc lo hi,
          h3BKMDyadicLocalizedGradientComponent0InverseL2
            hFourier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i :
        H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      ((WithLp.toLp 2 :
        Point3 → H3FourierPoint3) x)‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := hx

    _ =
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
          ring

theorem ae_norm_h3BKMMiddleLocalizedGradientComponent1InverseL2_toLp_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier lo hi i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have h :=
    ae_norm_h3FourierComplexL2_finsetSum_toLp_le_card_mul
      (Finset.Icc lo hi)
      (fun n =>
        h3BKMDyadicLocalizedGradientComponent1InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)
      (2 * (g t * h3BKMDyadicKernelUnitMassConstant))
      (fun n _hn =>
        ae_norm_h3BKMDyadicLocalizedGradientComponent1InverseL2_toLp_le
          hInt hMeas hFourier hEnvelope
          (h3BKMDyadicRadius_pos n)
          i)

  unfold h3BKMMiddleLocalizedGradientComponent1InverseL2

  rw [h3BKMMiddleDyadicShellCount lo hi] at h
  rw [← h3BKMMiddleDyadicLogWidth_eq_shellCount hlohi] at h

  filter_upwards [h] with x hx

  calc
    ‖((∑ n ∈ Finset.Icc lo hi,
          h3BKMDyadicLocalizedGradientComponent1InverseL2
            hFourier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i :
        H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      ((WithLp.toLp 2 :
        Point3 → H3FourierPoint3) x)‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := hx

    _ =
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
          ring

theorem ae_norm_h3BKMMiddleLocalizedGradientComponent2InverseL2_toLp_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier lo hi i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have h :=
    ae_norm_h3FourierComplexL2_finsetSum_toLp_le_card_mul
      (Finset.Icc lo hi)
      (fun n =>
        h3BKMDyadicLocalizedGradientComponent2InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)
      (2 * (g t * h3BKMDyadicKernelUnitMassConstant))
      (fun n _hn =>
        ae_norm_h3BKMDyadicLocalizedGradientComponent2InverseL2_toLp_le
          hInt hMeas hFourier hEnvelope
          (h3BKMDyadicRadius_pos n)
          i)

  unfold h3BKMMiddleLocalizedGradientComponent2InverseL2

  rw [h3BKMMiddleDyadicShellCount lo hi] at h
  rw [← h3BKMMiddleDyadicLogWidth_eq_shellCount hlohi] at h

  filter_upwards [h] with x hx

  calc
    ‖((∑ n ∈ Finset.Icc lo hi,
          h3BKMDyadicLocalizedGradientComponent2InverseL2
            hFourier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i :
        H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      ((WithLp.toLp 2 :
        Point3 → H3FourierPoint3) x)‖
        ≤
      h3BKMMiddleDyadicLogWidth lo hi
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := hx

    _ =
      2
        * h3BKMMiddleDyadicLogWidth lo hi
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
          ring

end

end Euclidean
end Bridge
end PrimeTensor
