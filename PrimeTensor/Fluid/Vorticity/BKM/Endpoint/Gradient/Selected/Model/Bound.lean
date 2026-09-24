import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Middle.Selected.Representative
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Low.Physical.L2
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.High.Cutoff.Selection

/-!
# BKM endpoint: bound the complete selected low/middle/high gradient model

The endpoint ingredients are now available separately:

* the fixed low-frequency contribution is controlled by the physical base
  velocity `L²` mass;
* the selected middle contribution is a canonical pointwise representative
  with logarithmic vorticity control;
* the selected high-frequency contribution is uniformly bounded after choosing
  the canonical upper cutoff.

This file packages those three pieces into one complex pointwise gradient model
for an arbitrary target velocity component `j : Fin 3` and derivative
coordinate `i : Fin 3`.

No reconstruction statement is asserted here.  The purpose of this checkpoint
is to isolate the quantitative estimate from the final identification theorem.
Once the model is shown to equal the real physical derivative, the endpoint
bound follows immediately by taking real parts.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedGradientModelBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Three-component selected middle package -/

/--
Selected middle-gradient proxy for an arbitrary target velocity component.
-/
noncomputable def h3BKMSelectedMiddleGradient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t A : ℝ)
    (j i : Fin 3)
    (x : Point3) : ℂ :=
  ![
    h3BKMSelectedMiddleGradientComponent0 u t A i x,
    h3BKMSelectedMiddleGradientComponent1 u t A i x,
    h3BKMSelectedMiddleGradientComponent2 u t A i x
  ] j

/--
The selected middle-gradient package inherits the componentwise logarithmic
bound.
-/
theorem norm_h3BKMSelectedMiddleGradient_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (j i : Fin 3)
    (x : Point3) :
    ‖h3BKMSelectedMiddleGradient
        u t A j i x‖
      ≤
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  fin_cases j

  · simpa [h3BKMSelectedMiddleGradient] using
      norm_h3BKMSelectedMiddleGradientComponent0_le
        hEnvelope A i x

  · simpa [h3BKMSelectedMiddleGradient] using
      norm_h3BKMSelectedMiddleGradientComponent1_le
        hEnvelope A i x

  · simpa [h3BKMSelectedMiddleGradient] using
      norm_h3BKMSelectedMiddleGradientComponent2_le
        hEnvelope A i x

/-! ## Complete selected gradient model -/

/--
The complete selected BKM gradient model: fixed low piece, canonical selected
middle piece, and selected high tail.
-/
noncomputable def h3BKMSelectedGradientModel
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3)
    (x : Point3) : ℂ :=
  FourierTransformInv.fourierInv
      (h3BKMLowGradientAmplitude
        0
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i)
      ((WithLp.toLp 2 :
        Point3 → H3FourierPoint3) x)
    +
  h3BKMSelectedMiddleGradient
      u t A j i x
    +
  FourierTransformInv.fourierInv
      (h3BKMHighGradientAmplitude
        (h3BKMUpperCutoffIndex A)
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i)
      ((WithLp.toLp 2 :
        Point3 → H3FourierPoint3) x)

/--
Quantitative bound for the complete selected gradient model.

The only size hypothesis is that the chosen scalar cutoff scale `A` dominates
the weighted H³ norm of the selected velocity component.
-/
theorem norm_h3BKMSelectedGradientModel_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (j i : Fin 3)
    (x : Point3)
    (hComponent :
      ‖velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j‖
        ≤ A) :
    ‖h3BKMSelectedGradientModel
        hFourier A j i x‖
      ≤
    h3BKMLowGradientUnitL2Constant
        *
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖
      +
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant)
      +
    (2 * Real.pi)
      * h3BKMQuarterTailMomentConstant := by

  let xH : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier j

  let L : ℂ :=
    FourierTransformInv.fourierInv
      (h3BKMLowGradientAmplitude 0 G i)
      xH

  let M : ℂ :=
    h3BKMSelectedMiddleGradient
      u t A j i x

  let H : ℂ :=
    FourierTransformInv.fourierInv
      (h3BKMHighGradientAmplitude
        (h3BKMUpperCutoffIndex A)
        G i)
      xH

  have hLow :
      ‖L‖
        ≤
      h3BKMLowGradientUnitL2Constant
        *
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖ := by
    dsimp only [L, G, xH]
    exact
      norm_fourierInv_h3BKMLowGradientAmplitude_zero_le_physicalL2
        hFourier j i
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)

  have hMiddle :
      ‖M‖
        ≤
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
    dsimp only [M]
    exact
      norm_h3BKMSelectedMiddleGradient_le
        hEnvelope A j i x

  have hHigh :
      ‖H‖
        ≤
      (2 * Real.pi)
        * h3BKMQuarterTailMomentConstant := by
    dsimp only [H, G, xH]
    exact
      norm_fourierInv_h3BKMHighGradientAmplitude_selected_le_constant
        A
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
        hComponent

  change
    ‖L + M + H‖
      ≤
    h3BKMLowGradientUnitL2Constant
        *
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖
      +
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant)
      +
    (2 * Real.pi)
      * h3BKMQuarterTailMomentConstant

  calc
    ‖L + M + H‖
        ≤
      ‖L + M‖ + ‖H‖ :=
      norm_add_le _ _

    _ ≤
      (‖L‖ + ‖M‖) + ‖H‖ := by
      exact
        add_le_add
          (norm_add_le L M)
          le_rfl

    _ ≤
      (h3BKMLowGradientUnitL2Constant
          *
        ‖velocityH3L2JetAt
            u t hInt hMeas
            (h3JetSlot0 j)‖
        +
        2
          * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
          * (g t * h3BKMDyadicKernelUnitMassConstant))
        +
      (2 * Real.pi)
        * h3BKMQuarterTailMomentConstant := by
      exact
        add_le_add
          (add_le_add hLow hMiddle)
          hHigh

    _ =
      h3BKMLowGradientUnitL2Constant
          *
        ‖velocityH3L2JetAt
            u t hInt hMeas
            (h3JetSlot0 j)‖
        +
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant)
        +
      (2 * Real.pi)
        * h3BKMQuarterTailMomentConstant := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
