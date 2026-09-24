import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Middle.Localized.Physical.Representative
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Middle.Selected.Pointwise.Bound

/-!
# BKM endpoint: canonical selected middle-gradient representatives

The general middle-gradient `L²` states have now been identified almost
everywhere with the concrete physical middle proxies, and the canonical upper
cutoff has already been selected from a scalar H³ size `A`.

This file packages the three selected physical middle terms as literal
pointwise functions

    M_j(A,t,i,x)

and records both properties needed by the final endpoint layer:

* `M_j` is an a.e. representative of the corresponding selected middle
  inverse-gradient `L²` state;
* `M_j` satisfies the selected logarithmic vorticity bound at every point.

Thus later files can work entirely with a canonical pointwise middle object and
never reopen the finite shell sum or `Lp` representative bookkeeping.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedMiddleGradientRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointSelectedMiddleGradientRepresentative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Canonical selected physical representatives -/

noncomputable def h3BKMSelectedMiddleGradientComponent0
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t A : ℝ)
    (i : Fin 3)
    (x : Point3) : ℂ :=
  h3BKMMiddleDyadicGradientComponent0
    u t
    0
    (h3BKMUpperCutoffIndex A)
    i x

noncomputable def h3BKMSelectedMiddleGradientComponent1
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t A : ℝ)
    (i : Fin 3)
    (x : Point3) : ℂ :=
  h3BKMMiddleDyadicGradientComponent1
    u t
    0
    (h3BKMUpperCutoffIndex A)
    i x

noncomputable def h3BKMSelectedMiddleGradientComponent2
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t A : ℝ)
    (i : Fin 3)
    (x : Point3) : ℂ :=
  h3BKMMiddleDyadicGradientComponent2
    u t
    0
    (h3BKMUpperCutoffIndex A)
    i x

/-! ## `L²` representative identities -/

theorem h3BKMSelectedMiddleGradientComponent0_ae_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    h3BKMSelectedMiddleGradientComponent0 u t A i := by

  change
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMMiddleDyadicGradientComponent0
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x)

  exact
    h3BKMMiddleLocalizedGradientComponent0InverseL2_toLp_ae_eq_physical
      hInt hMeas hFourier hEnvelope
      0
      (h3BKMUpperCutoffIndex A)
      i

theorem h3BKMSelectedMiddleGradientComponent1_ae_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    h3BKMSelectedMiddleGradientComponent1 u t A i := by

  change
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMMiddleDyadicGradientComponent1
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x)

  exact
    h3BKMMiddleLocalizedGradientComponent1InverseL2_toLp_ae_eq_physical
      hInt hMeas hFourier hEnvelope
      0
      (h3BKMUpperCutoffIndex A)
      i

theorem h3BKMSelectedMiddleGradientComponent2_ae_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    h3BKMSelectedMiddleGradientComponent2 u t A i := by

  change
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMMiddleDyadicGradientComponent2
        u t
        0
        (h3BKMUpperCutoffIndex A)
        i x)

  exact
    h3BKMMiddleLocalizedGradientComponent2InverseL2_toLp_ae_eq_physical
      hInt hMeas hFourier hEnvelope
      0
      (h3BKMUpperCutoffIndex A)
      i

/-! ## Everywhere logarithmic bounds -/

theorem norm_h3BKMSelectedMiddleGradientComponent0_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMSelectedMiddleGradientComponent0
        u t A i x‖
      ≤
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicGradientComponent0_selected_le
      hEnvelope A i x

theorem norm_h3BKMSelectedMiddleGradientComponent1_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMSelectedMiddleGradientComponent1
        u t A i x‖
      ≤
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicGradientComponent1_selected_le
      hEnvelope A i x

theorem norm_h3BKMSelectedMiddleGradientComponent2_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3)
    (x : Point3) :
    ‖h3BKMSelectedMiddleGradientComponent2
        u t A i x‖
      ≤
    2
      * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicGradientComponent2_selected_le
      hEnvelope A i x

end

end Euclidean
end Bridge
end PrimeTensor
