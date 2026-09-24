import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Gradient.Localized.Physical

/-!
# BKM endpoint: physical representatives of one-shell gradient states

The one-shell inverse-gradient `L²` states have already been assembled from the
three localized inverse-curl states,

    G₀ = C01⁻¹(i,1) + C02⁻¹(i,2),
    G₁ = C12⁻¹(i,2) - C01⁻¹(i,0),
    G₂ = -(C02⁻¹(i,0) + C12⁻¹(i,1)).

The individual inverse-curl states have physical representatives with the exact
vorticity signs

    -C12⁻¹  ~  K * ωₓ,
     C02⁻¹  ~  K * ωᵧ,
    -C01⁻¹  ~  K * ω_z.

This file performs only the corresponding `Lp` representative algebra and
records the three resulting one-shell physical gradient identities:

    G₀ ~ -Kᵢ₁ * ω_z + Kᵢ₂ * ωᵧ,
    G₁ ~  Kᵢ₀ * ω_z - Kᵢ₂ * ωₓ,
    G₂ ~ -Kᵢ₀ * ωᵧ + Kᵢ₁ * ωₓ.

The next checkpoint can sum these identities over the finite dyadic middle
window without reopening any curl-sign bookkeeping.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicLocalizedGradientPhysicalRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicLocalizedGradientPhysicalRepresentative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Target velocity component 0 -/

/--
The target-component `0` one-shell inverse-gradient state is represented a.e.
by `-Kᵢ₁ * ω_z + Kᵢ₂ * ωᵧ`.
-/
theorem h3BKMDyadicLocalizedGradientComponent0InverseL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMDyadicLocalizedGradientComponent0InverseL2
          hFourier R hR i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      -
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 1)
          (h3BKMPhysicalVorticityZ u t)
          x
        +
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 2)
          (h3BKMPhysicalVorticityY u t)
          x) := by

  let A : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl01InverseL2
      hFourier R hR i 1

  let B : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl02InverseL2
      hFourier R hR i 2

  have hAdd :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_add A B)

  have hNegA :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg A)

  have hZ :=
    h3BKMLocalizedCanonicalCurl01InverseL2_neg_toLp_ae_eq_physicalZ
      hInt hMeas hFourier hEnvelope hR i 1

  have hY :=
    h3BKMLocalizedCanonicalCurl02InverseL2_toLp_ae_eq_physicalY
      hInt hMeas hFourier hEnvelope hR i 2

  filter_upwards [hAdd, hNegA, hZ, hY] with x hAddx hNegAx hZx hYx

  simp only [Function.comp_apply] at hAddx hNegAx

  have hA :
      (A : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        =
      -
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 1)
          (h3BKMPhysicalVorticityZ u t)
          x := by

    calc
      (A : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
          =
        -
          ((-A : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x) := by
            rw [hNegAx]
            simp

      _ =
        -
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel R hR i 1)
            (h3BKMPhysicalVorticityZ u t)
            x := by
          rw [hZx]

  change
    ((A + B : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
      =
    -
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i 1)
        (h3BKMPhysicalVorticityZ u t)
        x
      +
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i 2)
        (h3BKMPhysicalVorticityY u t)
        x

  rw [hAddx]
  simp only [Pi.add_apply]
  rw [hA, hYx]

/-! ## Target velocity component 1 -/

/--
The target-component `1` one-shell inverse-gradient state is represented a.e.
by `Kᵢ₀ * ω_z - Kᵢ₂ * ωₓ`.
-/
theorem h3BKMDyadicLocalizedGradientComponent1InverseL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMDyadicLocalizedGradientComponent1InverseL2
          hFourier R hR i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 0)
          (h3BKMPhysicalVorticityZ u t)
          x
        -
      h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 2)
          (h3BKMPhysicalVorticityX u t)
          x) := by

  let A : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl12InverseL2
      hFourier R hR i 2

  let B : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl01InverseL2
      hFourier R hR i 0

  have hSub :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_sub A B)

  have hNegA :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg A)

  have hNegB :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg B)

  have hX :=
    h3BKMLocalizedCanonicalCurl12InverseL2_neg_toLp_ae_eq_physicalX
      hInt hMeas hFourier hEnvelope hR i 2

  have hZ :=
    h3BKMLocalizedCanonicalCurl01InverseL2_neg_toLp_ae_eq_physicalZ
      hInt hMeas hFourier hEnvelope hR i 0

  filter_upwards [hSub, hNegA, hNegB, hX, hZ] with
      x hSubx hNegAx hNegBx hXx hZx

  simp only [Function.comp_apply] at hSubx hNegAx hNegBx

  have hA :
      (A : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        =
      -
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 2)
          (h3BKMPhysicalVorticityX u t)
          x := by

    calc
      (A : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
          =
        -
          ((-A : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x) := by
            rw [hNegAx]
            simp

      _ =
        -
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel R hR i 2)
            (h3BKMPhysicalVorticityX u t)
            x := by
          rw [hXx]

  have hB :
      (B : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        =
      -
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 0)
          (h3BKMPhysicalVorticityZ u t)
          x := by

    calc
      (B : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
          =
        -
          ((-B : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x) := by
            rw [hNegBx]
            simp

      _ =
        -
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel R hR i 0)
            (h3BKMPhysicalVorticityZ u t)
            x := by
          rw [hZx]

  change
    ((A - B : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
      =
    h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i 0)
        (h3BKMPhysicalVorticityZ u t)
        x
      -
    h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i 2)
        (h3BKMPhysicalVorticityX u t)
        x

  rw [hSubx]
  simp only [Pi.sub_apply]
  rw [hA, hB]
  ring

/-! ## Target velocity component 2 -/

/--
The target-component `2` one-shell inverse-gradient state is represented a.e.
by `-Kᵢ₀ * ωᵧ + Kᵢ₁ * ωₓ`.
-/
theorem h3BKMDyadicLocalizedGradientComponent2InverseL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMDyadicLocalizedGradientComponent2InverseL2
          hFourier R hR i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      -
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 0)
          (h3BKMPhysicalVorticityY u t)
          x
        +
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 1)
          (h3BKMPhysicalVorticityX u t)
          x) := by

  let A : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl02InverseL2
      hFourier R hR i 0

  let B : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl12InverseL2
      hFourier R hR i 1

  have hAdd :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_add A B)

  have hNegAdd :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg (A + B))

  have hNegB :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg B)

  have hY :=
    h3BKMLocalizedCanonicalCurl02InverseL2_toLp_ae_eq_physicalY
      hInt hMeas hFourier hEnvelope hR i 0

  have hX :=
    h3BKMLocalizedCanonicalCurl12InverseL2_neg_toLp_ae_eq_physicalX
      hInt hMeas hFourier hEnvelope hR i 1

  filter_upwards [hAdd, hNegAdd, hNegB, hY, hX] with
      x hAddx hNegAddx hNegBx hYx hXx

  simp only [Function.comp_apply] at hAddx hNegAddx hNegBx

  have hB :
      (B : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        =
      -
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i 1)
          (h3BKMPhysicalVorticityX u t)
          x := by

    calc
      (B : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
          =
        -
          ((-B : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x) := by
            rw [hNegBx]
            simp

      _ =
        -
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel R hR i 1)
            (h3BKMPhysicalVorticityX u t)
            x := by
          rw [hXx]

  change
    ((-(A + B) : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
      =
    -
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i 0)
        (h3BKMPhysicalVorticityY u t)
        x
      +
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i 1)
        (h3BKMPhysicalVorticityX u t)
        x

  rw [hNegAddx]
  simp only [Pi.neg_apply]
  rw [hAddx]
  simp only [Pi.add_apply]
  rw [hYx, hB]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
