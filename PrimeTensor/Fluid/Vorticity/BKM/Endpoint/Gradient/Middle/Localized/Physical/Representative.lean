import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Gradient.Localized.Physical.Representative
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Middle.Localized.Physical

/-!
# BKM endpoint: physical representatives of finite middle-gradient states

The one-shell inverse-gradient states now have the exact physical
representatives

    G₀,n ~ -Kᵢ₁,n * ω_z + Kᵢ₂,n * ωᵧ,
    G₁,n ~  Kᵢ₀,n * ω_z - Kᵢ₂,n * ωₓ,
    G₂,n ~ -Kᵢ₀,n * ωᵧ + Kᵢ₁,n * ωₓ.

The finite middle `L²` states are defined by summing these one-shell states over
`Finset.Icc lo hi`, while the physical middle proxies are defined by the same
finite sums of physical convolutions.

This file performs that finite summation and proves that all three middle `L²`
states represent their concrete physical middle-gradient proxies almost
everywhere.  No new analytic estimate is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointMiddleLocalizedGradientPhysicalRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointMiddleLocalizedGradientPhysicalRepresentative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Component 0 -/

/--
The finite middle inverse-gradient state for target velocity component `0`
represents the concrete physical middle proxy almost everywhere.
-/
theorem h3BKMMiddleLocalizedGradientComponent0InverseL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (lo hi : ℕ)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier lo hi i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMMiddleDyadicGradientComponent0
        u t lo hi i x) := by

  have hSum :=
    h3FourierComplexL2_finsetSum_toLp_ae
      (Finset.Icc lo hi)
      (fun n =>
        h3BKMDyadicLocalizedGradientComponent0InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)

  have hShell :
      ∀ᵐ x ∂(volume : Measure Point3),
        ∀ n ∈ Finset.Icc lo hi,
          (h3BKMDyadicLocalizedGradientComponent0InverseL2
              hFourier
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i :
              H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)
            =
          -
            h3BKMPhysicalConvolution
              (h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 1)
              (h3BKMPhysicalVorticityZ u t)
              x
            +
            h3BKMPhysicalConvolution
              (h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 2)
              (h3BKMPhysicalVorticityY u t)
              x := by
    exact
      (Finset.eventually_all (Finset.Icc lo hi)).2
        (fun n _hn =>
          h3BKMDyadicLocalizedGradientComponent0InverseL2_toLp_ae_eq_physical
            hInt hMeas hFourier hEnvelope
            (h3BKMDyadicRadius_pos n)
            i)

  filter_upwards [hSum, hShell] with x hSumx hShellx

  unfold h3BKMMiddleLocalizedGradientComponent0InverseL2
  rw [hSumx]

  calc
    ∑ n ∈ Finset.Icc lo hi,
        (h3BKMDyadicLocalizedGradientComponent0InverseL2
            hFourier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i :
            H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        =
      ∑ n ∈ Finset.Icc lo hi,
        (-
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i 1)
            (h3BKMPhysicalVorticityZ u t)
            x
          +
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i 2)
            (h3BKMPhysicalVorticityY u t)
            x) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hShellx n hn

    _ =
      h3BKMMiddleDyadicGradientComponent0
        u t lo hi i x := by
      unfold
        h3BKMMiddleDyadicGradientComponent0
        h3BKMMiddleDyadicShellSum
        h3BKMPhysicalDyadicShellSum
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_neg_distrib]

/-! ## Component 1 -/

/--
The finite middle inverse-gradient state for target velocity component `1`
represents the concrete physical middle proxy almost everywhere.
-/
theorem h3BKMMiddleLocalizedGradientComponent1InverseL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (lo hi : ℕ)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier lo hi i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMMiddleDyadicGradientComponent1
        u t lo hi i x) := by

  have hSum :=
    h3FourierComplexL2_finsetSum_toLp_ae
      (Finset.Icc lo hi)
      (fun n =>
        h3BKMDyadicLocalizedGradientComponent1InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)

  have hShell :
      ∀ᵐ x ∂(volume : Measure Point3),
        ∀ n ∈ Finset.Icc lo hi,
          (h3BKMDyadicLocalizedGradientComponent1InverseL2
              hFourier
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i :
              H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)
            =
          h3BKMPhysicalConvolution
              (h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 0)
              (h3BKMPhysicalVorticityZ u t)
              x
            -
            h3BKMPhysicalConvolution
              (h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 2)
              (h3BKMPhysicalVorticityX u t)
              x := by
    exact
      (Finset.eventually_all (Finset.Icc lo hi)).2
        (fun n _hn =>
          h3BKMDyadicLocalizedGradientComponent1InverseL2_toLp_ae_eq_physical
            hInt hMeas hFourier hEnvelope
            (h3BKMDyadicRadius_pos n)
            i)

  filter_upwards [hSum, hShell] with x hSumx hShellx

  unfold h3BKMMiddleLocalizedGradientComponent1InverseL2
  rw [hSumx]

  calc
    ∑ n ∈ Finset.Icc lo hi,
        (h3BKMDyadicLocalizedGradientComponent1InverseL2
            hFourier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i :
            H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        =
      ∑ n ∈ Finset.Icc lo hi,
        (h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i 0)
            (h3BKMPhysicalVorticityZ u t)
            x
          -
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i 2)
            (h3BKMPhysicalVorticityX u t)
            x) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hShellx n hn

    _ =
      h3BKMMiddleDyadicGradientComponent1
        u t lo hi i x := by
      unfold
        h3BKMMiddleDyadicGradientComponent1
        h3BKMMiddleDyadicShellSum
        h3BKMPhysicalDyadicShellSum
      simp only [sub_eq_add_neg]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_neg_distrib]

/-! ## Component 2 -/

/--
The finite middle inverse-gradient state for target velocity component `2`
represents the concrete physical middle proxy almost everywhere.
-/
theorem h3BKMMiddleLocalizedGradientComponent2InverseL2_toLp_ae_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (lo hi : ℕ)
    (i : Fin 3) :
    (fun x : Point3 =>
      (h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier lo hi i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMMiddleDyadicGradientComponent2
        u t lo hi i x) := by

  have hSum :=
    h3FourierComplexL2_finsetSum_toLp_ae
      (Finset.Icc lo hi)
      (fun n =>
        h3BKMDyadicLocalizedGradientComponent2InverseL2
          hFourier
          (h3BKMDyadicRadius n)
          (h3BKMDyadicRadius_pos n)
          i)

  have hShell :
      ∀ᵐ x ∂(volume : Measure Point3),
        ∀ n ∈ Finset.Icc lo hi,
          (h3BKMDyadicLocalizedGradientComponent2InverseL2
              hFourier
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i :
              H3FourierPoint3 → ℂ)
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)
            =
          -
            h3BKMPhysicalConvolution
              (h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 0)
              (h3BKMPhysicalVorticityY u t)
              x
            +
            h3BKMPhysicalConvolution
              (h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i 1)
              (h3BKMPhysicalVorticityX u t)
              x := by
    exact
      (Finset.eventually_all (Finset.Icc lo hi)).2
        (fun n _hn =>
          h3BKMDyadicLocalizedGradientComponent2InverseL2_toLp_ae_eq_physical
            hInt hMeas hFourier hEnvelope
            (h3BKMDyadicRadius_pos n)
            i)

  filter_upwards [hSum, hShell] with x hSumx hShellx

  unfold h3BKMMiddleLocalizedGradientComponent2InverseL2
  rw [hSumx]

  calc
    ∑ n ∈ Finset.Icc lo hi,
        (h3BKMDyadicLocalizedGradientComponent2InverseL2
            hFourier
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i :
            H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        =
      ∑ n ∈ Finset.Icc lo hi,
        (-
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i 0)
            (h3BKMPhysicalVorticityY u t)
            x
          +
          h3BKMPhysicalConvolution
            (h3BKMDyadicPhysicalKernel
              (h3BKMDyadicRadius n)
              (h3BKMDyadicRadius_pos n)
              i 1)
            (h3BKMPhysicalVorticityX u t)
            x) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hShellx n hn

    _ =
      h3BKMMiddleDyadicGradientComponent2
        u t lo hi i x := by
      unfold
        h3BKMMiddleDyadicGradientComponent2
        h3BKMMiddleDyadicShellSum
        h3BKMPhysicalDyadicShellSum
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_neg_distrib]

end

end Euclidean
end Bridge
end PrimeTensor
