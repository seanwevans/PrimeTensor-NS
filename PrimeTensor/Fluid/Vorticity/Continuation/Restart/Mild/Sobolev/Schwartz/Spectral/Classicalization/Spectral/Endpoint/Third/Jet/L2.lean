import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Endpoint.Third.Jet.AE

/-!
# Classicalization: integrated endpoint estimate in zeroth/third H³ jet coordinates

`SpectralEndpointThirdJetAE` proves the pointwise almost-everywhere inequality

    |G_t - G_s|²
      ≤
    3 ( |F⁰_t - F⁰_s|²
        + Σᵢₖₗ |F³_{t,ikl} - F³_{s,ikl}|² ).

This file integrates that estimate.

The endpoint density on the right is integrable because every concrete Fourier
jet slot is an `L²` class.  Its integral is exactly the finite sum of squared
`L²` distances of the zeroth and ordered third-order Fourier jets.  The weighted
raw representative on the left is likewise integrable because it is almost
everywhere the representative of the genuine weighted spectral `L²` state.

Consequently the complete weighted scalar H³ spectral distance is controlled
by only the zeroth and third-order Fourier-jet distances.

No Navier--Stokes evolution theorem is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSpectralEndpointThirdJetL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Zeroth-plus-third ordered Fourier-jet difference square density for one
velocity component. -/
def velocityH3FourierComponentEndpointDifferenceSquareDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t s : ℝ)
    (hIntT : VelocityH3IntegrableAt u t)
    (hMeasT : VelocityH3MeasurableAt u t)
    (hIntS : VelocityH3IntegrableAt u s)
    (hMeasS : VelocityH3MeasurableAt u s)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  ‖velocityH3FourierJetAt
      u t hIntT hMeasT (h3JetSlot0 j) ξ
      -
    velocityH3FourierJetAt
      u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
    +
  ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    ‖velocityH3FourierJetAt
        u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
        -
      velocityH3FourierJetAt
        u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2

/-- The endpoint difference density is integrable. -/
theorem velocityH3FourierComponentEndpointDifferenceSquareDensity_integrable
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t s : ℝ)
    (hIntT : VelocityH3IntegrableAt u t)
    (hMeasT : VelocityH3MeasurableAt u t)
    (hIntS : VelocityH3IntegrableAt u s)
    (hMeasS : VelocityH3MeasurableAt u s)
    (j : Fin 3) :
    Integrable
      (velocityH3FourierComponentEndpointDifferenceSquareDensity
        u t s hIntT hMeasT hIntS hMeasS j)
      volume := by
  have h0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3FourierJetAt
              u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt
              u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2)
        volume :=
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (velocityH3FourierJetAt
        u t hIntT hMeasT (h3JetSlot0 j))
      (velocityH3FourierJetAt
        u s hIntS hMeasS (h3JetSlot0 j))

  have h3 :
      ∀ i k l : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)
          volume := by
    intro i k l
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (velocityH3FourierJetAt
          u t hIntT hMeasT (h3JetSlot3 j i k l))
        (velocityH3FourierJetAt
          u s hIntS hMeasS (h3JetSlot3 j i k l))

  have h3sum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)
        volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    exact h3 i k l

  unfold velocityH3FourierComponentEndpointDifferenceSquareDensity
  exact h0.add h3sum

/-- The endpoint density integrates to the finite zeroth-plus-third squared
`L²` jet distance. -/
theorem integral_velocityH3FourierComponentEndpointDifferenceSquareDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t s : ℝ)
    (hIntT : VelocityH3IntegrableAt u t)
    (hMeasT : VelocityH3MeasurableAt u t)
    (hIntS : VelocityH3IntegrableAt u s)
    (hMeasS : VelocityH3MeasurableAt u s)
    (j : Fin 3) :
    (∫ ξ : H3FourierPoint3,
      velocityH3FourierComponentEndpointDifferenceSquareDensity
        u t s hIntT hMeasT hIntS hMeasS j ξ
      ∂volume)
      =
    ‖velocityH3FourierJetAt
        u t hIntT hMeasT (h3JetSlot0 j)
        -
      velocityH3FourierJetAt
        u s hIntS hMeasS (h3JetSlot0 j)‖ ^ 2
      +
    ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖velocityH3FourierJetAt
          u t hIntT hMeasT (h3JetSlot3 j i k l)
          -
        velocityH3FourierJetAt
          u s hIntS hMeasS (h3JetSlot3 j i k l)‖ ^ 2 := by
  have h0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3FourierJetAt
              u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt
              u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2)
        volume :=
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (velocityH3FourierJetAt
        u t hIntT hMeasT (h3JetSlot0 j))
      (velocityH3FourierJetAt
        u s hIntS hMeasS (h3JetSlot0 j))

  have h3 :
      ∀ i k l : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)
          volume := by
    intro i k l
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (velocityH3FourierJetAt
          u t hIntT hMeasT (h3JetSlot3 j i k l))
        (velocityH3FourierJetAt
          u s hIntS hMeasS (h3JetSlot3 j i k l))

  have h3sum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)
        volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    exact h3 i k l

  have h3int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt
              u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
              -
            velocityH3FourierJetAt
              u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
        =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt
              u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
              -
            velocityH3FourierJetAt
              u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
          ∂volume := by
    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt
              u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
              -
            velocityH3FourierJetAt
              u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                  -
                velocityH3FourierJetAt
                  u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
          ∂volume := by
            simpa using
              (integral_finsetSum (μ := volume) Finset.univ
                (fun i _ => by
                  apply integrable_finsetSum
                  intro k hk
                  apply integrable_finsetSum
                  intro l hl
                  exact h3 i k l))
      _ =
        ∑ i : Fin 3, ∑ k : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                  -
                velocityH3FourierJetAt
                  u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
          ∂volume := by
            apply Finset.sum_congr rfl
            intro i hi
            simpa using
              (integral_finsetSum (μ := volume) Finset.univ
                (fun k _ => by
                  apply integrable_finsetSum
                  intro l hl
                  exact h3 i k l))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        simpa using
          (integral_finsetSum (μ := volume) Finset.univ
            (fun l _ => h3 i k l))

  unfold velocityH3FourierComponentEndpointDifferenceSquareDensity
  rw [integral_add h0 h3sum, h3int]
  simp_rw [
    ← h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
  ]

/-- The weighted raw Fourier difference is integrable, because it is almost
everywhere the pointwise difference of the two genuine weighted spectral
`L²` states. -/
theorem velocityH3WeightedBaseFourierRaw_sub_norm_sq_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t s : ℝ}
    {hIntT : VelocityH3IntegrableAt u t}
    {hMeasT : VelocityH3MeasurableAt u t}
    {hIntS : VelocityH3IntegrableAt u s}
    {hMeasS : VelocityH3MeasurableAt u s}
    (hFourierT :
      VelocityH3FourierCompatibleAt u t hIntT hMeasT)
    (hFourierS :
      VelocityH3FourierCompatibleAt u s hIntS hMeasS)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖velocityH3WeightedBaseFourierRaw
            u t hIntT hMeasT j ξ
            -
          velocityH3WeightedBaseFourierRaw
            u s hIntS hMeasS j ξ‖ ^ 2)
      volume := by
  have hState :=
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (velocityH3SpectralScalarAt
        u t hIntT hMeasT hFourierT j)
      (velocityH3SpectralScalarAt
        u s hIntS hMeasS hFourierS j)

  refine hState.congr ?_

  filter_upwards
    [velocityH3SpectralScalarAt_ae hFourierT j,
     velocityH3SpectralScalarAt_ae hFourierS j]
    with ξ hT hS

  rw [hT, hS]

/-- Exact identification of the scalar spectral `L²` distance with the integral
of the two weighted raw representatives. -/
theorem norm_velocityH3SpectralScalarAt_sub_sq_eq_integral_weightedRaw
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t s : ℝ}
    {hIntT : VelocityH3IntegrableAt u t}
    {hMeasT : VelocityH3MeasurableAt u t}
    {hIntS : VelocityH3IntegrableAt u s}
    {hMeasS : VelocityH3MeasurableAt u s}
    (hFourierT :
      VelocityH3FourierCompatibleAt u t hIntT hMeasT)
    (hFourierS :
      VelocityH3FourierCompatibleAt u s hIntS hMeasS)
    (j : Fin 3) :
    ‖velocityH3SpectralScalarAt
        u t hIntT hMeasT hFourierT j
        -
      velocityH3SpectralScalarAt
        u s hIntS hMeasS hFourierS j‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖velocityH3WeightedBaseFourierRaw
          u t hIntT hMeasT j ξ
          -
        velocityH3WeightedBaseFourierRaw
          u s hIntS hMeasS j ξ‖ ^ 2
      ∂volume := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  let GT : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hIntT hMeasT hFourierT j

  let GS : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u s hIntS hMeasS hFourierS j

  filter_upwards
    [MeasureTheory.Lp.coeFn_sub GT GS,
     velocityH3SpectralScalarAt_ae hFourierT j,
     velocityH3SpectralScalarAt_ae hFourierS j]
    with ξ hSub hT hS

  calc
    ‖((GT - GS : H3SpectralScalarState) :
        H3FourierPoint3 → ℂ) ξ‖ ^ 2
        =
      ‖(GT : H3FourierPoint3 → ℂ) ξ
          -
        (GS : H3FourierPoint3 → ℂ) ξ‖ ^ 2 := by
          simpa only [Pi.sub_apply] using
            congrArg
              (fun z : ℂ => ‖z‖ ^ 2)
              hSub
    _ =
      ‖velocityH3WeightedBaseFourierRaw
          u t hIntT hMeasT j ξ
          -
        velocityH3WeightedBaseFourierRaw
          u s hIntS hMeasS j ξ‖ ^ 2 := by
          rw [hT, hS]

/-- Integrated endpoint interpolation for one scalar velocity component:
the complete weighted H³ spectral distance is controlled by only the zeroth
and ordered third-jet Fourier distances. -/
theorem norm_velocityH3SpectralScalarAt_sub_sq_le_three_base_third
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t s : ℝ}
    {hIntT : VelocityH3IntegrableAt u t}
    {hMeasT : VelocityH3MeasurableAt u t}
    {hIntS : VelocityH3IntegrableAt u s}
    {hMeasS : VelocityH3MeasurableAt u s}
    (hFourierT :
      VelocityH3FourierCompatibleAt u t hIntT hMeasT)
    (hFourierS :
      VelocityH3FourierCompatibleAt u s hIntS hMeasS)
    (j : Fin 3) :
    ‖velocityH3SpectralScalarAt
        u t hIntT hMeasT hFourierT j
        -
      velocityH3SpectralScalarAt
        u s hIntS hMeasS hFourierS j‖ ^ 2
      ≤
    3 *
      (‖velocityH3FourierJetAt
          u t hIntT hMeasT (h3JetSlot0 j)
          -
        velocityH3FourierJetAt
          u s hIntS hMeasS (h3JetSlot0 j)‖ ^ 2
        +
       ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
         ‖velocityH3FourierJetAt
             u t hIntT hMeasT (h3JetSlot3 j i k l)
             -
           velocityH3FourierJetAt
             u s hIntS hMeasS (h3JetSlot3 j i k l)‖ ^ 2) := by
  rw [
    norm_velocityH3SpectralScalarAt_sub_sq_eq_integral_weightedRaw
      hFourierT hFourierS j
  ]

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3WeightedBaseFourierRaw
              u t hIntT hMeasT j ξ
              -
            velocityH3WeightedBaseFourierRaw
              u s hIntS hMeasS j ξ‖ ^ 2)
        volume :=
    velocityH3WeightedBaseFourierRaw_sub_norm_sq_integrable
      hFourierT hFourierS j

  have hEndpoint :
      Integrable
        (velocityH3FourierComponentEndpointDifferenceSquareDensity
          u t s hIntT hMeasT hIntS hMeasS j)
        volume :=
    velocityH3FourierComponentEndpointDifferenceSquareDensity_integrable
      u t s hIntT hMeasT hIntS hMeasS j

  have hRight :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          3 *
            velocityH3FourierComponentEndpointDifferenceSquareDensity
              u t s hIntT hMeasT hIntS hMeasS j ξ)
        volume :=
    hEndpoint.const_mul 3

  have hAE :
      (fun ξ : H3FourierPoint3 =>
        ‖velocityH3WeightedBaseFourierRaw
            u t hIntT hMeasT j ξ
            -
          velocityH3WeightedBaseFourierRaw
            u s hIntS hMeasS j ξ‖ ^ 2)
        ≤ᵐ[volume]
      (fun ξ : H3FourierPoint3 =>
        3 *
          velocityH3FourierComponentEndpointDifferenceSquareDensity
            u t s hIntT hMeasT hIntS hMeasS j ξ) := by
    simpa only [
      velocityH3FourierComponentEndpointDifferenceSquareDensity
    ] using
      (velocityH3WeightedBaseFourierRaw_sub_norm_sq_le_three_base_third_ae
        hFourierT hFourierS j)

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖velocityH3WeightedBaseFourierRaw
            u t hIntT hMeasT j ξ
            -
          velocityH3WeightedBaseFourierRaw
            u s hIntS hMeasS j ξ‖ ^ 2
        ∂volume)
        ≤
      ∫ ξ : H3FourierPoint3,
        3 *
          velocityH3FourierComponentEndpointDifferenceSquareDensity
            u t s hIntT hMeasT hIntS hMeasS j ξ
        ∂volume :=
    integral_mono_ae hLeft hRight hAE

  rw [integral_const_mul] at hIntegral
  rw [
    integral_velocityH3FourierComponentEndpointDifferenceSquareDensity
      u t s hIntT hMeasT hIntS hMeasS j
  ] at hIntegral

  exact hIntegral

end

end Euclidean
end Bridge
end PrimeTensor
