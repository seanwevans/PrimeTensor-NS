import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.LowerRadial
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Aggregate H³ Fourier moment density

The exact zeroth, third, and fourth radial moments are currently written as a
finite sum of three scalar-component integrals.  For the interpolation step it
is cleaner to combine those components first.

Define the nonnegative spectral mass density

    S(ξ) = Σⱼ ‖ûⱼ(ξ)‖².

Then

    M₀ = ∫ S,
    M₃ = ∫ q³ S,
    M₄ = ∫ q⁴ S,

where `M₄` is the top physical H³ dissipation block on the admissible path.

This file also introduces the intermediate second moment

    M₂ = ∫ q² S,

and proves its integrability from the existing order-two Fourier jet.  The
next file can therefore apply ordinary `2,2` Hölder/Cauchy--Schwarz to the
three scalar functions built from `S`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3InterpolationMomentDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3InterpolationMomentDensity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Aggregate spectral mass density -/

/-- Sum of the three componentwise Fourier square amplitudes. -/
noncomputable def velocityH3FourierMassDensityAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (ξ : H3FourierPoint3) :
    ℝ :=
  ∑ j : Fin 3,
    ‖velocityH3BaseFourierAt
        u t hInt hMeas j ξ‖ ^ 2

theorem velocityH3FourierMassDensityAt_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (ξ : H3FourierPoint3) :
    0 ≤ velocityH3FourierMassDensityAt
      u t hInt hMeas ξ := by
  unfold velocityH3FourierMassDensityAt
  exact
    Finset.sum_nonneg
      (fun j hj => by positivity)

theorem velocityH3FourierMassDensityAt_integrable
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    Integrable
      (velocityH3FourierMassDensityAt
        u t hInt hMeas)
      volume := by

  unfold velocityH3FourierMassDensityAt

  apply integrable_finsetSum
  intro j hj

  exact
    (MeasureTheory.Lp.memLp
      (velocityH3BaseFourierAt
        u t hInt hMeas j)).norm.integrable_sq

/-! ## Order-two radial moment -/

/-- Exact order-two pointwise radial/symbol identity. -/
theorem h3FourierGradientSquare_sq_mul_norm_sq_eq_sum_symbol2
    (ξ : H3FourierPoint3)
    (F : ℂ) :
    h3FourierGradientSquare ξ ^ 2 * ‖F‖ ^ 2
      =
    ∑ i : Fin 3, ∑ k : Fin 3,
      ‖h3FourierDerivativeSymbol2 i k ξ * F‖ ^ 2 := by

  rw [← sum_norm_h3FourierDerivativeSymbol2_sq ξ]

  simp_rw [
    norm_mul,
    mul_pow
  ]

  simp_rw [← Finset.sum_mul]

/-- One ordered second-symbol square density is integrable. -/
theorem integrable_norm_h3FourierDerivativeSymbol2_mul_base_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3FourierDerivativeSymbol2 i k ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  have hSlot :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3FourierJetAt
              u t hInt hMeas
              (h3JetSlot2 j i k) ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt
        u t hInt hMeas
        (h3JetSlot2 j i k))).norm.integrable_sq

  refine hSlot.congr ?_

  filter_upwards
    [velocityH3FourierCompatibleAt_orderTwo
      hFourier j i k]
    with ξ hξ

  rw [hξ]

/-- The scalar-component second radial density is integrable. -/
theorem integrable_h3FourierGradientSquare_sq_mul_base_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 2
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  have hsum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3,
            ‖h3FourierDerivativeSymbol2 i k ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
        volume := by

    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk

    simpa only [norm_mul] using
      (integrable_norm_h3FourierDerivativeSymbol2_mul_base_sq
        hInt hMeas hFourier j i k)

  refine hsum.congr ?_

  filter_upwards with ξ

  exact
    (h3FourierGradientSquare_sq_mul_norm_sq_eq_sum_symbol2
      ξ
      (velocityH3BaseFourierAt
        u t hInt hMeas j ξ)).symm

/-- Intermediate aggregate second radial moment. -/
noncomputable def velocityH3FourierSecondRadialMomentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ℝ :=
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 2
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

/-! ## Componentwise radial integrability for orders three and four -/

/-- The scalar-component cubic radial density is integrable. -/
theorem integrable_h3FourierGradientSquare_cube_mul_base_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 3
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  have hsum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖h3FourierDerivativeSymbol3 i k l ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
        volume := by

    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl

    simpa only [norm_mul] using
      (integrable_norm_h3FourierDerivativeSymbol3_mul_base_sq
        hInt hMeas hFourier j i k l)

  refine hsum.congr ?_

  filter_upwards with ξ

  exact
    (h3FourierGradientSquare_cube_mul_norm_sq_eq_sum_symbol3
      ξ
      (velocityH3BaseFourierAt
        u t hInt hMeas j ξ)).symm

/-- The scalar-component fourth radial density is integrable on a strict H³
energy-class slice. -/
theorem h3Path_integrable_h3FourierGradientSquare_four_mul_base_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 4
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  have hsum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ r : Fin 3,
            ‖h3FourierDerivativeSymbol4 i k l r ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
        volume := by

    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    apply integrable_finsetSum
    intro r hr

    simpa only [norm_mul] using
      (h3Path_integrable_norm_h3FourierDerivativeSymbol4_mul_base_sq
        hH3 hClass ht hInt hMeas hFourier j i k l r)

  refine hsum.congr ?_

  filter_upwards with ξ

  exact
    (h3FourierGradientSquare_four_mul_norm_sq_eq_sum_symbol4
      ξ
      (velocityH3BaseFourierAt
        u t hInt hMeas j ξ)).symm

/-! ## Aggregate integrability -/

theorem velocityH3FourierSecondAggregateDensity_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 2
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)
      volume := by

  unfold velocityH3FourierMassDensityAt
  simp_rw [Finset.mul_sum]

  apply integrable_finsetSum
  intro j hj

  exact
    integrable_h3FourierGradientSquare_sq_mul_base_norm_sq
      hInt hMeas hFourier j

theorem velocityH3FourierThirdAggregateDensity_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 3
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)
      volume := by

  unfold velocityH3FourierMassDensityAt
  simp_rw [Finset.mul_sum]

  apply integrable_finsetSum
  intro j hj

  exact
    integrable_h3FourierGradientSquare_cube_mul_base_norm_sq
      hInt hMeas hFourier j

theorem h3Path_velocityH3FourierFourthAggregateDensity_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 4
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)
      volume := by

  unfold velocityH3FourierMassDensityAt
  simp_rw [Finset.mul_sum]

  apply integrable_finsetSum
  intro j hj

  exact
    h3Path_integrable_h3FourierGradientSquare_four_mul_base_norm_sq
      hH3 hClass ht hInt hMeas hFourier j

/-! ## Collapse component sums into one spectral integral -/

theorem velocityH3FourierZerothRadialMomentAt_eq_integral_massDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    velocityH3FourierZerothRadialMomentAt
        u t hInt hMeas
      =
    ∫ ξ : H3FourierPoint3,
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ := by

  unfold
    velocityH3FourierZerothRadialMomentAt
    velocityH3FourierMassDensityAt

  symm

  simpa using
    (integral_finsetSum
      (μ := volume)
      Finset.univ
      (fun j _ =>
        (MeasureTheory.Lp.memLp
          (velocityH3BaseFourierAt
            u t hInt hMeas j)).norm.integrable_sq))

theorem velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierSecondRadialMomentAt
        u t hInt hMeas
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 2
        *
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ := by

  unfold
    velocityH3FourierSecondRadialMomentAt
    velocityH3FourierMassDensityAt

  calc
    (∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 2
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      =
    ∫ ξ : H3FourierPoint3,
      ∑ j : Fin 3,
        h3FourierGradientSquare ξ ^ 2
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      symm

      simpa using
        (integral_finsetSum
          (μ := volume)
          Finset.univ
          (fun j _ =>
            integrable_h3FourierGradientSquare_sq_mul_base_norm_sq
              hInt hMeas hFourier j))

    _ =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 2
          *
        ∑ j : Fin 3,
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      apply integral_congr_ae
      filter_upwards with ξ
      rw [Finset.mul_sum]

theorem velocityH3FourierThirdRadialMomentAt_eq_integral_massDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierThirdRadialMomentAt
        u t hInt hMeas
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 3
        *
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ := by

  unfold
    velocityH3FourierThirdRadialMomentAt
    velocityH3FourierMassDensityAt

  calc
    (∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 3
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      =
    ∫ ξ : H3FourierPoint3,
      ∑ j : Fin 3,
        h3FourierGradientSquare ξ ^ 3
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      symm

      simpa using
        (integral_finsetSum
          (μ := volume)
          Finset.univ
          (fun j _ =>
            integrable_h3FourierGradientSquare_cube_mul_base_norm_sq
              hInt hMeas hFourier j))

    _ =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 3
          *
        ∑ j : Fin 3,
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      apply integral_congr_ae
      filter_upwards with ξ
      rw [Finset.mul_sum]

theorem h3Path_velocityH3FourierFourthRadialMomentAt_eq_integral_massDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 4
        *
      velocityH3FourierMassDensityAt
        u t hInt hMeas ξ := by

  unfold
    velocityH3FourierFourthRadialMomentAt
    velocityH3FourierMassDensityAt

  calc
    (∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 4
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      =
    ∫ ξ : H3FourierPoint3,
      ∑ j : Fin 3,
        h3FourierGradientSquare ξ ^ 4
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      symm

      simpa using
        (integral_finsetSum
          (μ := volume)
          Finset.univ
          (fun j _ =>
            h3Path_integrable_h3FourierGradientSquare_four_mul_base_norm_sq
              hH3 hClass ht hInt hMeas hFourier j))

    _ =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 4
          *
        ∑ j : Fin 3,
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      apply integral_congr_ae
      filter_upwards with ξ
      rw [Finset.mul_sum]

end

end Euclidean
end Bridge
end PrimeTensor
