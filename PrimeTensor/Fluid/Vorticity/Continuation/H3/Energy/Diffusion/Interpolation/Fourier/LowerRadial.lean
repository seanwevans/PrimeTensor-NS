import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.FourthRadial
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy

/-!
# Zeroth and third radial Fourier moments for H³ interpolation

The top viscous block has now been identified exactly as

    D₃(t) = Σⱼ ∫ q(ξ)⁴ ‖ûⱼ(t,ξ)‖² dξ,

with `q = h3FourierGradientSquare`.

To put the interpolation problem into one common spectral language, this file
packages the matching lower moments

    M₀(t) = Σⱼ ∫ ‖ûⱼ(t,ξ)‖² dξ,

    M₃(t) = Σⱼ ∫ q(ξ)³ ‖ûⱼ(t,ξ)‖² dξ,

and proves the exact physical identities

    E₀(t) = M₀(t),
    E₃(t) = M₃(t).

No inequality is used here.  These are Plancherel plus the already-closed
order-three Fourier compatibility and the exact ordered third-symbol identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3InterpolationLowerRadial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3InterpolationLowerRadial :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Radial moment definitions -/

/-- Zeroth radial Fourier moment of the three velocity components. -/
noncomputable def velocityH3FourierZerothRadialMomentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ℝ :=
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

/-- Third radial Fourier moment of the three velocity components. -/
noncomputable def velocityH3FourierThirdRadialMomentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ℝ :=
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 3
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

/-! ## Third-symbol pointwise algebra -/

/-- The cubic radial density is exactly the complete ordered third-symbol
square density. -/
theorem h3FourierGradientSquare_cube_mul_norm_sq_eq_sum_symbol3
    (ξ : H3FourierPoint3)
    (F : ℂ) :
    h3FourierGradientSquare ξ ^ 3 * ‖F‖ ^ 2
      =
    ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖h3FourierDerivativeSymbol3 i k l ξ * F‖ ^ 2 := by

  rw [← sum_norm_h3FourierDerivativeSymbol3_sq ξ]

  simp_rw [
    norm_mul,
    mul_pow
  ]

  simp_rw [← Finset.sum_mul]

/-! ## Integrability and componentwise collapse of the cubic moment -/

/-- One ordered third-symbol square density is integrable. -/
theorem integrable_norm_h3FourierDerivativeSymbol3_mul_base_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k l : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3FourierDerivativeSymbol3 i k l ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  have hSlot :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3FourierJetAt
              u t hInt hMeas
              (h3JetSlot3 j i k l) ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt
        u t hInt hMeas
        (h3JetSlot3 j i k l))).norm.integrable_sq

  refine hSlot.congr ?_

  filter_upwards
    [velocityH3FourierCompatibleAt_orderThree
      hFourier j i k l]
    with ξ hξ

  rw [hξ]

/-- For one component, the ordered third-symbol moment is exactly the radial
cubic moment. -/
theorem sum_integral_symbol3_eq_integral_thirdRadial_component
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    (∑ i : Fin 3,
      ∑ k : Fin 3,
        ∑ l : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ‖h3FourierDerivativeSymbol3 i k l ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 3
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2 := by

  have h3 :
      ∀ i k l : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖h3FourierDerivativeSymbol3 i k l ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
          volume := by

    intro i k l

    exact
      integrable_norm_h3FourierDerivativeSymbol3_mul_base_sq
        hInt hMeas hFourier j i k l

  have h3int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ‖h3FourierDerivativeSymbol3 i k l ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2
        ∂volume)
        =
      ∑ i : Fin 3,
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ‖h3FourierDerivativeSymbol3 i k l ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2
            ∂volume := by

    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ‖h3FourierDerivativeSymbol3 i k l ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3,
              ∑ l : Fin 3,
                ‖h3FourierDerivativeSymbol3 i k l ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
          ∂volume := by

        simpa using
          (integral_finsetSum
            (μ := volume)
            Finset.univ
            (fun i _ => by
              apply integrable_finsetSum
              intro k hk
              apply integrable_finsetSum
              intro l hl
              simpa only [norm_mul] using h3 i k l))

      _ =
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ∑ l : Fin 3,
                ‖h3FourierDerivativeSymbol3 i k l ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
            ∂volume := by

        apply Finset.sum_congr rfl
        intro i hi

        simpa using
          (integral_finsetSum
            (μ := volume)
            Finset.univ
            (fun k _ => by
              apply integrable_finsetSum
              intro l hl
              simpa only [norm_mul] using h3 i k l))

      _ =
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ‖h3FourierDerivativeSymbol3 i k l ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
              ∂volume := by

        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk

        simpa using
          (integral_finsetSum
            (μ := volume)
            Finset.univ
            (fun l _ => by
              simpa only [norm_mul] using h3 i k l))

  calc
    (∑ i : Fin 3,
      ∑ k : Fin 3,
        ∑ l : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ‖h3FourierDerivativeSymbol3 i k l ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
      =
    ∫ ξ : H3FourierPoint3,
      ∑ i : Fin 3,
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            ‖h3FourierDerivativeSymbol3 i k l ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2
      ∂volume :=
      h3int.symm

    _ =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 3
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      apply integral_congr_ae

      filter_upwards with ξ

      exact
        (h3FourierGradientSquare_cube_mul_norm_sq_eq_sum_symbol3
          ξ
          (velocityH3BaseFourierAt
            u t hInt hMeas j ξ)).symm

/-! ## Exact physical/radial identities -/

/-- The physical kinetic block is exactly the zeroth radial Fourier moment. -/
theorem velocityH3Energy0At_eq_fourierZerothRadialMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    velocityH3Energy0At u t
      =
    velocityH3FourierZerothRadialMomentAt
      u t hInt hMeas := by

  unfold velocityH3FourierZerothRadialMomentAt

  calc
    velocityH3Energy0At u t
        =
      ∑ j : Fin 3,
        ‖velocityH3FourierJetAt
            u t hInt hMeas
            (h3JetSlot0 j)‖ ^ 2 := by

      symm

      simp_rw [
        velocityH3FourierJetAt_apply,
        norm_h3ScalarFourierL2
      ]

      simpa only [h3JetSlot0] using
        (velocityH3L2JetAt_squareEnergy0_eq
          hInt hMeas)

    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj

      simpa only [velocityH3BaseFourierAt] using
        (h3FourierComplexL2_norm_sq_eq_integral_norm_sq
          (velocityH3FourierJetAt
            u t hInt hMeas
            (h3JetSlot0 j)))

/-- The physical third-order H³ block is exactly the cubic radial Fourier
moment. -/
theorem velocityH3Energy3At_eq_fourierThirdRadialMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3Energy3At u t
      =
    velocityH3FourierThirdRadialMomentAt
      u t hInt hMeas := by

  unfold velocityH3FourierThirdRadialMomentAt

  have hEnergy :
      (∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas
                  (h3JetSlot3 j i k l)‖ ^ 2)
        =
      velocityH3Energy3At u t := by

    simp_rw [
      velocityH3FourierJetAt_apply,
      norm_h3ScalarFourierL2
    ]

    simpa only [
      h3JetSlot3,
      Fintype.sum_prod_type
    ] using
      (velocityH3L2JetAt_squareEnergy3_eq
        hInt hMeas)

  calc
    velocityH3Energy3At u t
        =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas
                  (h3JetSlot3 j i k l)‖ ^ 2 :=
      hEnergy.symm

    _ =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ‖velocityH3FourierJetAt
                    u t hInt hMeas
                    (h3JetSlot3 j i k l) ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl

      exact
        h3FourierComplexL2_norm_sq_eq_integral_norm_sq
          (velocityH3FourierJetAt
            u t hInt hMeas
            (h3JetSlot3 j i k l))

    _ =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ‖h3FourierDerivativeSymbol3 i k l ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl

      apply integral_congr_ae

      filter_upwards
        [velocityH3FourierCompatibleAt_orderThree
          hFourier j i k l]
        with ξ hξ

      rw [hξ]

    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 3
            *
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj

      exact
        sum_integral_symbol3_eq_integral_thirdRadial_component
          hInt hMeas hFourier j

/-! ## H³-path wrapper -/

/-- On an admissible H³ path, both lower physical blocks are their canonical
radial Fourier moments. -/
theorem h3Path_lowerRadialMomentIdentities
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes
        htAbs
    velocityH3Energy0At u t
      =
    velocityH3FourierZerothRadialMomentAt
      u t hInt hMeas
      ∧
    velocityH3Energy3At u t
      =
    velocityH3FourierThirdRadialMomentAt
      u t hInt hMeas := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      htAbs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      htAbs
      hInt

  exact
    ⟨
      velocityH3Energy0At_eq_fourierZerothRadialMoment
        hInt hMeas,
      velocityH3Energy3At_eq_fourierThirdRadialMoment
        hInt hMeas hFourier
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
