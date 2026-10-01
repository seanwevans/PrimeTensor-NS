import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityDissipationAngularConcentration
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.MomentDensity

/-!
# Identify the full H³ dissipation with its radial Fourier moment

The preceding terminal reduction isolates the surviving angular obstruction in
the spectral density

    q(ξ) |G(ξ)|²,

where `G = W₃ û` is the weighted H³ spectral state. Since

    W₃² = 1 + q + q² + q³,

this is exactly

    (q + q² + q³ + q⁴) |û|².

The top block `q⁴` is already identified with `velocityH3Dissipation3At`.
The lower interpolation layer already contains the `q²`, `q³`, and `q⁴`
radial moments, but the exact first- and second-energy identifications needed
to assemble the *full* physical dissipation have not yet been packaged.

This file closes that bookkeeping gap:

* `E₁` is exactly the first radial moment `∫ q |û|²`;
* `E₂` is exactly the second radial moment `∫ q² |û|²`;
* `D₀ = E₁`, `D₁ = E₂`, and `D₂ = E₃` by finite index reordering;
* therefore

      velocityH3DissipationAt
        = M₁ + M₂ + M₃ + M₄.

No estimate is used. This is an exact Plancherel/Fourier-symbol identity and
provides the physical target for the terminal angular concentration channel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationFourierIdentification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationFourierIdentification :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## First radial moment -/

/-- First radial Fourier moment of the three velocity components. -/
noncomputable def velocityH3FourierFirstRadialMomentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ℝ :=
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

/-- The first radial density is exactly the complete ordered first-symbol
square density. -/
theorem h3FourierGradientSquare_mul_norm_sq_eq_sum_symbol1
    (ξ : H3FourierPoint3)
    (F : ℂ) :
    h3FourierGradientSquare ξ * ‖F‖ ^ 2
      =
    ∑ i : Fin 3,
      ‖h3FourierDerivativeSymbol i ξ * F‖ ^ 2 := by

  rw [← sum_norm_h3FourierDerivativeSymbol_sq ξ]

  simp_rw [
    norm_mul,
    mul_pow
  ]

  rw [← Finset.sum_mul]

/-- One ordered first-symbol square density is integrable. -/
theorem integrable_norm_h3FourierDerivativeSymbol_mul_base_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  have hSlot :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3FourierJetAt
              u t hInt hMeas
              (h3JetSlot1 j i) ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt
        u t hInt hMeas
        (h3JetSlot1 j i))).norm.integrable_sq

  refine hSlot.congr ?_

  filter_upwards
    [velocityH3FourierCompatibleAt_orderOne
      hFourier j i]
    with ξ hξ

  rw [hξ]

/-- The scalar-component first radial density is integrable. -/
theorem integrable_h3FourierGradientSquare_mul_base_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  have hsum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3,
            ‖h3FourierDerivativeSymbol i ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
        volume := by

    apply integrable_finsetSum
    intro i hi

    exact
      integrable_norm_h3FourierDerivativeSymbol_mul_base_sq
        hInt hMeas hFourier j i

  refine hsum.congr ?_

  filter_upwards with ξ

  exact
    (h3FourierGradientSquare_mul_norm_sq_eq_sum_symbol1
      ξ
      (velocityH3BaseFourierAt
        u t hInt hMeas j ξ)).symm

/-- For one velocity component, the ordered first-symbol moment is exactly the
first radial moment. -/
theorem sum_integral_symbol1_eq_integral_firstRadial_component
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    (∑ i : Fin 3,
      ∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2 := by

  have h1 :
      ∀ i : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖h3FourierDerivativeSymbol i ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
          volume := by

    intro i

    exact
      integrable_norm_h3FourierDerivativeSymbol_mul_base_sq
        hInt hMeas hFourier j i

  calc
    (∑ i : Fin 3,
      ∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol i ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
        =
      ∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ‖h3FourierDerivativeSymbol i ξ
              *
            velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2
        ∂volume := by

      symm

      simpa using
        (integral_finsetSum
          (μ := volume)
          Finset.univ
          (fun i _ => h1 i))

    _ =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
        ∂volume := by

      apply integral_congr_ae

      filter_upwards with ξ

      exact
        (h3FourierGradientSquare_mul_norm_sq_eq_sum_symbol1
          ξ
          (velocityH3BaseFourierAt
            u t hInt hMeas j ξ)).symm

/-! ## Exact lower physical/radial identities -/

/-- The physical first-order H³ energy block is exactly the first radial
Fourier moment. -/
theorem velocityH3Energy1At_eq_fourierFirstRadialMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3Energy1At u t
      =
    velocityH3FourierFirstRadialMomentAt
      u t hInt hMeas := by

  unfold velocityH3FourierFirstRadialMomentAt

  have hEnergy :
      (∑ j : Fin 3,
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt
              u t hInt hMeas
              (h3JetSlot1 j i)‖ ^ 2)
        =
      velocityH3Energy1At u t := by

    simp_rw [
      velocityH3FourierJetAt_apply,
      norm_h3ScalarFourierL2
    ]

    simpa only [
      h3JetSlot1,
      Fintype.sum_prod_type
    ] using
      (velocityH3L2JetAt_squareEnergy1_eq
        hInt hMeas)

  calc
    velocityH3Energy1At u t
        =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt
              u t hInt hMeas
              (h3JetSlot1 j i)‖ ^ 2 :=
      hEnergy.symm

    _ =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas
                (h3JetSlot1 j i) ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi

      exact
        h3FourierComplexL2_norm_sq_eq_integral_norm_sq
          (velocityH3FourierJetAt
            u t hInt hMeas
            (h3JetSlot1 j i))

    _ =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ‖h3FourierDerivativeSymbol i ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi

      apply integral_congr_ae

      filter_upwards
        [velocityH3FourierCompatibleAt_orderOne
          hFourier j i]
        with ξ hξ

      rw [hξ]

    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ
            *
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj

      exact
        sum_integral_symbol1_eq_integral_firstRadial_component
          hInt hMeas hFourier j

/-- The physical second-order H³ energy block is exactly the second radial
Fourier moment already defined by the interpolation layer. -/
theorem velocityH3Energy2At_eq_fourierSecondRadialMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3Energy2At u t
      =
    velocityH3FourierSecondRadialMomentAt
      u t hInt hMeas := by

  unfold velocityH3FourierSecondRadialMomentAt

  have hEnergy :
      (∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas
                (h3JetSlot2 j i k)‖ ^ 2)
        =
      velocityH3Energy2At u t := by

    simp_rw [
      velocityH3FourierJetAt_apply,
      norm_h3ScalarFourierL2
    ]

    simpa only [
      h3JetSlot2,
      Fintype.sum_prod_type
    ] using
      (velocityH3L2JetAt_squareEnergy2_eq
        hInt hMeas)

  calc
    velocityH3Energy2At u t
        =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas
                (h3JetSlot2 j i k)‖ ^ 2 :=
      hEnergy.symm

    _ =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas
                  (h3JetSlot2 j i k) ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk

      exact
        h3FourierComplexL2_norm_sq_eq_integral_norm_sq
          (velocityH3FourierJetAt
            u t hInt hMeas
            (h3JetSlot2 j i k))

    _ =
      ∑ j : Fin 3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ‖h3FourierDerivativeSymbol2 i k ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk

      apply integral_congr_ae

      filter_upwards
        [velocityH3FourierCompatibleAt_orderTwo
          hFourier j i k]
        with ξ hξ

      rw [hξ]

    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 2
            *
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2 := by

      apply Finset.sum_congr rfl
      intro j hj

      have h2 :
          ∀ i k : Fin 3,
            Integrable
              (fun ξ : H3FourierPoint3 =>
                ‖h3FourierDerivativeSymbol2 i k ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2)
              volume := by

        intro i k

        exact
          integrable_norm_h3FourierDerivativeSymbol2_mul_base_sq
            hInt hMeas hFourier j i k

      have h2int :
          (∫ ξ : H3FourierPoint3,
            ∑ i : Fin 3,
              ∑ k : Fin 3,
                ‖h3FourierDerivativeSymbol2 i k ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
            ∂volume)
            =
          ∑ i : Fin 3,
            ∑ k : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ‖h3FourierDerivativeSymbol2 i k ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
              ∂volume := by

        calc
          (∫ ξ : H3FourierPoint3,
            ∑ i : Fin 3,
              ∑ k : Fin 3,
                ‖h3FourierDerivativeSymbol2 i k ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
            ∂volume)
              =
            ∑ i : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ∑ k : Fin 3,
                  ‖h3FourierDerivativeSymbol2 i k ξ
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
                  simpa only [norm_mul] using h2 i k))

          _ =
            ∑ i : Fin 3,
              ∑ k : Fin 3,
                ∫ ξ : H3FourierPoint3,
                  ‖h3FourierDerivativeSymbol2 i k ξ
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
                  simpa only [norm_mul] using h2 i k))

      calc
        (∑ i : Fin 3,
          ∑ k : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ‖h3FourierDerivativeSymbol2 i k ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2)
            =
          ∫ ξ : H3FourierPoint3,
            ∑ i : Fin 3,
              ∑ k : Fin 3,
                ‖h3FourierDerivativeSymbol2 i k ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
            ∂volume :=
          h2int.symm

        _ =
          ∫ ξ : H3FourierPoint3,
            h3FourierGradientSquare ξ ^ 2
              *
            ‖velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2
            ∂volume := by

          apply integral_congr_ae

          filter_upwards with ξ

          exact
            (h3FourierGradientSquare_sq_mul_norm_sq_eq_sum_symbol2
              ξ
              (velocityH3BaseFourierAt
                u t hInt hMeas j ξ)).symm

/-! ## Physical dissipation block reindexing -/

/-- The lowest positive dissipation block is definitionally the first-order H³
energy block. -/
theorem velocityH3Dissipation0At_eq_energy1
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    velocityH3Dissipation0At u t
      =
    velocityH3Energy1At u t := by

  rfl

/-- The second positive dissipation block is the second-order H³ energy block,
after exchanging the two finite derivative indices. -/
theorem velocityH3Dissipation1At_eq_energy2
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    velocityH3Dissipation1At u t
      =
    velocityH3Energy2At u t := by

  unfold
    velocityH3Dissipation1At
    velocityH3Energy2At

  apply Finset.sum_congr rfl
  intro j hj

  rw [Finset.sum_comm]

/-- The third positive dissipation block is the third-order H³ energy block,
after cyclically moving the outer physical derivative index to the front. -/
theorem velocityH3Dissipation2At_eq_energy3
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    velocityH3Dissipation2At u t
      =
    velocityH3Energy3At u t := by

  unfold
    velocityH3Dissipation2At
    velocityH3Energy3At

  apply Finset.sum_congr rfl
  intro j hj

  let F :
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      ℝ :=
    fun a b c =>
      spatialSquareEnergy
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (loggedVelocityComponent u t j))))

  change
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ r : PrimeTensor.Axis Depth.three,
          F r i k)
      =
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          F i k l

  calc
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ r : PrimeTensor.Axis Depth.three,
          F r i k)
        =
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ r : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            F r i k := by

      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

    _ =
      ∑ r : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            F r i k := by

      rw [Finset.sum_comm]

    _ =
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            F i k l := by

      rfl

/-! ## Full physical/radial dissipation identity -/

/-- Sum of the four positive radial moments corresponding to the full H³
viscous dissipation. -/
noncomputable def velocityH3FourierFullDissipationRadialMomentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ℝ :=
  velocityH3FourierFirstRadialMomentAt
      u t hInt hMeas
    +
  velocityH3FourierSecondRadialMomentAt
      u t hInt hMeas
    +
  velocityH3FourierThirdRadialMomentAt
      u t hInt hMeas
    +
  velocityH3FourierFourthRadialMomentAt
      u t hInt hMeas

/-- Exact physical/Fourier identity for the full positive H³ dissipation. -/
theorem velocityH3DissipationAt_eq_fourierFullDissipationRadialMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3DissipationAt u t
      =
    velocityH3FourierFullDissipationRadialMomentAt
      u t hInt hMeas := by

  unfold
    velocityH3DissipationAt
    velocityH3FourierFullDissipationRadialMomentAt

  rw [
    velocityH3Dissipation0At_eq_energy1,
    velocityH3Dissipation1At_eq_energy2,
    velocityH3Dissipation2At_eq_energy3,
    velocityH3Energy1At_eq_fourierFirstRadialMoment
      hInt hMeas hFourier,
    velocityH3Energy2At_eq_fourierSecondRadialMoment
      hInt hMeas hFourier,
    velocityH3Energy3At_eq_fourierThirdRadialMoment
      hInt hMeas hFourier,
    velocityH3Dissipation3At_eq_fourierFourthRadialMoment
      hH3 hClass ht hInt hMeas hFourier
  ]

/-- Canonical H³-path wrapper for the exact full dissipation radial identity. -/
theorem velocityH3DissipationAt_eq_fourierFullDissipationRadialMoment_on_h3Path
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
    velocityH3DissipationAt u t
      =
    velocityH3FourierFullDissipationRadialMomentAt
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
    velocityH3DissipationAt_eq_fourierFullDissipationRadialMoment
      hH3
      hClass
      ht
      hInt
      hMeas
      hFourier

end

end Euclidean
end Bridge
end PrimeTensor
