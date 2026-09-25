import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.FourthMoment

/-!
# Collapse the top H³ dissipation to the radial fourth Fourier moment

`FourthMoment` identifies the physical top dissipation block with the finite
ordered fourth-symbol moment

    Σⱼᵢₖₗᵣ ∫ ‖mᵢₖₗᵣ(ξ) ûⱼ(ξ)‖² dξ.

The fourth-symbol algebra gives pointwise

    Σᵢₖₗᵣ ‖mᵢₖₗᵣ(ξ) F‖²
      =
    q(ξ)⁴ ‖F‖²,

where `q = h3FourierGradientSquare`.

This file supplies the one remaining analytic detail: each fourth-symbol
density is integrable because it is almost everywhere the squared norm of the
Fourier transform of an already-closed physical fourth derivative.  We may
therefore commute the four derivative-index sums through the integral and
collapse them pointwise.

The resulting exact identity is

    velocityH3Dissipation3At u t
      =
    Σⱼ ∫ q(ξ)⁴ ‖ûⱼ(t,ξ)‖² dξ.

This is the fourth moment needed for the upcoming
`E₃⁴ ≤ E₀ D₃³` interpolation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3DissipationFourthRadial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3DissipationFourthRadial :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Integrability of one fourth-symbol density -/

/--
One fourth-symbol square density is integrable whenever the corresponding
physical third derivative is spatially `C¹` and its next derivative is in
`L²`.
-/
theorem integrable_norm_h3FourierDerivativeSymbol4_mul_base_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k l r : Fin 3)
    (hThirdC1 :
      SpatialC1
        (spatial3.d (h3AxisOfFin3 i)
          (spatial3.d (h3AxisOfFin3 k)
            (spatial3.d (h3AxisOfFin3 l)
              (loggedVelocityComponent
                u t (h3AxisOfFin3 j))))))
    (hFourth :
      MemLp
        (spatial3.d (h3AxisOfFin3 r)
          (spatial3.d (h3AxisOfFin3 i)
            (spatial3.d (h3AxisOfFin3 k)
              (spatial3.d (h3AxisOfFin3 l)
                (loggedVelocityComponent
                  u t (h3AxisOfFin3 j))))))
        2
        (volume : Measure Point3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3FourierDerivativeSymbol4 i k l r ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  let f3 : ScalarField3 :=
    spatial3.d (h3AxisOfFin3 i)
      (spatial3.d (h3AxisOfFin3 k)
        (spatial3.d (h3AxisOfFin3 l)
          (loggedVelocityComponent
            u t (h3AxisOfFin3 j))))

  let f4 : ScalarField3 :=
    spatial3.d (h3AxisOfFin3 r) f3

  have hf3 :
      MemLp f3 2 (volume : Measure Point3) := by
    dsimp only [f3]
    simpa [
      velocityH3JetFieldAt,
      h3JetSlot3
    ] using
      (velocityH3JetFieldAt_memLp2
        hInt hMeas
        (h3JetSlot3 j i k l))

  have hFourth' :
      MemLp f4 2 (volume : Measure Point3) := by
    simpa only [f4, f3] using hFourth

  have hThirdC1' :
      SpatialC1 f3 := by
    simpa only [f3] using hThirdC1

  have hFourthRaw :
      (h3ScalarFourierL2
          (hFourth'.toLp f4) :
          H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol r ξ
          *
        h3ScalarFourierL2
          (hf3.toLp f3) ξ) := by

    simpa only [f4] using
      (h3ScalarFourierL2_spatialDerivative_fin_ae
        hThirdC1'
        r
        hf3
        hFourth')

  have hThirdTransform :
      h3ScalarFourierL2 (hf3.toLp f3)
        =
      velocityH3FourierJetAt
        u t hInt hMeas
        (h3JetSlot3 j i k l) := by

    rw [velocityH3FourierJetAt_eq_scalarJetField]

    simpa [
      f3,
      velocityH3JetFieldAt,
      h3JetSlot3
    ] using
      (h3ScalarFourierL2_toLp_proof_irrel
        hf3
        (velocityH3JetFieldAt_memLp2
          hInt hMeas
          (h3JetSlot3 j i k l)))

  rw [hThirdTransform] at hFourthRaw

  have hThird :=
    velocityH3FourierCompatibleAt_orderThree
      hFourier
      j i k l

  have hFourthAE :
      (h3ScalarFourierL2
          (hFourth'.toLp f4) :
          H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol4 i k l r ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ) := by

    filter_upwards
      [hFourthRaw, hThird]
      with ξ h4 h3

    rw [h4, h3]

    unfold h3FourierDerivativeSymbol4

    ring

  have hFourierSq :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3ScalarFourierL2
              (hFourth'.toLp f4) ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp
      (h3ScalarFourierL2
        (hFourth'.toLp f4))).norm.integrable_sq

  refine hFourierSq.congr ?_

  filter_upwards [hFourthAE] with ξ hξ

  rw [hξ]

/-! ## Path-level coordinate integrability -/

/-- Every fourth-symbol density occurring in the top dissipation moment is
integrable on a strict H³ energy-class slice. -/
theorem h3Path_integrable_norm_h3FourierDerivativeSymbol4_mul_base_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k l r : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3FourierDerivativeSymbol4 i k l r ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2)
      volume := by

  exact
    integrable_norm_h3FourierDerivativeSymbol4_mul_base_sq
      hInt
      hMeas
      hFourier
      j i k l r
      (h3Path_thirdVelocityJet_spatialC1
        hClass ht j i k l)
      (h3Path_fourthVelocityJet_memLp2
        hH3 hClass ht j i k l r)

/-! ## Radial fourth moment -/

/-- Radial fourth Fourier moment of the three velocity components. -/
noncomputable def velocityH3FourierFourthRadialMomentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ℝ :=
  ∑ j : Fin 3,
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 4
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

/--
For one velocity component, the finite fourth-symbol moment is exactly the
radial fourth moment.
-/
theorem sum_integral_symbol4_eq_integral_fourthRadial_component
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
    (∑ i : Fin 3,
      ∑ k : Fin 3,
        ∑ l : Fin 3,
          ∑ r : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ‖h3FourierDerivativeSymbol4 i k l r ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2)
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 4
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2 := by

  have h4 :
      ∀ i k l r : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖h3FourierDerivativeSymbol4 i k l r ξ
                *
              velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
          volume := by

    intro i k l r

    exact
      h3Path_integrable_norm_h3FourierDerivativeSymbol4_mul_base_sq
        hH3
        hClass
        ht
        hInt
        hMeas
        hFourier
        j i k l r

  have h4int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ∑ r : Fin 3,
                ‖h3FourierDerivativeSymbol4 i k l r ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
        ∂volume)
        =
      ∑ i : Fin 3,
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            ∑ r : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ‖h3FourierDerivativeSymbol4 i k l r ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
              ∂volume := by

    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ∑ r : Fin 3,
                ‖h3FourierDerivativeSymbol4 i k l r ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3,
              ∑ l : Fin 3,
                ∑ r : Fin 3,
                  ‖h3FourierDerivativeSymbol4 i k l r ξ
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
              apply integrable_finsetSum
              intro r hr
              simpa only [norm_mul] using h4 i k l r))

      _ =
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ∑ l : Fin 3,
                ∑ r : Fin 3,
                  ‖h3FourierDerivativeSymbol4 i k l r ξ
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
              apply integrable_finsetSum
              intro r hr
              simpa only [norm_mul] using h4 i k l r))

      _ =
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ∑ r : Fin 3,
                  ‖h3FourierDerivativeSymbol4 i k l r ξ
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
              apply integrable_finsetSum
              intro r hr
              simpa only [norm_mul] using h4 i k l r))

      _ =
        ∑ i : Fin 3,
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              ∑ r : Fin 3,
                ∫ ξ : H3FourierPoint3,
                  ‖h3FourierDerivativeSymbol4 i k l r ξ
                      *
                    velocityH3BaseFourierAt
                      u t hInt hMeas j ξ‖ ^ 2
                ∂volume := by

        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl

        simpa using
          (integral_finsetSum
            (μ := volume)
            Finset.univ
            (fun r _ => h4 i k l r))

  symm

  calc
    (∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 4
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂volume)
      =
    ∫ ξ : H3FourierPoint3,
      ∑ i : Fin 3,
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            ∑ r : Fin 3,
              ‖h3FourierDerivativeSymbol4 i k l r ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

      apply integral_congr_ae

      filter_upwards with ξ

      exact
        h3FourierGradientSquare_four_mul_norm_sq_eq_sum_symbol4
          ξ
          (velocityH3BaseFourierAt
            u t hInt hMeas j ξ)

    _ =
      ∑ i : Fin 3,
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            ∑ r : Fin 3,
              ∫ ξ : H3FourierPoint3,
                ‖h3FourierDerivativeSymbol4 i k l r ξ
                    *
                  velocityH3BaseFourierAt
                    u t hInt hMeas j ξ‖ ^ 2
              ∂volume :=
      h4int

/--
The finite ordered fourth Fourier moment is exactly the radial fourth moment.
-/
theorem velocityH3FourierFourthMomentAt_eq_radial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierFourthMomentAt
        u t hInt hMeas
      =
    velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas := by

  unfold velocityH3FourierFourthMomentAt
  unfold velocityH3FourierFourthRadialMomentAt

  apply Finset.sum_congr rfl
  intro j hj

  exact
    sum_integral_symbol4_eq_integral_fourthRadial_component
      hH3
      hClass
      ht
      hInt
      hMeas
      hFourier
      j

/-!
## Exact top-dissipation radial identity
-/

/--
The physical top H³ dissipation block is exactly the radial fourth Fourier
moment at every strict H³ energy-class time.
-/
theorem velocityH3Dissipation3At_eq_fourierFourthRadialMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3Dissipation3At u t
      =
    velocityH3FourierFourthRadialMomentAt
      u t hInt hMeas := by

  calc
    velocityH3Dissipation3At u t
        =
      velocityH3FourierFourthMomentAt
        u t hInt hMeas :=
      velocityH3Dissipation3At_eq_fourierFourthMoment
        hH3
        hClass
        ht
        hInt
        hMeas
        hFourier

    _ =
      velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas :=
      velocityH3FourierFourthMomentAt_eq_radial
        hH3
        hClass
        ht
        hInt
        hMeas
        hFourier

/--
Canonical H³-path wrapper for the exact radial fourth-moment identity.
-/
theorem velocityH3Dissipation3At_eq_fourierFourthRadialMoment_on_h3Path
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
    velocityH3Dissipation3At u t
      =
    velocityH3FourierFourthRadialMomentAt
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
    velocityH3Dissipation3At_eq_fourierFourthRadialMoment
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
