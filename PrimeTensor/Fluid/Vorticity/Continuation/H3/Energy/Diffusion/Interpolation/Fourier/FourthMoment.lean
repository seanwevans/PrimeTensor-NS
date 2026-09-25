import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.FourthCoordinate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Dissipation

/-!
# Assemble the top H³ dissipation as a fourth Fourier moment

`FourthCoordinate` identifies every ordered physical fourth derivative with its
corresponding fourth-symbol Fourier square integral.  This file performs only
the finite bookkeeping needed to assemble all such coordinates.

Define the finite fourth Fourier moment

    M₄(u,t)
      =
    Σⱼᵢₖₗᵣ ∫ ‖mᵢₖₗᵣ(ξ) ûⱼ(ξ)‖² dξ.

Then, on every strict H³ energy-class slice,

    velocityH3Dissipation3At u t = M₄(u,t).

No interchange between a finite sum and an integral is used yet.  That is kept
for the next analytic increment, where the fourth-symbol identity

    Σᵢₖₗᵣ ‖mᵢₖₗᵣ(ξ)‖² = q(ξ)⁴

will collapse `M₄` to the radial fourth moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3DissipationFourthMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3DissipationFourthMoment :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Five-axis finite sum transport -/

/-- Transport a five-axis `Fin 3` sum to the project's axis type. -/
theorem sum_fin3_comp_h3AxisOfFin3_five
    (f :
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      ℝ) :
    (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ r : Fin 3,
      f
        (h3AxisOfFin3 j)
        (h3AxisOfFin3 i)
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 l)
        (h3AxisOfFin3 r))
      =
    ∑ j : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            ∑ r : PrimeTensor.Axis Depth.three,
              f j i k l r := by

  calc
    (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ r : Fin 3,
      f
        (h3AxisOfFin3 j)
        (h3AxisOfFin3 i)
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 l)
        (h3AxisOfFin3 r))
        =
      ∑ j : Fin 3,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              ∑ r : PrimeTensor.Axis Depth.three,
                f (h3AxisOfFin3 j) i k l r := by

      apply Finset.sum_congr rfl
      intro j hj

      exact
        sum_fin3_comp_h3AxisOfFin3_four
          (fun i k l r =>
            f (h3AxisOfFin3 j) i k l r)

    _ =
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              ∑ r : PrimeTensor.Axis Depth.three,
                f j i k l r := by

      exact
        sum_fin3_comp_h3AxisOfFin3
          (fun j =>
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  ∑ r : PrimeTensor.Axis Depth.three,
                    f j i k l r)

/-! ## Spectral fourth moment -/

/--
Finite ordered fourth Fourier moment of the three velocity components.

The proof arguments `hInt` and `hMeas` enter only through the canonical base
Fourier representatives.
-/
noncomputable def velocityH3FourierFourthMomentAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ℝ :=
  ∑ j : Fin 3,
    ∑ i : Fin 3,
      ∑ k : Fin 3,
        ∑ l : Fin 3,
          ∑ r : Fin 3,
            ∫ ξ : H3FourierPoint3,
              ‖h3FourierDerivativeSymbol4 i k l r ξ
                  *
                velocityH3BaseFourierAt
                  u t hInt hMeas j ξ‖ ^ 2

/-! ## Exact physical/spectral identification -/

/--
The top positive H³ viscous dissipation block is exactly the finite fourth
Fourier moment.
-/
theorem velocityH3Dissipation3At_eq_fourierFourthMoment
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
    velocityH3FourierFourthMomentAt
      u t hInt hMeas := by

  unfold velocityH3Dissipation3At
  unfold velocityH3FourierFourthMomentAt

  rw [
    ←
      sum_fin3_comp_h3AxisOfFin3_five
        (fun j i k l r =>
          spatialSquareEnergy
            (spatial3.d r
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))))))
  ]

  apply Finset.sum_congr rfl
  intro j hj

  apply Finset.sum_congr rfl
  intro i hi

  apply Finset.sum_congr rfl
  intro k hk

  apply Finset.sum_congr rfl
  intro l hl

  apply Finset.sum_congr rfl
  intro r hr

  exact
    spatialSquareEnergy_fourthVelocityJet_eq_integral_symbol4
      hInt
      hMeas
      hFourier
      j i k l r
      (h3Path_thirdVelocityJet_spatialC1
        hClass ht j i k l)
      (h3Path_fourthVelocityJet_memLp2
        hH3 hClass ht j i k l r)

/--
Canonical path wrapper using the integrability, measurability, and Fourier
compatibility already supplied by an admissible H³ path.
-/
theorem velocityH3Dissipation3At_eq_fourierFourthMoment_on_h3Path
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
    velocityH3FourierFourthMomentAt
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
    velocityH3Dissipation3At_eq_fourierFourthMoment
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
