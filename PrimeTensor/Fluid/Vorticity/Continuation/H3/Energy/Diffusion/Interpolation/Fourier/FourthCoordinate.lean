import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.FourthSymbol
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Velocity.Jet.Four.Arbitrary.Closure

/-!
# Exact physical/Fourier bridge for one fourth H³ derivative coordinate

The fourth-symbol algebra is now closed.  Before summing the full top viscous
block, identify one ordered fourth physical derivative exactly with its Fourier
multiplier density.

For a component `j` and ordered derivative axes `i,k,l,r`, write

    f₃ = ∂ᵢ ∂ₖ ∂ₗ uⱼ,
    f₄ = ∂ᵣ f₃.

If `f₃` is spatially `C¹` and `f₄ ∈ L²`, the existing first-derivative Fourier
theorem gives

    Fourier(f₄)
      =
    mᵣ Fourier(f₃)

almost everywhere.  Combining this with the already-closed order-three Fourier
compatibility gives

    Fourier(f₄)
      =
    mᵢₖₗᵣ Fourier(uⱼ)

almost everywhere.

Plancherel then yields the exact scalar square-energy identity

    spatialSquareEnergy(f₄)
      =
    ∫ ‖mᵢₖₗᵣ(ξ) Fourier(uⱼ)(ξ)‖² dξ.

The terminal H³ energy class already supplies both required hypotheses:
spatial `C¹` for the third jet follows from its `C⁵` justification class, and
the arbitrary fourth physical jet is already closed in `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3DissipationFourthCoordinate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3DissipationFourthCoordinate :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Analytic hypotheses already supplied by the path -/

/-- Every ordered third derivative is spatially `C¹` on a strict H³
energy-class slice. -/
theorem h3Path_thirdVelocityJet_spatialC1
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i k l : Fin 3) :
    SpatialC1
      (spatial3.d (h3AxisOfFin3 i)
        (spatial3.d (h3AxisOfFin3 k)
          (spatial3.d (h3AxisOfFin3 l)
            (loggedVelocityComponent
              u t (h3AxisOfFin3 j))))) := by

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hkl3 :
      SpatialC3
        (spatial3.d (h3AxisOfFin3 k)
          (spatial3.d (h3AxisOfFin3 l)
            (loggedVelocityComponent
              u t (h3AxisOfFin3 j)))) := by
    exact
      hClass.velocity_spatial_five
        t
        htTail
        (h3AxisOfFin3 j)
        (h3AxisOfFin3 k)
        (h3AxisOfFin3 l)

  exact
    (hkl3.partialDeriv_contDiff_two
      (h3AxisOfFin3 i)).of_le
      (by norm_num)

/-- Every ordered fourth derivative belongs to physical `L²` on a strict H³
energy-class slice. -/
theorem h3Path_fourthVelocityJet_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i k l r : Fin 3) :
    MemLp
      (spatial3.d (h3AxisOfFin3 r)
        (spatial3.d (h3AxisOfFin3 i)
          (spatial3.d (h3AxisOfFin3 k)
            (spatial3.d (h3AxisOfFin3 l)
              (loggedVelocityComponent
                u t (h3AxisOfFin3 j))))))
      2
      (volume : Measure Point3) := by

  exact
    h3PathEnergyClassProducesArbitraryFourthVelocityJetMemLp2_closed
      u T hH3 a hClass t ht
      (h3AxisOfFin3 r)
      (h3AxisOfFin3 i)
      (h3AxisOfFin3 k)
      (h3AxisOfFin3 l)
      (h3AxisOfFin3 j)

/-! ## One-coordinate exact Fourier identity -/

/--
One ordered fourth physical derivative has exactly the square energy of the
corresponding fourth Fourier multiplier of the base component.
-/
theorem spatialSquareEnergy_fourthVelocityJet_eq_integral_symbol4
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
    spatialSquareEnergy
        (spatial3.d (h3AxisOfFin3 r)
          (spatial3.d (h3AxisOfFin3 i)
            (spatial3.d (h3AxisOfFin3 k)
              (spatial3.d (h3AxisOfFin3 l)
                (loggedVelocityComponent
                  u t (h3AxisOfFin3 j))))))
      =
    ∫ ξ : H3FourierPoint3,
      ‖h3FourierDerivativeSymbol4 i k l r ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2 := by

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

  have hPhysicalNorm :
      ‖h3ScalarFourierL2 (hFourth'.toLp f4)‖ ^ 2
        =
      spatialSquareEnergy f4 := by

    rw [norm_h3ScalarFourierL2]

    exact
      norm_toLp_sq_eq_spatialSquareEnergy
        hFourth'

  calc
    spatialSquareEnergy
        (spatial3.d (h3AxisOfFin3 r)
          (spatial3.d (h3AxisOfFin3 i)
            (spatial3.d (h3AxisOfFin3 k)
              (spatial3.d (h3AxisOfFin3 l)
                (loggedVelocityComponent
                  u t (h3AxisOfFin3 j))))))
        =
      spatialSquareEnergy f4 := by
        rfl

    _ =
      ‖h3ScalarFourierL2
          (hFourth'.toLp f4)‖ ^ 2 :=
        hPhysicalNorm.symm

    _ =
      ∫ ξ : H3FourierPoint3,
        ‖h3ScalarFourierL2
            (hFourth'.toLp f4) ξ‖ ^ 2 :=
      h3FourierComplexL2_norm_sq_eq_integral_norm_sq
        (h3ScalarFourierL2
          (hFourth'.toLp f4))

    _ =
      ∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol4 i k l r ξ
            *
          velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2 := by

      apply integral_congr_ae

      filter_upwards [hFourthAE] with ξ hξ

      rw [hξ]

end

end Euclidean
end Bridge
end PrimeTensor
