import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Holder.Real

/-!
# Third-order H³ interpolation: specialization to spatialEnergyPairing

`spatialEnergyPairing` was elaborated under the product measure-space built with
`axisFintypeH3EnergyDerivative`.  We recreate that exact local instance here so
the generic real 2-4-4 Hölder bridge specializes definitionally to the project
pairing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

/--
Use the exact axis `Fintype` witness that was present when
`spatialEnergyPairing` was elaborated.
-/
noncomputable local instance axisFintypeH3HolderPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3EnergyDerivative d

/--
Use the exact product measure-space underlying `spatialEnergyPairing`.
-/
noncomputable local instance point3MeasureSpaceH3HolderPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3EnergyDerivative Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The generic real 2-4-4 theorem specialized to the exact spatial measure used by
`spatialEnergyPairing`.
-/
theorem enorm_spatialEnergyPairing_mul_le_244
    {f g q : ScalarField3}
    (
      hF :
        AEMeasurable
          (fun x : Point3 => ‖f x‖ₑ)
          MeasureTheory.volume
    )
    (
      hG :
        AEMeasurable
          (fun x : Point3 => ‖g x‖ₑ)
          MeasureTheory.volume
    )
    (
      hQ :
        AEMeasurable
          (fun x : Point3 => ‖q x‖ₑ)
          MeasureTheory.volume
    ) :
    ‖
      spatialEnergyPairing
        f
        (fun x : Point3 => g x * q x)
    ‖ₑ
      ≤
    ‖(2 : ℝ)‖ₑ
      *
    (
      realLpEnorm MeasureTheory.volume 2 f
        *
      (
        realLpEnorm MeasureTheory.volume 4 g
          *
        realLpEnorm MeasureTheory.volume 4 q
      )
    ) := by

  unfold spatialEnergyPairing

  change
    ‖
      2
        *
      (
        ∫ x : Point3,
          f x * (g x * q x)
      )
    ‖ₑ
      ≤
    ‖(2 : ℝ)‖ₑ
      *
    (
      realLpEnorm MeasureTheory.volume 2 f
        *
      (
        realLpEnorm MeasureTheory.volume 4 g
          *
        realLpEnorm MeasureTheory.volume 4 q
      )
    )

  exact
    enorm_two_mul_integral_three_mul_le_244
      MeasureTheory.volume
      hF hG hQ

end Euclidean
end Bridge
end PrimeTensor
