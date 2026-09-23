import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPhysicalL2EnergyOldBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Classical.Overlap

/-!
# Selected physical L² energy: identify the canonical zeroth-order energy

The previous bridge removed the physical `L²` representation layer and showed

    ‖S(q)‖²
      = ∑ i : Fin 3,
          spatialSquareEnergy
            (loggedVelocityComponent u (t + q) (h3AxisOfFin3 i)).

The only difference from `velocityH3Energy0At` is the finite coordinate index.
The already-established maps

    Fin 3 ↔ Axis Depth.three

are genuine two-sided inverses, so they define an equivalence.  Reindexing the
finite sum along that equivalence gives the literal canonical zeroth-order
energy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPhysicalL2EnergyAxisBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The project coordinate maps form an explicit equivalence between the three
spectral coordinates and the intrinsic depth-three axes. -/
def h3Fin3EquivAxisThree :
    Fin 3 ≃ PrimeTensor.Axis Depth.three where
  toFun := h3AxisOfFin3
  invFun := h3ClassicalizationFinOfAxis
  left_inv := h3ClassicalizationFinOfAxis_h3AxisOfFin3
  right_inv := h3AxisOfFin3_h3ClassicalizationFinOfAxis

@[simp]
theorem h3Fin3EquivAxisThree_apply
    (i : Fin 3) :
    h3Fin3EquivAxisThree i = h3AxisOfFin3 i := by
  rfl

/-- Reindex any real-valued three-coordinate sum from `Fin 3` to the intrinsic
PrimeTensor depth-three axis type. -/
theorem sum_fin3_h3AxisOfFin3_eq_sum_axis_three
    (F : PrimeTensor.Axis Depth.three → ℝ) :
    (∑ i : Fin 3, F (h3AxisOfFin3 i))
      =
    ∑ j : PrimeTensor.Axis Depth.three, F j := by
  exact
    Fintype.sum_equiv
      h3Fin3EquivAxisThree
      (fun i : Fin 3 => F (h3AxisOfFin3 i))
      F
      (fun i => rfl)

/-- Under selected/old physical agreement, the selected physical Hilbert norm
square is literally the canonical zeroth-order H³ energy of the old branch at
the corresponding absolute time. -/
theorem norm_sq_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_velocityH3Energy0At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        q
        hNS ht hE hTail) :
    ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail q‖ ^ 2
      =
    velocityH3Energy0At u (t + q) := by
  rw [
    norm_sq_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_old_fin3_energy
      hNS ht hE hTail hAgreement
  ]

  unfold velocityH3Energy0At

  exact
    sum_fin3_h3AxisOfFin3_eq_sum_axis_three
      (fun j : PrimeTensor.Axis Depth.three =>
        spatialSquareEnergy
          (loggedVelocityComponent u (t + q) j))

/-- Radius-wide physical agreement gives the same canonical zeroth-order energy
identity at every positive overlap point that remains before the old terminal
time. -/
theorem norm_sq_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_velocityH3Energy0At_of_restartRadiusAgreement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (q :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (hEnd : t + (q : ℝ) < T) :
    ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ)‖ ^ 2
      =
    velocityH3Energy0At u (t + (q : ℝ)) := by
  exact
    norm_sq_h3PreterminalSelectedVelocityPhysicalL2HilbertAt_eq_velocityH3Energy0At
      hNS ht hE hTail
      (hPhysical q hEnd)

end

end Euclidean
end Bridge
end PrimeTensor
