import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.L2.Jet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyContinuity

/-!
# Scalar H³ energy continuity from strong physical L²-jet continuity

The concrete H³ restart state already has 120 real `L²` coordinates and the
exact normalized identity

    1 + h3L2JetSquareEnergy (velocityH3L2JetAt ...)
      =
    velocityH3EnergyAt u t.

Therefore strong continuity of every physical H³ `L²` jet coordinate implies
continuity of the scalar canonical H³ energy by finite-dimensional Hilbert
calculus alone.

No differentiation under a spatial integral, mixed higher time derivative, or
dominated-convergence hypothesis appears in this bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EnergyFromL2Jet
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The finite 120-coordinate `L²` square-energy observable is continuous. -/
theorem continuous_h3L2JetSquareEnergy :
    Continuous h3L2JetSquareEnergy := by
  unfold h3L2JetSquareEnergy

  apply continuous_finset_sum
  intro a ha

  exact
    (continuous_norm.comp
      (continuous_apply a)).pow 2

/-- Coordinatewise strong continuity of the canonical physical H³ `L²` jet
implies continuity of its finite sum-of-squares energy. -/
theorem continuous_h3PreterminalCanonicalL2JetSquareEnergyOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL2 :
      H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3L2JetSquareEnergy
          (fun a : H3JetIndex =>
            h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q)) := by
  unfold h3L2JetSquareEnergy

  apply continuous_finset_sum
  intro a ha

  exact
    (continuous_norm.comp
      (hL2 a)).pow 2

/-- Exact normalized energy identity along the canonical elapsed physical
`L²`-jet path. -/
theorem one_add_h3PreterminalCanonicalL2JetSquareEnergyOnElapsed_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    1
        +
      h3L2JetSquareEnergy
        (fun a : H3JetIndex =>
          h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail a q)
      =
    velocityH3EnergyAt
      u
      (t + (q : ℝ)) := by
  change
    1
        +
      h3L2JetSquareEnergy
        (velocityH3L2JetAt
          u
          (t + (q : ℝ))
          (h3PreterminalTailIntegrableOnElapsed
            hEnd hTail q)
          (h3PreterminalTailMeasurableOnElapsed
            hNS ht hEnd hTail q))
      =
    velocityH3EnergyAt
      u
      (t + (q : ℝ))

  exact
    one_add_h3L2JetSquareEnergy_velocityH3L2JetAt_eq
      (h3PreterminalTailIntegrableOnElapsed
        hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)

/-- Strong physical H³ `L²`-jet continuity implies scalar physical H³-energy
continuity on the same elapsed interval. -/
theorem h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_l2Jet
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL2 :
      H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hSq :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3L2JetSquareEnergy
            (fun a : H3JetIndex =>
              h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail a q)) :=
    continuous_h3PreterminalCanonicalL2JetSquareEnergyOnElapsed
      hNS ht hEnd hTail hL2

  have hNormalized :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          1
            +
          h3L2JetSquareEnergy
            (fun a : H3JetIndex =>
              h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail a q)) :=
    continuous_const.add hSq

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        velocityH3EnergyAt
          u
          (t + (q : ℝ)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        1
          +
        h3L2JetSquareEnergy
          (fun a : H3JetIndex =>
            h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q)) := by
    funext q
    exact
      (one_add_h3PreterminalCanonicalL2JetSquareEnergyOnElapsed_eq
        hNS ht hEnd hTail q).symm

  unfold H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed

  rw [hEq]

  exact hNormalized

/-- Consequently, strong physical H³ `L²`-jet continuity also supplies the
spectral square-energy continuity consumed by the pressure-free weak+norm
argument. -/
theorem h3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed_of_l2Jet
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL2 :
      H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed_of_physicalEnergy
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_l2Jet
        hNS ht hEnd hTail hL2)

end

end Euclidean
end Bridge
end PrimeTensor
