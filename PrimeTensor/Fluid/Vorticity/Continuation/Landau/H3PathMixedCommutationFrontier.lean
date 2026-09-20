import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathEnergyDynamicsFrontier
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.EnergyClassTemporalRHS

/-!
# Reduce H³-path scalar differentiability to pure mixed time--space commutation

The earlier derivative frontier packaged the order-two and order-three
time derivatives in PDE form:

    d/dt (D²u) = momentumRHS2,
    d/dt (D³u) = momentumRHS3.

On a `PreterminalH3EnergyClass`, the right-hand sides are no longer part of
the genuine analytic problem.  `EnergyClassTemporalRHS` already proves

    D²(∂ₜu) = momentumRHS2,
    D³(∂ₜu) = momentumRHS3

throughout the strict energy-class tail.

Therefore the remaining higher mixed-time issue is exactly the commutation

    d/dt (D²u) = D²(∂ₜu),
    d/dt (D³u) = D³(∂ₜu).

This file makes that reduction explicit.

Together with the already-isolated locally uniform integrable derivative
majorants, pure mixed commutation is sufficient to produce the canonical
scalar H³ differentiability interface used by
`H3PathEnergyDynamicsFrontier`.

No pressure choice and no momentum-RHS derivative value remains in the new
commutation frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/-! ## Pure mixed commutation frontier -/

/--
The genuine higher mixed time--space regularity carried by an H³ energy class.

This is strictly the commutation statement.  It contains no pressure witness
and no PDE-form derivative coefficient.
-/
def EnergyClassProducesH3HigherMixedTimeCommutationOnTail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        H3Order2VelocityMixedTimeDerivativeOnTail u a T
          ∧
        H3Order3VelocityMixedTimeDerivativeOnTail u a T

/-! ## PDE values are automatic from the energy class -/

/--
Pure mixed commutation reconstructs the historical PDE-form higher-time
frontier because the energy class already identifies `D²u_t` and `D³u_t` with
the corresponding momentum RHS fields.
-/
theorem energyClassProducesH3HigherTimeDerivativePDEOnTail_of_mixedCommutation
    (hMixed :
      EnergyClassProducesH3HigherMixedTimeCommutationOnTail) :
    EnergyClassProducesH3HigherTimeDerivativePDEOnTail := by

  intro u a T hClass p hPDE hPressure

  rcases
    hMixed u a T hClass
  with
    ⟨hMixed2, hMixed3⟩

  constructor

  · intro s hs j i k x

    have hsPre :
        s ∈ Set.Ioo (0 : ℝ) T := by
      exact
        ⟨
          lt_trans hClass.terminal_start.1 hs.1,
          hs.2
        ⟩

    have hTemporal :
        spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityTemporalComponent u s j))
          =
        momentumRHS2Component
          (logSpaceTimeVectorField u)
          p s i k j :=
      spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
        hPDE hsPre i k j

    have h :=
      hMixed2 s hs j i k x

    rw [hTemporal] at h

    exact h

  · intro s hs j i k l x

    have hsPre :
        s ∈ Set.Ioo (0 : ℝ) T := by
      exact
        ⟨
          lt_trans hClass.terminal_start.1 hs.1,
          hs.2
        ⟩

    have hTemporal :
        spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityTemporalComponent u s j)))
          =
        momentumRHS3Component
          (logSpaceTimeVectorField u)
          p s i k l j :=
      spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
        hPDE hsPre i k l j

    have h :=
      hMixed3 s hs j i k l x

    rw [hTemporal] at h

    exact h

/--
Conversely, the historical PDE-form frontier implies pure mixed commutation.
Thus the pressure/RHS payload is provably redundant at the energy-class level.
-/
theorem energyClassProducesH3HigherMixedTimeCommutationOnTail_of_pde
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail) :
    EnergyClassProducesH3HigherMixedTimeCommutationOnTail := by

  intro u a T hClass

  rcases hClass.pressure_witness with
    ⟨p, hPDE, hPressure⟩

  rcases
    hTime u a T hClass p hPDE hPressure
  with
    ⟨hTime2, hTime3⟩

  exact
    ⟨
      h3Order2VelocityMixedTimeDerivativeOnTail_of_pde
        hPDE
        hClass.terminal_start.1
        hTime2,
      h3Order3VelocityMixedTimeDerivativeOnTail_of_pde
        hPDE
        hClass.terminal_start.1
        hTime3
    ⟩

/--
The old PDE-form frontier and the new pure-commutation frontier are equivalent
once `PreterminalH3EnergyClass` is present.
-/
theorem energyClassProducesH3HigherTimeDerivativePDEOnTail_iff_mixedCommutation :
    EnergyClassProducesH3HigherTimeDerivativePDEOnTail
      ↔
    EnergyClassProducesH3HigherMixedTimeCommutationOnTail := by

  constructor

  · exact
      energyClassProducesH3HigherMixedTimeCommutationOnTail_of_pde

  · exact
      energyClassProducesH3HigherTimeDerivativePDEOnTail_of_mixedCommutation

/-! ## Scalar H³ differentiability from commutation + majorants -/

/--
Pure higher mixed commutation plus the existing locally uniform integrable
derivative majorants imply differentiability of the canonical scalar H³ energy
at every strict H³-path energy-class time.
-/
theorem h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_mixedCommutation_of_majorants
    (hMixed :
      EnergyClassProducesH3HigherMixedTimeCommutationOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesCanonicalEnergyDifferentiability := by

  have hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail :=
    energyClassProducesH3HigherTimeDerivativePDEOnTail_of_mixedCommutation
      hMixed

  have hOrder :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_pdeTime_of_majorants
      hTime
      hMajorants

  exact
    h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
      hOrder

/-! ## BKM compatibility at the reduced differentiability frontier -/

/--
BKM continuation with the scalar differentiability input discharged from the
two genuinely analytic differentiation-under-integral ingredients:

* pure `D²/D³` time--space commutation;
* locally uniform integrable derivative majorants.

The low-frequency and canonical gradient-growth interfaces remain independent.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_mixedCommutation_of_majorants_of_growth
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hMixed :
      EnergyClassProducesH3HigherMixedTimeCommutationOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_energyDynamics
      hLow
      (h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_mixedCommutation_of_majorants
        hMixed
        hMajorants)
      hGrowth

end

end Euclidean
end Bridge
end PrimeTensor
