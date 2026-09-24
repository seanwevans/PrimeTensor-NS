import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Sqrt.Integrability.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Pairing.PDE.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Pressure.Cancel.Zero
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Sign.Closure

/-!
# Autonomous square-root H³ energy growth on an admissible path

The previous reduction showed that finite

    ∫ sqrt(E_H3(t)) dt

is sufficient for continuation.  This file asks what the already-closed exact
H³ energy identity gives when the new sharp pointwise gradient estimate

    |∂ᵢ uⱼ(t,x)| ≤ C₁ sqrt(E_H3(t))

is inserted directly.

All analytic inputs to the ordinary differentiated energy inequality are now
closed:

* all four exact energy derivative identities;
* all PDE pairings;
* full pressure cancellation;
* full diffusion nonpositivity.

Therefore every H³ energy-class tail satisfies

    E'(t)
      ≤ 4422 (1 + C₁ sqrt(E(t))) E(t).

Since `E(t) ≥ 1`, this implies the autonomous Riccati-scale estimate

    E'(t)
      ≤ 4422 (C₁ + 1) sqrt(E(t)) E(t).

This is an important boundary theorem rather than a global bound: the
right-hand side has the superlinear `E^(3/2)` scale, so this estimate by itself
does not force `sqrt(E)` to be integrable up to the terminal time.  Any global
closure must retain or recover additional coercive structure beyond simply
discarding the viscous term as nonpositive.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The canonical pointwise first-gradient envelope supplied by the exact
spectral H³ energy identity. -/
noncomputable def h3PathCanonicalSqrtEnergyGradientEnvelope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      *
    Real.sqrt (velocityH3EnergyAt u t)

/-- Every strict time on an admissible H³ energy-class tail satisfies the
canonical square-root-energy velocity-gradient envelope. -/
theorem h3PathCanonicalSqrtEnergyGradientEnvelope_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    VelocityGradientEnvelope
      u
      (h3PathCanonicalSqrtEnergyGradientEnvelope u)
      t := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  intro i j x

  have hBound :=
    norm_loggedVelocityComponent_spatial_d_le_sqrt_h3Energy_of_h3Path
      hH3 htAbs i j x

  change
    abs
      (spatial3.d
        i
        (loggedVelocityComponent u t j)
        x)
      ≤
    h3PathCanonicalSqrtEnergyGradientEnvelope u t

  simpa only [
    h3PathCanonicalSqrtEnergyGradientEnvelope,
    Real.norm_eq_abs
  ] using hBound

/-- The exact closed H³ energy machinery yields an autonomous differentiated
energy inequality with the sharp square-root-energy gradient envelope. -/
theorem h3GradientGrowthInequalityFrom_h3Path_sqrtEnergy_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3GradientGrowthInequalityFrom
      a T
      (h3PathCanonicalSqrtEnergyGradientEnvelope u)
      (velocityH3EnergyAt u)
      4422 := by

  have hSigns :
      H3PathEnergyClassProducesFullScalarSigns :=
    h3PathEnergyClassProducesFullScalarSigns_of_pressureCancellation
      h3PathEnergyClassProducesPressureCancellation_closed

  apply
    h3GradientGrowthInequalityFrom_h3Path_exactEnergy
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hSigns
      hH3
      hClass

  intro t ht

  exact
    h3PathCanonicalSqrtEnergyGradientEnvelope_at
      hH3 hClass ht

/-- Pointwise form of the autonomous closed energy-growth inequality. -/
theorem deriv_velocityH3EnergyAt_le_sqrtEnergyGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
      ≤
    4422
      *
    (
      1 +
        abs
          (
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
              *
            Real.sqrt (velocityH3EnergyAt u t)
          )
    )
      *
    velocityH3EnergyAt u t := by

  have hGrowth :=
    h3GradientGrowthInequalityFrom_h3Path_sqrtEnergy_closed
      hH3 hClass

  simpa only [
    h3PathCanonicalSqrtEnergyGradientEnvelope
  ] using
    hGrowth t ht

/-- Fixed coefficient in the autonomous Riccati-scale H³ energy inequality. -/
noncomputable def h3PathSqrtEnergyRiccatiCoefficient : ℝ :=
  4422
    *
  (
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      +
    1
  )

/-- The closed energy estimate is at most Riccati scale:
`E' ≤ K sqrt(E) E`. -/
theorem deriv_velocityH3EnergyAt_le_sqrtEnergy_mul_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t
      ≤
    h3PathSqrtEnergyRiccatiCoefficient
      *
    Real.sqrt (velocityH3EnergyAt u t)
      *
    velocityH3EnergyAt u t := by

  let C : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  let E : ℝ :=
    velocityH3EnergyAt u t

  have hRaw :=
    deriv_velocityH3EnergyAt_le_sqrtEnergyGrowth
      hH3 hClass ht

  have hC :
      0 ≤ C := by
    dsimp only [C]
    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  have hEOne :
      1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3EnergyAt u t

  have hENonneg :
      0 ≤ E := by
    linarith

  have hSqrtNonneg :
      0 ≤ Real.sqrt E :=
    Real.sqrt_nonneg E

  have hSqrtOne :
      1 ≤ Real.sqrt E := by
    have h :=
      Real.sqrt_le_sqrt hEOne
    simpa only [Real.sqrt_one] using h

  have hFactor :
      1 + C * Real.sqrt E
        ≤
      (C + 1) * Real.sqrt E := by
    nlinarith

  have hAbs :
      abs
          (
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
              *
            Real.sqrt (velocityH3EnergyAt u t)
          )
        =
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) := by
    exact
      abs_of_nonneg
        (mul_nonneg
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
          (Real.sqrt_nonneg _))

  have hRaw' :
      deriv (velocityH3EnergyAt u) t
        ≤
      4422
        *
      (1 + C * Real.sqrt E)
        *
      E := by
    rw [hAbs] at hRaw
    simpa only [C, E] using hRaw

  calc
    deriv (velocityH3EnergyAt u) t
        ≤
      4422
        *
      (1 + C * Real.sqrt E)
        *
      E :=
      hRaw'

    _ ≤
      4422
        *
      ((C + 1) * Real.sqrt E)
        *
      E := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            hFactor
            (by norm_num))
          hENonneg

    _ =
      h3PathSqrtEnergyRiccatiCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t)
        *
      velocityH3EnergyAt u t := by
      dsimp only [
        h3PathSqrtEnergyRiccatiCoefficient,
        C,
        E
      ]
      ring

/-- The autonomous Riccati coefficient is nonnegative. -/
theorem h3PathSqrtEnergyRiccatiCoefficient_nonneg :
    0 ≤ h3PathSqrtEnergyRiccatiCoefficient := by

  unfold h3PathSqrtEnergyRiccatiCoefficient

  exact
    mul_nonneg
      (by norm_num)
      (by
        have hC :=
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        linarith)

end

end Euclidean
end Bridge
end PrimeTensor
