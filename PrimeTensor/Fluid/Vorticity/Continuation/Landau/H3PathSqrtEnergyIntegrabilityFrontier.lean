import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathVorticityEnergyEnvelope

/-!
# Reduce the H³-path vorticity frontier to scalar square-root energy integrability

The spatial part of the BKM quantity is now closed:

    |ω_m(t,x)| ≤ 2 C₁ sqrt(E_H3(t)).

Therefore the exact remaining sufficient temporal condition is simply

    sqrt(E_H3) ∈ L¹(0,T).

Multiplication by the fixed evaluation constant preserves integrability, so the
canonical H³ vorticity envelope is integrable whenever the square-root energy
profile is.  The already-closed H³-path BKM criterion then gives continuation.

The contrapositive gives a useful blowup alternative at the current interface:
a non-extendible preterminal H³ path must have nonintegrable square-root H³
energy on `(0,T)`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set

noncomputable section

/-- Scalar temporal frontier left after closing the spatial vorticity envelope. -/
def H3PathSqrtEnergyIntegrableOnPreterminal : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo (0 : ℝ) T)

/-- Integrability of the square-root H³ energy makes the canonical vorticity
envelope integrable. -/
theorem h3PathCanonicalVorticitySqrtEnergyEnvelope_integrableOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hSqrt :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo (0 : ℝ) T)) :
    MeasureTheory.IntegrableOn
      (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
      (Set.Ioo (0 : ℝ) T) := by

  have hScaled :=
    hSqrt.const_mul
      (2 *
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient)

  change
    MeasureTheory.Integrable
      (fun t : ℝ =>
        2 *
          (
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
              *
            Real.sqrt (velocityH3EnergyAt u t)
          ))
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) T))

  simpa only [mul_assoc] using hScaled

/-- The scalar square-root-energy temporal condition manufactures the exact
componentwise vorticity `L¹_t L∞_x` control used by the continuation theorem. -/
theorem vorticityL1LinfControl_of_h3Path_sqrtEnergyIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hSqrt :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo (0 : ℝ) T)) :
    VorticityL1LinfControl u T := by

  refine
    ⟨
      h3PathCanonicalVorticitySqrtEnergyEnvelope u,
      h3PathCanonicalVorticitySqrtEnergyEnvelope_integrableOn hSqrt,
      ?_
    ⟩

  intro t ht

  exact
    h3PathCanonicalVorticitySqrtEnergyEnvelope_at
      hH3 ht

/-- The scalar square-root-energy frontier implies the previously isolated
H³-path a-priori vorticity frontier. -/
theorem h3PathPreterminalNavierStokesForcesVorticityL1Linf_of_sqrtEnergyIntegrable
    (hSqrt :
      H3PathSqrtEnergyIntegrableOnPreterminal) :
    H3PathPreterminalNavierStokesForcesVorticityL1Linf := by

  intro u T hH3

  exact
    vorticityL1LinfControl_of_h3Path_sqrtEnergyIntegrable
      hH3
      (hSqrt u T hH3)

/-- Consequently, scalar square-root H³ energy integrability is sufficient for
smooth continuation of every preterminal H³ path. -/
theorem everyH3PathPreterminalNavierStokesSolutionExtends_of_sqrtEnergyIntegrable
    (hSqrt :
      H3PathSqrtEnergyIntegrableOnPreterminal) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by

  exact
    everyH3PathPreterminalNavierStokesSolutionExtends_of_vorticityApriori
      (h3PathPreterminalNavierStokesForcesVorticityL1Linf_of_sqrtEnergyIntegrable
        hSqrt)

/-- Contrapositive at a single path: failure of smooth continuation forces
failure of square-root H³ energy integrability. -/
theorem not_integrableOn_sqrt_velocityH3EnergyAt_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo (0 : ℝ) T) := by

  intro hSqrt

  have hControl :
      VorticityL1LinfControl u T :=
    vorticityL1LinfControl_of_h3Path_sqrtEnergyIntegrable
      hH3 hSqrt

  exact
    hNoExtension
      (h3PathVorticityL1LinfProducesExtension_closed
        u T hH3 hControl)

/-- At proposition level, failure of universal H³-path continuation rules out
the universal square-root-energy integrability statement. -/
theorem not_everyH3PathExtension_implies_not_sqrtEnergyIntegrable
    (hNoGlobal :
      ¬ EveryH3PathPreterminalNavierStokesSolutionExtends) :
    ¬ H3PathSqrtEnergyIntegrableOnPreterminal := by

  intro hSqrt

  exact
    hNoGlobal
      (everyH3PathPreterminalNavierStokesSolutionExtends_of_sqrtEnergyIntegrable
        hSqrt)

end

end Euclidean
end Bridge
end PrimeTensor
