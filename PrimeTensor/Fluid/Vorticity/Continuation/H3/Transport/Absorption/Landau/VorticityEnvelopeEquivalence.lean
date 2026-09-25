import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.SqrtEnergyEquivalence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Sqrt.Integrability.Frontier

/-!
# Equivalence of the current Landau and canonical BKM temporal frontiers

Let

    C₁ = h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient.

The canonical H³ vorticity envelope is

    g_V(t) = 2 C₁ sqrt(E(t)),

while the current canonical Landau coefficient is

    c_L(t) = 4422 (1 + C₁ sqrt(E(t))).

Therefore

    c_L(t) = 4422 + 2211 g_V(t).

Since the constant baseline is integrable on every finite interval and
`2211 ≠ 0`, the two functions are integrable on exactly the same finite
intervals.

Together with the previously proved Landau/sqrt-energy equivalence, this gives

    c_L ∈ L¹(I)
      ↔
    g_V ∈ L¹(I)
      ↔
    sqrt(E) ∈ L¹(I).

This is a statement about the canonical BKM envelope, not a lower bound on the
actual vorticity magnitude.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact affine identity -/

/--
The current canonical Landau coefficient is exactly the constant baseline
`4422` plus `2211` times the canonical H³ vorticity envelope.
-/
theorem canonicalLandauTransportCoefficient_eq_baseline_add_2211_mul_canonicalVorticityEnvelope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    h3PathCanonicalLandauTransportCoefficient u
      =
    fun t : ℝ =>
      4422
        +
      2211
        *
      h3PathCanonicalVorticitySqrtEnergyEnvelope u t := by

  funext t

  unfold
    h3PathCanonicalLandauTransportCoefficient
    h3PathCanonicalVorticitySqrtEnergyEnvelope

  ring

/-! ## Canonical vorticity-envelope / sqrt-energy equivalence -/

/--
On every finite open interval, the canonical H³ vorticity envelope is
integrable iff square-root H³ energy is integrable.
-/
theorem integrableOn_canonicalVorticitySqrtEnergyEnvelope_iff_sqrtEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) :
    MeasureTheory.IntegrableOn
        (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
        (Set.Ioo b T)
      ↔
    MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo b T) := by

  let C : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  let A : ℝ :=
    2 * C

  have hCPos :
      0 < C := by

    dsimp only [C]

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos

  have hAPos :
      0 < A := by

    dsimp only [A]

    exact
      mul_pos
        (by norm_num)
        hCPos

  have hANe :
      A ≠ 0 :=
    ne_of_gt hAPos

  constructor

  · intro hEnvelope

    have hRecovered :=
      hEnvelope.const_mul
        A⁻¹

    change
      MeasureTheory.Integrable
        (
          fun t : ℝ =>
            Real.sqrt (velocityH3EnergyAt u t)
        )
        (
          (MeasureTheory.volume : Measure ℝ).restrict
            (Set.Ioo b T)
        )

    dsimp only [
      A,
      C,
      h3PathCanonicalVorticitySqrtEnergyEnvelope
    ] at hANe hRecovered

    simpa only [
      ← mul_assoc,
      inv_mul_cancel₀ hANe,
      one_mul
    ] using
      hRecovered

  · intro hSqrt

    have hScaled :
        MeasureTheory.IntegrableOn
          (
            fun t : ℝ =>
              A
                *
              Real.sqrt (velocityH3EnergyAt u t)
          )
          (Set.Ioo b T) :=
      hSqrt.const_mul
        A

    have hEnvelopeEq :
        h3PathCanonicalVorticitySqrtEnergyEnvelope u
          =
        (
          fun t : ℝ =>
            A
              *
            Real.sqrt (velocityH3EnergyAt u t)
        ) := by

      funext t

      dsimp only [
        A,
        C,
        h3PathCanonicalVorticitySqrtEnergyEnvelope
      ]

      ring

    rw [hEnvelopeEq]

    exact
      hScaled

/-! ## Landau / BKM envelope equivalence -/

/--
On every finite interval, the current canonical Landau coefficient and the
canonical H³ vorticity envelope have exactly the same `L¹` integrability
status.
-/
theorem integrableOn_canonicalLandauTransportCoefficient_iff_canonicalVorticityEnvelope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) :
    MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo b T)
      ↔
    MeasureTheory.IntegrableOn
        (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
        (Set.Ioo b T) := by

  exact
    (
      integrableOn_canonicalLandauTransportCoefficient_iff_sqrtEnergy
        u b T
    ).trans
      (
        integrableOn_canonicalVorticitySqrtEnergyEnvelope_iff_sqrtEnergy
          u b T
      ).symm

/--
The complete current temporal-frontier triangle.
-/
theorem canonicalLandau_canonicalVorticity_sqrtEnergy_integrability_equivalent
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) :
    (
      MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo b T)
      ↔
      MeasureTheory.IntegrableOn
        (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
        (Set.Ioo b T)
    )
      ∧
    (
      MeasureTheory.IntegrableOn
        (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
        (Set.Ioo b T)
      ↔
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo b T)
    ) := by

  exact
    ⟨
      integrableOn_canonicalLandauTransportCoefficient_iff_canonicalVorticityEnvelope
        u b T,
      integrableOn_canonicalVorticitySqrtEnergyEnvelope_iff_sqrtEnergy
        u b T
    ⟩

/-! ## Nonextension consequence -/

/--
Under hypothetical nonextension, the canonical H³ vorticity envelope is
nonintegrable on every H³ energy-class tail.

This concerns the canonical upper envelope only; it does not assert a pointwise
lower bound on the actual vorticity.
-/
theorem not_integrableOn_canonicalVorticitySqrtEnergyEnvelope_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
        (Set.Ioo a T) := by

  intro hEnvelope

  have hSqrt :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T) :=
    (
      integrableOn_canonicalVorticitySqrtEnergyEnvelope_iff_sqrtEnergy
        u a T
    ).1
      hEnvelope

  exact
    (
      not_integrableOn_sqrt_velocityH3EnergyAt_on_energyClassTail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    )
      hSqrt

end

end Euclidean
end Bridge
end PrimeTensor
