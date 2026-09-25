import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.AffineHarmonicRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Integrability

/-!
# Exact temporal equivalence of the canonical Landau coefficient and sqrt-energy

The current canonical Landau coefficient is

    c_L(t)
      =
    4422 * (1 + C₁ * sqrt(E(t)))

with `C₁ > 0`.

On every finite time interval, the constant term is integrable and the
multiplicative coefficient `4422 * C₁` is strictly positive.  Therefore

    c_L ∈ L¹(I)
      ↔
    sqrt(E) ∈ L¹(I).

Thus the present Landau-coefficient integrability frontier is exactly the same
temporal frontier as square-root H³-energy integrability.

Combining this algebraic equivalence with the Riccati terminal obstruction
gives an independent proof that hypothetical nonextension forces the current
canonical Landau coefficient to be nonintegrable on every H³ energy-class
terminal tail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact integrability equivalence -/

/--
On every finite open interval, integrability of the current canonical Landau
coefficient is equivalent to integrability of square-root H³ energy.
-/
theorem integrableOn_canonicalLandauTransportCoefficient_iff_sqrtEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) :
    MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo b T)
      ↔
    MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo b T) := by

  let C : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  let A : ℝ :=
    4422 * C

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

  have hConst :
      MeasureTheory.IntegrableOn
        (fun _ : ℝ => (4422 : ℝ))
        (Set.Ioo b T) := by

    exact
      integrableOn_const
        measure_Ioo_lt_top.ne

  constructor

  · intro hCoefficient

    have hDifference :=
      hCoefficient.sub
        hConst

    have hDifferenceEq :
        (
          h3PathCanonicalLandauTransportCoefficient u
            -
          (fun _ : ℝ => (4422 : ℝ))
        )
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
        h3PathCanonicalLandauTransportCoefficient,
        Pi.sub_apply
      ]

      ring

    have hScaled :
        MeasureTheory.IntegrableOn
          (
            fun t : ℝ =>
              A
                *
              Real.sqrt (velocityH3EnergyAt u t)
          )
          (Set.Ioo b T) := by

      rw [hDifferenceEq] at hDifference

      exact
        hDifference

    have hRecovered :=
      hScaled.const_mul
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

    dsimp only [A] at hANe hRecovered

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
          (Set.Ioo b T) := by

      exact
        hSqrt.const_mul
          A

    have hSum :=
      hConst.add
        hScaled

    have hSumEq :
        (
          (fun _ : ℝ => (4422 : ℝ))
            +
          (
            fun t : ℝ =>
              A
                *
              Real.sqrt (velocityH3EnergyAt u t)
          )
        )
          =
        h3PathCanonicalLandauTransportCoefficient u := by

      funext t

      dsimp only [
        A,
        C,
        h3PathCanonicalLandauTransportCoefficient,
        Pi.add_apply
      ]

      ring

    rw [hSumEq] at hSum

    exact
      hSum

/-! ## Riccati derivation of the Landau frontier -/

/--
The current Landau coefficient obstruction follows directly from the Riccati
square-root-energy obstruction and the exact integrability equivalence.
-/
theorem not_integrableOn_canonicalLandauTransportCoefficient_on_energyClassTail_of_noH3PathExtension_from_riccati
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo a T) := by

  intro hCoefficient

  have hSqrt :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T) :=
    (
      integrableOn_canonicalLandauTransportCoefficient_iff_sqrtEnergy
        u
        a
        T
    ).1
      hCoefficient

  exact
    (
      not_integrableOn_sqrt_velocityH3EnergyAt_on_energyClassTail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    )
      hSqrt

/--
Conversely, on any finite interval the two temporal frontiers fail together.
-/
theorem not_integrableOn_canonicalLandauTransportCoefficient_iff_not_integrableOn_sqrtEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) :
    (
      ¬ MeasureTheory.IntegrableOn
          (h3PathCanonicalLandauTransportCoefficient u)
          (Set.Ioo b T)
    )
      ↔
    (
      ¬ MeasureTheory.IntegrableOn
          (fun t : ℝ =>
            Real.sqrt (velocityH3EnergyAt u t))
          (Set.Ioo b T)
    ) := by

  exact
    not_congr
      (
        integrableOn_canonicalLandauTransportCoefficient_iff_sqrtEnergy
          u
          b
          T
      )

/-! ## Continuation reformulation -/

/--
On an H³ energy-class tail, the existing Landau coefficient continuation
criterion is exactly a square-root-energy integrability criterion.
-/
theorem exists_smoothContinuationExtension_of_integrableOn_sqrtEnergy_on_energyClassTail_via_LandauCoefficient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSqrt :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have hCoefficient :
      MeasureTheory.IntegrableOn
        (h3PathCanonicalLandauTransportCoefficient u)
        (Set.Ioo a T) :=
    (
      integrableOn_canonicalLandauTransportCoefficient_iff_sqrtEnergy
        u
        a
        T
    ).2
      hSqrt

  exact
    h3PathExtension_of_integrableCanonicalLandauTransportCoefficientOnTail
      hH3
      hClass
      hCoefficient

end

end Euclidean
end Bridge
end PrimeTensor
