import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.HarmonicRate

/-!
# Simplified and affine-harmonic Landau terminal rate

The Riccati coefficient and current Landau coefficient use the same spectral
constant

    C₁ = h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient.

Since

    K = 4422 (C₁ + 1),

the harmonic coefficient introduced previously simplifies exactly to

    L_L = 2 C₁ / (C₁ + 1).

Moreover, the canonical Landau coefficient is

    c_L(t) = 4422 (1 + C₁ sqrt(E(t))).

The Riccati lower bound therefore yields the stronger affine-harmonic profile

    4422 + L_L / (T - t) ≤ c_L(t)

at every strict H³ energy-class time on a hypothetical nonextension branch.

The corresponding arbitrarily-late strict violation is a continuation
criterion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Simplification of the harmonic coefficient -/

/--
The factor `4422` cancels exactly between the Landau and Riccati coefficients.
-/
theorem h3CanonicalLandauHarmonicCoefficient_eq_two_mul_coefficient_div_one_add :
    h3CanonicalLandauHarmonicCoefficient
      =
    (
      2
        *
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
    )
      /
    (
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        +
      1
    ) := by

  let C : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  have hCPos :
      0 < C := by

    dsimp only [C]

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos

  have hCOneNe :
      C + 1 ≠ 0 := by
    linarith

  unfold
    h3CanonicalLandauHarmonicCoefficient
    h3PathSqrtEnergyRiccatiCoefficient

  dsimp only [C] at hCOneNe ⊢

  field_simp [hCOneNe]

/-! ## Affine-harmonic lower rate -/

/--
Under hypothetical nonextension, the current canonical Landau coefficient is
bounded below by its constant `4422` baseline plus the positive harmonic
terminal profile.
-/
theorem canonicalLandauTransportCoefficient_affine_harmonic_lower_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    4422
        +
      h3CanonicalLandauHarmonicCoefficient
        /
      (T - t)
      ≤
    h3PathCanonicalLandauTransportCoefficient u t := by

  let C : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  let K : ℝ :=
    h3PathSqrtEnergyRiccatiCoefficient

  let d : ℝ :=
    T - t

  let s : ℝ :=
    Real.sqrt (velocityH3EnergyAt u t)

  have hCPos :
      0 < C := by

    dsimp only [C]

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos

  have hCNonneg :
      0 ≤ C :=
    le_of_lt hCPos

  have hKPos :
      0 < K := by

    dsimp only [K]

    exact
      h3PathSqrtEnergyRiccatiCoefficient_pos

  have hKNe :
      K ≠ 0 :=
    ne_of_gt hKPos

  have hdPos :
      0 < d := by

    dsimp only [d]

    linarith [ht.2]

  have hRiccati :
      2 ≤ K * d * s := by

    dsimp only [K, d, s]

    exact
      two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        ht

  have hScaleNonneg :
      0 ≤ (4422 * C) / K := by

    exact
      div_nonneg
        (
          mul_nonneg
            (by norm_num)
            hCNonneg
        )
        (le_of_lt hKPos)

  have hScaled :=
    mul_le_mul_of_nonneg_left
      hRiccati
      hScaleNonneg

  have hCore :
      h3CanonicalLandauHarmonicCoefficient
        ≤
      4422 * C * s * d := by

    calc
      h3CanonicalLandauHarmonicCoefficient
          =
        ((4422 * C) / K) * 2 := by

          unfold h3CanonicalLandauHarmonicCoefficient

          dsimp only [C, K]

          field_simp [hKNe]

      _ ≤
        ((4422 * C) / K) * (K * d * s) :=
        hScaled

      _ =
        4422 * C * s * d := by

        field_simp [hKNe]

  have hHarmonicCore :
      h3CanonicalLandauHarmonicCoefficient / d
        ≤
      4422 * C * s := by

    apply
      (div_le_iff₀ hdPos).2

    simpa [mul_assoc] using
      hCore

  dsimp only [d] at hHarmonicCore

  unfold h3PathCanonicalLandauTransportCoefficient

  dsimp only [C, s] at hHarmonicCore ⊢

  nlinarith

/--
Equivalent explicit form using the simplified harmonic coefficient.
-/
theorem canonicalLandauTransportCoefficient_affine_reduced_harmonic_lower_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    4422
        +
      (
        (
          2
            *
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        )
          /
        (
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
            +
          1
        )
      )
        /
      (T - t)
      ≤
    h3PathCanonicalLandauTransportCoefficient u t := by

  rw [
    ← h3CanonicalLandauHarmonicCoefficient_eq_two_mul_coefficient_div_one_add
  ]

  exact
    canonicalLandauTransportCoefficient_affine_harmonic_lower_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ht

/-! ## Tail and neutral forms -/

/--
The affine-harmonic lower profile holds throughout the entire strict
energy-class tail under hypothetical nonextension.
-/
theorem canonicalLandauTransportCoefficient_affine_harmonic_lower_on_tail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ t : ℝ,
      t ∈ Set.Ioo a T →
      4422
          +
        h3CanonicalLandauHarmonicCoefficient
          /
        (T - t)
        ≤
      h3PathCanonicalLandauTransportCoefficient u t := by

  intro t ht

  exact
    canonicalLandauTransportCoefficient_affine_harmonic_lower_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ht

/--
Neutral affine-harmonic Landau alternative.
-/
theorem smoothContinuationExtension_or_canonicalLandauCoefficient_affine_harmonic_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
        4422
            +
          h3CanonicalLandauHarmonicCoefficient
            /
          (T - t)
          ≤
        h3PathCanonicalLandauTransportCoefficient u t
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          canonicalLandauTransportCoefficient_affine_harmonic_lower_on_tail_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

/-! ## Continuation threshold -/

/--
If the canonical Landau coefficient drops below the forced affine-harmonic
profile arbitrarily late, smooth continuation follows.
-/
theorem exists_smoothContinuationExtension_of_canonicalLandauCoefficient_affine_harmonic_subcritical_arbitrarilyLate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSubcritical :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          h3PathCanonicalLandauTransportCoefficient u t
            <
          4422
            +
          h3CanonicalLandauHarmonicCoefficient
            /
          (T - t)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  by_contra hNoExtension

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  obtain
    ⟨t, ht, hBelow⟩ :=
    hSubcritical
      b
      hb

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 ht.1,
      ht.2
    ⟩

  have hAbove :=
    canonicalLandauTransportCoefficient_affine_harmonic_lower_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      htClass

  exact
    (not_lt_of_ge hAbove)
      hBelow

end

end Euclidean
end Bridge
end PrimeTensor
