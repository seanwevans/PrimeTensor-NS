import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Landau.TerminalFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.LowerBound

/-!
# Harmonic terminal rate for the canonical Landau coefficient

The current canonical Landau coefficient is

    c_L(t)
      =
    4422 * (1 + C₁ * sqrt(E(t))),

where `C₁` is the fixed coordinate-derivative evaluation coefficient.

The previous terminal-frontier theorem showed abstractly that hypothetical
nonextension forces `c_L` to be nonintegrable on every strict terminal tail.

This file makes that obstruction quantitative.

First, the explicit first-moment reciprocal H³ weight is a nonzero continuous
function.  Since volume is positive on nonempty open sets, its packaged `L²`
state is nonzero.  Therefore

    0 < C₁.

Second, hypothetical nonextension already forces the Riccati lower rate

    2 ≤ K (T-t) sqrt(E(t)),

with `K > 0`.  Hence

    L_L / (T-t) ≤ c_L(t),

where

    L_L = (2 * 4422 * C₁) / K > 0.

Thus the present Landau coefficient itself carries a harmonic terminal
singularity on every strict H³ energy-class time of a hypothetical
nonextension branch.

This remains a necessary-condition statement only.  Its positive
contrapositive says that if the canonical Landau coefficient falls strictly
below this forced harmonic threshold arbitrarily late, smooth continuation
must exist.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3LandauHarmonicRate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Strict positivity of the spectral derivative coefficient -/

/--
The explicit first-moment reciprocal H³ `L²` state is nonzero.
-/
theorem h3SobolevFrequencyFirstMomentInvComplexL2_ne_zero :
    h3SobolevFrequencyFirstMomentInvComplexL2 ≠ 0 := by

  intro hZero

  have hRep :=
    h3SobolevFrequencyFirstMomentInvComplexL2_ae

  rw [hZero] at hRep

  have hContinuous :
      Continuous h3SobolevFrequencyFirstMomentInvComplex := by

    unfold h3SobolevFrequencyFirstMomentInvComplex

    exact
      Complex.continuous_ofReal.comp
        continuous_h3SobolevFrequencyFirstMomentInv

  have hAeRaw :
      h3SobolevFrequencyFirstMomentInvComplex
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (0 : H3FourierPoint3 → ℂ) := by

    exact
      hRep.symm.trans
        (
          Lp.coeFn_zero
            ℂ
            2
            (volume : Measure H3FourierPoint3)
        )

  have hEverywhere :
      h3SobolevFrequencyFirstMomentInvComplex
        =
      (0 : H3FourierPoint3 → ℂ) := by

    exact
      (
        hContinuous.ae_eq_iff_eq
          (volume : Measure H3FourierPoint3)
          continuous_zero
      ).1
        hAeRaw

  let i : PrimeTensor.Axis Depth.three :=
    h3AxisOfFin3 (0 : Fin 3)

  let ξ : H3FourierPoint3 :=
    h3FourierAxisDirection i

  have hXiNe :
      ξ ≠ 0 := by

    intro hXi

    have hCoordinate :=
      congrArg
        (fun z : H3FourierPoint3 => z i)
        hXi

    dsimp only [ξ] at hCoordinate

    simpa using
      hCoordinate

  have hXiNormPos :
      (0 : ℝ) < ‖ξ‖ := by

    exact
      norm_pos_iff.mpr
        hXiNe

  have hFirstPos :
      0 < h3SobolevFrequencyFirstMomentInv ξ := by

    unfold
      h3SobolevFrequencyFirstMomentInv
      h3SobolevFrequencyWeightInv

    exact
      mul_pos
        hXiNormPos
        (
          inv_pos.mpr
            (
              h3SobolevFrequencyWeight_pos
                ξ
            )
        )

  have hValueNe :
      h3SobolevFrequencyFirstMomentInvComplex ξ ≠ 0 := by

    unfold h3SobolevFrequencyFirstMomentInvComplex

    exact
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt hFirstPos)

  have hValueZero :
      h3SobolevFrequencyFirstMomentInvComplex ξ = 0 := by

    have hAt :=
      congrFun hEverywhere ξ

    simpa using
      hAt

  exact
    hValueNe
      hValueZero

/--
The first-moment deweighting constant is strictly positive.
-/
theorem h3SobolevFirstMomentDeweightingConstant_pos :
    0 < h3SobolevFirstMomentDeweightingConstant := by

  unfold h3SobolevFirstMomentDeweightingConstant

  exact
    norm_pos_iff.mpr
      h3SobolevFrequencyFirstMomentInvComplexL2_ne_zero

/--
The fixed coordinate-derivative evaluation coefficient used by the H³
spectral-to-physical bridge is strictly positive.
-/
theorem h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos :
    0 <
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient := by

  unfold
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  exact
    mul_pos
      (by positivity)
      h3SobolevFirstMomentDeweightingConstant_pos

/-! ## Harmonic coefficient -/

/--
Fixed positive coefficient in the harmonic lower rate for the current
canonical Landau transport coefficient.
-/
noncomputable def h3CanonicalLandauHarmonicCoefficient : ℝ :=
  (
    2
      *
    4422
      *
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  )
    /
  h3PathSqrtEnergyRiccatiCoefficient

theorem h3CanonicalLandauHarmonicCoefficient_pos :
    0 < h3CanonicalLandauHarmonicCoefficient := by

  unfold h3CanonicalLandauHarmonicCoefficient

  exact
    div_pos
      (
        mul_pos
          (
            mul_pos
              (by norm_num)
              (by norm_num)
          )
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
      )
      h3PathSqrtEnergyRiccatiCoefficient_pos

/-! ## Pointwise harmonic terminal rate -/

/--
At every strict H³ energy-class time, hypothetical nonextension forces the
canonical Landau coefficient above a positive harmonic terminal profile.
-/
theorem canonicalLandauTransportCoefficient_harmonic_lower_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
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

  let cL : ℝ :=
    h3PathCanonicalLandauTransportCoefficient u t

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

  have hsNonneg :
      0 ≤ s := by

    dsimp only [s]

    exact
      Real.sqrt_nonneg _

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

  have hCoefficientDom :
      4422 * C * s
        ≤
      cL := by

    dsimp only [cL, C, s]

    unfold h3PathCanonicalLandauTransportCoefficient

    nlinarith

  have hCoefficientDomScaled :
      4422 * C * s * d
        ≤
      cL * d :=
    mul_le_mul_of_nonneg_right
      hCoefficientDom
      (le_of_lt hdPos)

  apply
    (div_le_iff₀ hdPos).2

  exact
    le_trans
      hCore
      hCoefficientDomScaled

/-! ## Strict-tail and neutral forms -/

/--
Hypothetical nonextension forces the harmonic Landau-coefficient lower bound
on the whole strict energy-class tail.
-/
theorem canonicalLandauTransportCoefficient_harmonic_lower_on_tail_of_noH3PathExtension
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
      h3CanonicalLandauHarmonicCoefficient
          /
        (T - t)
        ≤
      h3PathCanonicalLandauTransportCoefficient u t := by

  intro t ht

  exact
    canonicalLandauTransportCoefficient_harmonic_lower_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ht

/--
Neutral harmonic-rate package for the present Landau closure.

Either smooth continuation exists, or the canonical Landau coefficient obeys
the positive harmonic lower rate at every strict terminal time.
-/
theorem smoothContinuationExtension_or_canonicalLandauCoefficient_harmonic_lower
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
      Or.inl hExtension

  · exact
      Or.inr
        (
          canonicalLandauTransportCoefficient_harmonic_lower_on_tail_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

/-! ## Positive threshold continuation criterion -/

/--
If the current canonical Landau coefficient falls strictly below its forced
harmonic nonextension threshold at arbitrarily late times, then smooth
continuation across `T` exists.
-/
theorem exists_smoothContinuationExtension_of_canonicalLandauCoefficient_harmonic_subcritical_arbitrarilyLate
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
    canonicalLandauTransportCoefficient_harmonic_lower_of_noH3PathExtension
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
