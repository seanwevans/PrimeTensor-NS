import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FiveQuarterForcingMass

/-!
# Envelope form of the quantitative five-quarter forcing bound

`FiveQuarterForcingMass` expresses the full projected nonlinear forcing mass as
a finite sum of coordinatewise unweighted and `9/4` state masses.

This file collapses that expression behind four scalar state envelopes.

If

    m₀(U_k) ≤ U₀,   m₉(U_k) ≤ U₉,
    m₀(V_j) ≤ V₀,   m₉(V_j) ≤ V₉

for every coordinate, then every projected forcing coordinate satisfies

    m₅(P div(U⊗V)_i)
      ≤
    2 ∑ₖ ∑ⱼ
      (2π) C₉ (U₉ V₀ + U₀ V₉).

For the diagonal Navier--Stokes forcing `U = V`, this becomes one reusable
constant depending only on a common unweighted envelope `M₀` and a common
`9/4` envelope `M₉`.

This is the quantitative interface needed by the positive-time bootstrap:
above this file, the convolution, derivative, divergence, and Leray algebra no
longer need to be reopened.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFiveQuarterForcingEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The unweighted raw Fourier mass is nonnegative. -/
theorem h3SpectralScalarRawFourierL1Mass_nonneg
    (F : H3SpectralScalarState) :
    0 ≤ h3SpectralScalarRawFourierL1Mass F := by
  unfold h3SpectralScalarRawFourierL1Mass
  exact integral_nonneg fun ξ => norm_nonneg _

/-- The `9/4` weighted raw Fourier mass is nonnegative. -/
theorem h3SpectralScalarRawFourierNineQuarterMass_nonneg
    (F : H3SpectralScalarState) :
    0 ≤ h3SpectralScalarRawFourierNineQuarterMass F := by
  unfold h3SpectralScalarRawFourierNineQuarterMass
  exact integral_nonneg fun ξ => by
    exact
      mul_nonneg
        (by
          unfold h3FourierNineQuarterWeight
          exact Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

/-- Bilinear state-envelope coefficient for one projected `5/4` forcing
coordinate. -/
noncomputable def h3FiveQuarterForcingBilinearEnvelope
    (U0 U9 V0 V9 : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (h3FourierNineQuarterSplitCoefficient *
            (U9 * V0 + U0 * V9))

/-- Diagonal state-envelope coefficient for `U = V`. -/
noncomputable def h3FiveQuarterForcingDiagonalEnvelope
    (M0 M9 : ℝ) : ℝ :=
  h3FiveQuarterForcingBilinearEnvelope M0 M9 M0 M9

theorem h3FiveQuarterForcingBilinearEnvelope_nonneg
    {U0 U9 V0 V9 : ℝ}
    (hU0 : 0 ≤ U0)
    (hU9 : 0 ≤ U9)
    (hV0 : 0 ≤ V0)
    (hV9 : 0 ≤ V9) :
    0 ≤ h3FiveQuarterForcingBilinearEnvelope U0 U9 V0 V9 := by
  unfold h3FiveQuarterForcingBilinearEnvelope

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  have hSplit : 0 ≤ h3FourierNineQuarterSplitCoefficient := by
    unfold h3FourierNineQuarterSplitCoefficient
    exact Real.rpow_nonneg (by norm_num) _

  exact
    mul_nonneg
      (by norm_num)
      (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => by
          exact
            mul_nonneg
              hTwoPi
              (mul_nonneg
                hSplit
                (add_nonneg
                  (mul_nonneg hU9 hV0)
                  (mul_nonneg hU0 hV9))))

theorem h3FiveQuarterForcingDiagonalEnvelope_nonneg
    {M0 M9 : ℝ}
    (hM0 : 0 ≤ M0)
    (hM9 : 0 ≤ M9) :
    0 ≤ h3FiveQuarterForcingDiagonalEnvelope M0 M9 := by
  unfold h3FiveQuarterForcingDiagonalEnvelope
  exact
    h3FiveQuarterForcingBilinearEnvelope_nonneg
      hM0 hM9 hM0 hM9

/-- Coordinatewise state envelopes collapse the full quantitative forcing
estimate to one scalar bilinear coefficient. -/
theorem h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_bilinearEnvelope
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    {U0 U9 V0 V9 : ℝ}
    (hU0nonneg : 0 ≤ U0)
    (hU9nonneg : 0 ≤ U9)
    (_hV0nonneg : 0 ≤ V0)
    (_hV9nonneg : 0 ≤ V9)
    (hU0 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass (U k) ≤ U0)
    (hU9 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass (U k) ≤ U9)
    (hV0 :
      ∀ j : Fin 3,
        h3SpectralScalarRawFourierL1Mass (V j) ≤ V0)
    (hV9 :
      ∀ j : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass (V j) ≤ V9)
    (hUq :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hVq :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass U V i
      ≤
    h3FiveQuarterForcingBilinearEnvelope U0 U9 V0 V9 := by
  have hBase :=
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_stateMasses
      U V i hUq hVq

  have hSplit0 :
      0 ≤ h3FourierNineQuarterSplitCoefficient := by
    unfold h3FourierNineQuarterSplitCoefficient
    exact Real.rpow_nonneg (by norm_num) _

  have hTwoPi0 : 0 ≤ 2 * Real.pi := by
    positivity

  have hTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (h3SpectralScalarRawFourierNineQuarterMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierNineQuarterMass (V j)))
          ≤
        (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (U9 * V0 + U0 * V9)) := by
    intro k j

    have hU0m :=
      h3SpectralScalarRawFourierL1Mass_nonneg (U k)
    have hU9m :=
      h3SpectralScalarRawFourierNineQuarterMass_nonneg (U k)
    have hV0m :=
      h3SpectralScalarRawFourierL1Mass_nonneg (V j)
    have hV9m :=
      h3SpectralScalarRawFourierNineQuarterMass_nonneg (V j)

    have hLeft :
        h3SpectralScalarRawFourierNineQuarterMass (U k) *
            h3SpectralScalarRawFourierL1Mass (V j)
          ≤
        U9 * V0 :=
      mul_le_mul
        (hU9 k)
        (hV0 j)
        hV0m
        hU9nonneg

    have hRight :
        h3SpectralScalarRawFourierL1Mass (U k) *
            h3SpectralScalarRawFourierNineQuarterMass (V j)
          ≤
        U0 * V9 :=
      mul_le_mul
        (hU0 k)
        (hV9 j)
        hV9m
        hU0nonneg

    have hSum :
        h3SpectralScalarRawFourierNineQuarterMass (U k) *
              h3SpectralScalarRawFourierL1Mass (V j) +
            h3SpectralScalarRawFourierL1Mass (U k) *
              h3SpectralScalarRawFourierNineQuarterMass (V j)
          ≤
        U9 * V0 + U0 * V9 :=
      add_le_add hLeft hRight

    have hSplit :=
      mul_le_mul_of_nonneg_left hSum hSplit0

    exact
      mul_le_mul_of_nonneg_left hSplit hTwoPi0

  have hSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (h3SpectralScalarRawFourierNineQuarterMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierNineQuarterMass (V j))))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (U9 * V0 + U0 * V9)) := by
    exact
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hTerm k j

  have hTwo0 : 0 ≤ (2 : ℝ) := by
    norm_num

  unfold h3FiveQuarterForcingBilinearEnvelope

  calc
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass U V i
        ≤
      2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierNineQuarterSplitCoefficient *
                (h3SpectralScalarRawFourierNineQuarterMass (U k) *
                    h3SpectralScalarRawFourierL1Mass (V j) +
                  h3SpectralScalarRawFourierL1Mass (U k) *
                    h3SpectralScalarRawFourierNineQuarterMass (V j))) :=
      hBase
    _ ≤
      2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierNineQuarterSplitCoefficient *
                (U9 * V0 + U0 * V9)) :=
      mul_le_mul_of_nonneg_left hSum hTwo0

/-- Diagonal specialization for the Navier--Stokes quadratic forcing. -/
theorem h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_diagonalEnvelope
    (W : H3SpectralFinVectorState)
    (i : Fin 3)
    {M0 M9 : ℝ}
    (hM0nonneg : 0 ≤ M0)
    (hM9nonneg : 0 ≤ M9)
    (hW0 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass (W k) ≤ M0)
    (hW9 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass (W k) ≤ M9)
    (hWq :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (W k) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass W W i
      ≤
    h3FiveQuarterForcingDiagonalEnvelope M0 M9 := by
  unfold h3FiveQuarterForcingDiagonalEnvelope

  exact
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_bilinearEnvelope
      W W i
      hM0nonneg hM9nonneg
      hM0nonneg hM9nonneg
      hW0 hW9 hW0 hW9
      hWq hWq

end
end Euclidean
end Bridge
end PrimeTensor
