import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialConcentration

/-!
# Transverse-frequency polarization of the shrinking equatorial obstruction

The previous checkpoint extracted, under hypothetical nonextension together
with one surviving physical-vorticity strong-H³ endpoint, two strict terminal
sequences `s_n,t_n -> T` and shrinking angular apertures

    κ_n = 1 / (n + 1) -> 0

such that a fixed positive amount of longitudinal H³ square-defect mass remains
inside

    |d_i(ξ)| < κ_n |D(ξ)|.

Before coupling this concentration to curl, record the exact angular geometry
of that cone without introducing one extra derivative.

For coordinate `i`, let the transverse derivative-symbol square be the sum of
the two coordinate-symbol squares different from `i`.  Since

    sum_j |d_j(ξ)|² = |D(ξ)|²,

we have exactly

    transverse² + |d_i|² = |D|².

On the bad cone,

    |d_i| < κ |D|,

hence

    (1 - κ²) |D|² < transverse².

Thus the shrinking equatorial concentration sequence is automatically
transverse-frequency polarized: as `κ_n -> 0`, frequencies supporting the
surviving longitudinal defect have essentially all of their derivative-symbol
square in the two directions transverse to the surviving vorticity index.

This is still a conditional necessary mechanism under hypothetical
nonextension.  No extra Sobolev regularity and no singular Fourier division
is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialPolarization
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Transverse derivative-symbol square -/

/--
Sum of the squares of the two Fourier derivative-symbol norms transverse to
coordinate `i`.
-/
def h3TerminalTransverseDerivativeSymbolSquareMagnitude
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  if i = 0 then
    ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ‖ ^ 2
      +
    ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ‖ ^ 2
  else if i = 1 then
    ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ‖ ^ 2
      +
    ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ‖ ^ 2
  else
    ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ‖ ^ 2
      +
    ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ‖ ^ 2

/--
Exact Pythagorean split of the radial derivative-symbol square into the
longitudinal coordinate and the two transverse coordinates.
-/
theorem transverseDerivativeSymbolSquareMagnitude_add_longitudinal_eq_gradientSquare
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3TerminalTransverseDerivativeSymbolSquareMagnitude i ξ
        +
      ‖h3FourierDerivativeSymbol i ξ‖ ^ 2
      =
    h3FourierGradientSquare ξ := by

  rw [
    ← sum_norm_h3FourierDerivativeSymbol_sq ξ
  ]

  fin_cases i <;>
    simp [
      h3TerminalTransverseDerivativeSymbolSquareMagnitude,
      Fin.sum_univ_three
    ] <;>
    ring

/--
Equivalent split using the radial gradient magnitude `|D(ξ)|`.
-/
theorem transverseDerivativeSymbolSquareMagnitude_add_longitudinal_eq_gradientMagnitude_sq
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3TerminalTransverseDerivativeSymbolSquareMagnitude i ξ
        +
      ‖h3FourierDerivativeSymbol i ξ‖ ^ 2
      =
    (h3FourierGradientMagnitude ξ) ^ 2 := by

  rw [
    h3FourierGradientMagnitude_sq
  ]

  exact
    transverseDerivativeSymbolSquareMagnitude_add_longitudinal_eq_gradientSquare
      i ξ

/-! ## Bad-cone polarization -/

/--
On the angular bad cone, more than a `1 - κ²` fraction of the radial
derivative-symbol square lies in the two transverse frequency coordinates.
-/
theorem one_sub_sq_mul_gradientMagnitude_sq_lt_transverseDerivativeSymbolSquareMagnitude_of_mem_badCone
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 ≤ κ)
    {ξ : H3FourierPoint3}
    (hBad :
      ξ ∈ h3TerminalLongitudinalAngularBadCone i κ) :
    (1 - κ ^ 2)
        *
      (h3FourierGradientMagnitude ξ) ^ 2
      <
    h3TerminalTransverseDerivativeSymbolSquareMagnitude
      i ξ := by

  change
    ‖h3FourierDerivativeSymbol i ξ‖
      <
    κ * h3FourierGradientMagnitude ξ
    at hBad

  have hRightNonneg :
      0
        ≤
      κ * h3FourierGradientMagnitude ξ :=
    mul_nonneg
      hκ
      (h3FourierGradientMagnitude_nonneg ξ)

  have hSquare :
      ‖h3FourierDerivativeSymbol i ξ‖ ^ 2
        <
      (
        κ * h3FourierGradientMagnitude ξ
      ) ^ 2 :=
    (
      sq_lt_sq₀
        (norm_nonneg _)
        hRightNonneg
    ).2
      hBad

  have hSplit :
      h3TerminalTransverseDerivativeSymbolSquareMagnitude i ξ
          +
        ‖h3FourierDerivativeSymbol i ξ‖ ^ 2
        =
      (h3FourierGradientMagnitude ξ) ^ 2 :=
    transverseDerivativeSymbolSquareMagnitude_add_longitudinal_eq_gradientMagnitude_sq
      i ξ

  nlinarith

/--
The same bad-cone polarization written with the project's existing gradient
square.
-/
theorem one_sub_sq_mul_gradientSquare_lt_transverseDerivativeSymbolSquareMagnitude_of_mem_badCone
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 ≤ κ)
    {ξ : H3FourierPoint3}
    (hBad :
      ξ ∈ h3TerminalLongitudinalAngularBadCone i κ) :
    (1 - κ ^ 2)
        *
      h3FourierGradientSquare ξ
      <
    h3TerminalTransverseDerivativeSymbolSquareMagnitude
      i ξ := by

  rw [
    ← h3FourierGradientMagnitude_sq
  ]

  exact
    one_sub_sq_mul_gradientMagnitude_sq_lt_transverseDerivativeSymbolSquareMagnitude_of_mem_badCone
      hκ
      hBad

/-! ## Polarization on the shrinking concentration sequence -/

/--
The previously extracted shrinking equatorial H³ concentration sequence can be
chosen with the pointwise transverse-frequency polarization attached at every
index.

At index `n`, every frequency in the bad cone of aperture `1/(n+1)` satisfies

    (1 - κ_n²) |D(ξ)|² < transverse_i(ξ)²,

while the same cone carries more than `ε²/2` of longitudinal H³ defect mass.
-/
theorem exists_shrinkingEquatorialCone_longitudinalBadConeSquareDefect_transverseFrequencyPolarization_sequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s t : ℕ → ℝ,
      ∃ hs :
        ∀ n : ℕ,
          s n ∈ Set.Ioo (0 : ℝ) T,
        ∃ ht :
          ∀ n : ℕ,
            t n ∈ Set.Ioo (0 : ℝ) T,
          Tendsto s atTop (𝓝 T)
            ∧
          Tendsto t atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                (1 : ℝ) / ((n : ℝ) + 1)
            )
            atTop
            (𝓝 0)
            ∧
          (
            ∀ n : ℕ,
              dist (s n) T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              dist (t n) T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              ε ^ 2 / 2
                  <
                h3TerminalLongitudinalBadConeSquareDefect
                  i
                  ((1 : ℝ) / ((n : ℝ) + 1))
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (s n)
                    (hs n))
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (t n)
                    (ht n))
                ∧
              (
                ∀ ξ : H3FourierPoint3,
                  ξ
                      ∈
                    h3TerminalLongitudinalAngularBadCone
                      i
                      ((1 : ℝ) / ((n : ℝ) + 1))
                    →
                  (
                    1
                      -
                    (
                      (1 : ℝ) / ((n : ℝ) + 1)
                    ) ^ 2
                  )
                      *
                    h3FourierGradientSquare ξ
                    <
                  h3TerminalTransverseDerivativeSymbolSquareMagnitude
                    i ξ
              )
          ) := by

  obtain
    ⟨
      s,
      t,
      hs,
      ht,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      hData
    ⟩ :=
    exists_shrinkingEquatorialCone_longitudinalBadConeSquareDefect_sequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  refine
    ⟨
      s,
      t,
      hs,
      ht,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      ?_
    ⟩

  intro n

  have hκ :
      0
        ≤
      (1 : ℝ) / ((n : ℝ) + 1) := by
    positivity

  refine
    ⟨
      (hData n).1,
      (hData n).2.1,
      (hData n).2.2,
      ?_
    ⟩

  intro ξ hBad

  exact
    one_sub_sq_mul_gradientSquare_lt_transverseDerivativeSymbolSquareMagnitude_of_mem_badCone
      hκ
      hBad

end

end Euclidean
end Bridge
end PrimeTensor
