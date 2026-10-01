import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Angular.Cone.L2
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Good-cone Cauchy control from one physical vorticity endpoint

The angular-cone L² estimate still carried one harmless helper hypothesis:

    almost every Fourier point is nonzero.

For the product Lebesgue measure on `H3FourierPoint3`, this is automatic from
the null-singleton instance.

This file then closes the next structural step.

A pathwise strong H³ endpoint for physical vorticity component `i` supplies
pathwise strong H³ endpoints for both transverse velocity components.  Hence
the two transverse spectral paths are pairwise Cauchy near `T`.

The integrated good-cone estimate transfers that Cauchy control to the
longitudinal component on every fixed angular good cone.  Quantitatively, for
every `κ > 0` and every `r > 0`, sufficiently late strict times `s,t` satisfy

    longitudinalGoodConeScaledSquareDefect < 4 r².

Thus the surviving longitudinal obstruction from the previous reduction
cannot live on any fixed good cone.  If a genuine longitudinal non-Cauchy
defect remains, it must move into the complementary equatorial cone.

This statement still does not identify pathwise endpoint failure with
non-Cauchy behavior: terminal-representation failure remains a separate
logical possibility and will be split explicitly in the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalAngularConeCauchy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The origin is negligible -/

/--
The origin is negligible for the ambient Fourier Lebesgue measure.
-/
theorem h3FourierPoint3_ae_ne_zero :
    ∀ᵐ ξ : H3FourierPoint3 ∂volume,
      ξ ≠ 0 := by

  have hPoint3HyperplaneNull :
      (volume : Measure Point3)
          {x : Point3 | x xAxis = 0}
        =
      0 := by

    change
      Measure.pi
          (fun _ : PrimeTensor.Axis Depth.three =>
            (volume : Measure ℝ))
          {x : Point3 | x xAxis = 0}
        =
      0

    exact
      Measure.pi_hyperplane
        (fun _ : PrimeTensor.Axis Depth.three =>
          (volume : Measure ℝ))
        xAxis
        0

  have hFourierHyperplaneNull :
      (volume : Measure H3FourierPoint3)
          ((WithLp.ofLp :
              H3FourierPoint3 → Point3) ⁻¹'
            {x : Point3 | x xAxis = 0})
        =
      0 := by

    exact
      (
        PiLp.volume_preserving_ofLp
          (PrimeTensor.Axis Depth.three)
      ).preimage_null
        hPoint3HyperplaneNull

  have hFourierZeroNull :
      (volume : Measure H3FourierPoint3)
          ({0} : Set H3FourierPoint3)
        =
      0 := by

    refine
      measure_mono_null
        ?_
        hFourierHyperplaneNull

    intro ξ hξ

    simp only [Set.mem_singleton_iff] at hξ

    subst ξ

    simp

  rw [ae_iff]

  simpa using
    hFourierZeroNull

/-! ## Global transverse H³ square defect -/

/--
The sum of the two transverse bundled H³ norm-square defects.
-/
def h3TerminalTransverseSpectralNormSquareMagnitude
    (i : Fin 3)
    (G H : H3SpectralFinVectorState) : ℝ :=
  if i = 0 then
    ‖G 1 - H 1‖ ^ 2 + ‖G 2 - H 2‖ ^ 2
  else if i = 1 then
    ‖G 0 - H 0‖ ^ 2 + ‖G 2 - H 2‖ ^ 2
  else
    ‖G 0 - H 0‖ ^ 2 + ‖G 1 - H 1‖ ^ 2

/--
The transverse good-cone square defect is bounded by twice the corresponding
global transverse H³ norm-square defect.
-/
theorem transverseGoodConeSquareDefect_le_globalNormSquare
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalTransverseGoodConeSquareDefect
        i κ G H
      ≤
    2 *
      h3TerminalTransverseSpectralNormSquareMagnitude
        i G H := by

  fin_cases i

  · have h1 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                -
              (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
          volume :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 1)
        (H 1)

    have h2 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                -
              (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
          volume :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 2)
        (H 2)

    have hInt :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            2 *
              (
                ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                    -
                  (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                  +
                ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                    -
                  (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
              ))
          volume :=
      (h1.add h2).const_mul 2

    have hNonneg :
        ∀ᵐ ξ : H3FourierPoint3 ∂volume,
          0
            ≤
          2 *
            (
              ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
      filter_upwards with ξ
      positivity

    calc
      h3TerminalTransverseGoodConeSquareDefect
          (0 : Fin 3) κ G H
          =
        ∫ ξ : H3FourierPoint3 in
            h3TerminalLongitudinalAngularGoodCone (0 : Fin 3) κ,
          2 *
            (
              ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
              simp [
                h3TerminalTransverseGoodConeSquareDefect,
                h3TerminalTransverseSpectralSquareMagnitude,
                h3TerminalSpectralDifferenceAt
              ]
      _ ≤
        ∫ ξ : H3FourierPoint3,
          2 *
            (
              ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
              exact
                integral_mono_measure
                  Measure.restrict_le_self
                  hNonneg
                  hInt
      _ =
        2 *
          (
            ‖G 1 - H 1‖ ^ 2
              +
            ‖G 2 - H 2‖ ^ 2
          ) := by
              rw [integral_const_mul]
              rw [integral_add h1 h2]
              rw [
                ←
                  h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                    (G 1) (H 1)
              ]
              rw [
                ←
                  h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                    (G 2) (H 2)
              ]
      _ =
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (0 : Fin 3) G H := by
              simp [
                h3TerminalTransverseSpectralNormSquareMagnitude
              ]

  · have h0 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                -
              (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
          volume :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 0)
        (H 0)

    have h2 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                -
              (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
          volume :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 2)
        (H 2)

    have hInt :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            2 *
              (
                ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                    -
                  (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                  +
                ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                    -
                  (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
              ))
          volume :=
      (h0.add h2).const_mul 2

    have hNonneg :
        ∀ᵐ ξ : H3FourierPoint3 ∂volume,
          0
            ≤
          2 *
            (
              ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
      filter_upwards with ξ
      positivity

    calc
      h3TerminalTransverseGoodConeSquareDefect
          (1 : Fin 3) κ G H
          =
        ∫ ξ : H3FourierPoint3 in
            h3TerminalLongitudinalAngularGoodCone (1 : Fin 3) κ,
          2 *
            (
              ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
              simp [
                h3TerminalTransverseGoodConeSquareDefect,
                h3TerminalTransverseSpectralSquareMagnitude,
                h3TerminalSpectralDifferenceAt
              ]
      _ ≤
        ∫ ξ : H3FourierPoint3,
          2 *
            (
              ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 2 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 2 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
              exact
                integral_mono_measure
                  Measure.restrict_le_self
                  hNonneg
                  hInt
      _ =
        2 *
          (
            ‖G 0 - H 0‖ ^ 2
              +
            ‖G 2 - H 2‖ ^ 2
          ) := by
              rw [integral_const_mul]
              rw [integral_add h0 h2]
              rw [
                ←
                  h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                    (G 0) (H 0)
              ]
              rw [
                ←
                  h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                    (G 2) (H 2)
              ]
      _ =
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (1 : Fin 3) G H := by
              simp [
                h3TerminalTransverseSpectralNormSquareMagnitude
              ]

  · have h0 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                -
              (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
          volume :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 0)
        (H 0)

    have h1 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                -
              (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
          volume :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 1)
        (H 1)

    have hInt :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            2 *
              (
                ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                    -
                  (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                  +
                ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                    -
                  (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
              ))
          volume :=
      (h0.add h1).const_mul 2

    have hNonneg :
        ∀ᵐ ξ : H3FourierPoint3 ∂volume,
          0
            ≤
          2 *
            (
              ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
      filter_upwards with ξ
      positivity

    calc
      h3TerminalTransverseGoodConeSquareDefect
          (2 : Fin 3) κ G H
          =
        ∫ ξ : H3FourierPoint3 in
            h3TerminalLongitudinalAngularGoodCone (2 : Fin 3) κ,
          2 *
            (
              ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
              simp [
                h3TerminalTransverseGoodConeSquareDefect,
                h3TerminalTransverseSpectralSquareMagnitude,
                h3TerminalSpectralDifferenceAt
              ]
      _ ≤
        ∫ ξ : H3FourierPoint3,
          2 *
            (
              ‖(G 0 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 0 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
                +
              ‖(G 1 : H3FourierPoint3 → ℂ) ξ
                  -
                (H 1 : H3FourierPoint3 → ℂ) ξ‖ ^ 2
            ) := by
              exact
                integral_mono_measure
                  Measure.restrict_le_self
                  hNonneg
                  hInt
      _ =
        2 *
          (
            ‖G 0 - H 0‖ ^ 2
              +
            ‖G 1 - H 1‖ ^ 2
          ) := by
              rw [integral_const_mul]
              rw [integral_add h0 h1]
              rw [
                ←
                  h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                    (G 0) (H 0)
              ]
              rw [
                ←
                  h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                    (G 1) (H 1)
              ]
      _ =
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (2 : Fin 3) G H := by
              simp [
                h3TerminalTransverseSpectralNormSquareMagnitude
              ]

/-! ## Pairwise Cauchy control from a path endpoint -/

/--
A pathwise strong H³ endpoint for one velocity component makes that strict-time
spectral component pairwise Cauchy near `T`.
-/
theorem velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {j : Fin 3}
    (hEndpoint :
      H3TerminalVelocityComponentStrongH3EndpointPath
        hH3 j) :
    ∀ r : ℝ,
      0 < r →
      ∃ η : ℝ,
        0 < η
          ∧
        ∀
          (s : ℝ)
          (hs : s ∈ Set.Ioo (0 : ℝ) T)
          (t : ℝ)
          (ht : t ∈ Set.Ioo (0 : ℝ) T),
          dist s T < η →
          dist t T < η →
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                    hH3 j s hs
                  -
                h3TerminalVelocityComponentSpectralStateAt
                    hH3 j t ht
              )
              < r := by

  intro r hr

  obtain
    ⟨
      Ginf,
      _hTerminalRep,
      hModulus
    ⟩ :=
    hEndpoint

  have hHalf :
      0 < r / 2 := by
    linarith

  obtain
    ⟨
      η,
      hη,
      hNear
    ⟩ :=
    hModulus
      (r / 2)
      hHalf

  refine
    ⟨
      η,
      hη,
      ?_
    ⟩

  intro s hs t ht hsT htT

  have hS :=
    hNear
      s hs hsT

  have hT :=
    hNear
      t ht htT

  calc
    norm
        (
          h3TerminalVelocityComponentSpectralStateAt
              hH3 j s hs
            -
          h3TerminalVelocityComponentSpectralStateAt
              hH3 j t ht
        )
        =
      norm
        (
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 j s hs
              -
            Ginf
          )
            +
          (
            Ginf
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 j t ht
          )
        ) := by
          congr 1
          abel
    _ ≤
      norm
        (
          h3TerminalVelocityComponentSpectralStateAt
              hH3 j s hs
            -
          Ginf
        )
        +
      norm
        (
          Ginf
            -
          h3TerminalVelocityComponentSpectralStateAt
                hH3 j t ht
        ) :=
          norm_add_le _ _
    _ =
      norm
        (
          h3TerminalVelocityComponentSpectralStateAt
              hH3 j s hs
            -
          Ginf
        )
        +
      norm
        (
          h3TerminalVelocityComponentSpectralStateAt
              hH3 j t ht
            -
          Ginf
        ) := by
          congr 1
          exact
            norm_sub_rev
              Ginf
              (h3TerminalVelocityComponentSpectralStateAt
                hH3 j t ht)
    _ <
      r / 2 + r / 2 :=
        add_lt_add
          hS
          hT
    _ =
      r := by
        ring

/-! ## Physical endpoint forces good-cone longitudinal Cauchy control -/

/--
If physical vorticity component `i` has a pathwise strong H³ endpoint, then
for every fixed good-cone aperture `κ > 0` the longitudinal good-cone square
defect becomes arbitrarily small.

The quantitative form `4 * r²` avoids introducing an unnecessary square-root
normalization.
-/
theorem longitudinalGoodConeScaledSquareDefect_lt_four_mul_sq_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {κ r : ℝ}
    (hκ : 0 < κ)
    (hr : 0 < r) :
    ∃ η : ℝ,
      0 < η
        ∧
      ∀
        (s : ℝ)
        (hs : s ∈ Set.Ioo (0 : ℝ) T)
        (t : ℝ)
        (ht : t ∈ Set.Ioo (0 : ℝ) T),
        dist s T < η →
        dist t T < η →
          h3TerminalLongitudinalGoodConeScaledSquareDefect
              i κ
              (h3TerminalVelocitySpectralStateAt hH3 s hs)
              (h3TerminalVelocitySpectralStateAt hH3 t ht)
            <
          4 * r ^ 2 := by

  fin_cases i

  · have hEndpoint1 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (1 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    have hEndpoint2 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (2 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    obtain
      ⟨η1, hη1, hC1⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint1 r hr

    obtain
      ⟨η2, hη2, hC2⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint2 r hr

    refine
      ⟨
        min η1 η2,
        lt_min hη1 hη2,
        ?_
      ⟩

    intro s hs t ht hsT htT

    have hs1 :
        dist s T < η1 :=
      lt_of_lt_of_le
        hsT
        (min_le_left _ _)

    have ht1 :
        dist t T < η1 :=
      lt_of_lt_of_le
        htT
        (min_le_left _ _)

    have hs2 :
        dist s T < η2 :=
      lt_of_lt_of_le
        hsT
        (min_le_right _ _)

    have ht2 :
        dist t T < η2 :=
      lt_of_lt_of_le
        htT
        (min_le_right _ _)

    have hN1 :=
      hC1
        s hs t ht
        hs1 ht1

    have hN2 :=
      hC2
        s hs t ht
        hs2 ht2

    have hN1sq :
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (1 : Fin 3) s hs
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (1 : Fin 3) t ht
          ) ^ 2
          <
        r ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hr.le
      ).2 hN1

    have hN2sq :
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (2 : Fin 3) s hs
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (2 : Fin 3) t ht
          ) ^ 2
          <
        r ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hr.le
      ).2 hN2

    let Gs :=
      h3TerminalVelocitySpectralStateAt
        hH3 s hs

    let Gt :=
      h3TerminalVelocitySpectralStateAt
        hH3 t ht

    have hGlobal :
        h3TerminalTransverseSpectralNormSquareMagnitude
            (0 : Fin 3) Gs Gt
          <
        2 * r ^ 2 := by

      dsimp only [Gs, Gt]

      simp [
        h3TerminalTransverseSpectralNormSquareMagnitude,
        h3TerminalVelocitySpectralStateAt_apply
      ]

      nlinarith

    have hGood :
        h3TerminalLongitudinalGoodConeScaledSquareDefect
            (0 : Fin 3) κ Gs Gt
          ≤
        h3TerminalTransverseGoodConeSquareDefect
            (0 : Fin 3) κ Gs Gt :=
      longitudinalGoodConeScaledSquareDefect_le_transverse
        hκ
        (h3TerminalVelocitySpectralStateAt_divergenceFree hH3 s hs)
        (h3TerminalVelocitySpectralStateAt_divergenceFree hH3 t ht)
        h3FourierPoint3_ae_ne_zero

    have hTrans :
        h3TerminalTransverseGoodConeSquareDefect
            (0 : Fin 3) κ Gs Gt
          ≤
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (0 : Fin 3) Gs Gt :=
      transverseGoodConeSquareDefect_le_globalNormSquare
        (0 : Fin 3) κ Gs Gt

    dsimp only [Gs, Gt] at hGood hTrans ⊢

    calc
      h3TerminalLongitudinalGoodConeScaledSquareDefect
          (0 : Fin 3) κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht)
          ≤
        h3TerminalTransverseGoodConeSquareDefect
          (0 : Fin 3) κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht) :=
            hGood
      _ ≤
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (0 : Fin 3)
            (h3TerminalVelocitySpectralStateAt hH3 s hs)
            (h3TerminalVelocitySpectralStateAt hH3 t ht) :=
              hTrans
      _ <
        4 * r ^ 2 := by
          nlinarith

  · have hEndpoint0 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (0 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    have hEndpoint2 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (2 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    obtain
      ⟨η0, hη0, hC0⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint0 r hr

    obtain
      ⟨η2, hη2, hC2⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint2 r hr

    refine
      ⟨
        min η0 η2,
        lt_min hη0 hη2,
        ?_
      ⟩

    intro s hs t ht hsT htT

    have hs0 :
        dist s T < η0 :=
      lt_of_lt_of_le
        hsT
        (min_le_left _ _)

    have ht0 :
        dist t T < η0 :=
      lt_of_lt_of_le
        htT
        (min_le_left _ _)

    have hs2 :
        dist s T < η2 :=
      lt_of_lt_of_le
        hsT
        (min_le_right _ _)

    have ht2 :
        dist t T < η2 :=
      lt_of_lt_of_le
        htT
        (min_le_right _ _)

    have hN0 :=
      hC0
        s hs t ht
        hs0 ht0

    have hN2 :=
      hC2
        s hs t ht
        hs2 ht2

    have hN0sq :
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (0 : Fin 3) s hs
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (0 : Fin 3) t ht
          ) ^ 2
          <
        r ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hr.le
      ).2 hN0

    have hN2sq :
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (2 : Fin 3) s hs
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (2 : Fin 3) t ht
          ) ^ 2
          <
        r ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hr.le
      ).2 hN2

    let Gs :=
      h3TerminalVelocitySpectralStateAt
        hH3 s hs

    let Gt :=
      h3TerminalVelocitySpectralStateAt
        hH3 t ht

    have hGlobal :
        h3TerminalTransverseSpectralNormSquareMagnitude
            (1 : Fin 3) Gs Gt
          <
        2 * r ^ 2 := by

      dsimp only [Gs, Gt]

      simp [
        h3TerminalTransverseSpectralNormSquareMagnitude,
        h3TerminalVelocitySpectralStateAt_apply
      ]

      nlinarith

    have hGood :
        h3TerminalLongitudinalGoodConeScaledSquareDefect
            (1 : Fin 3) κ Gs Gt
          ≤
        h3TerminalTransverseGoodConeSquareDefect
            (1 : Fin 3) κ Gs Gt :=
      longitudinalGoodConeScaledSquareDefect_le_transverse
        hκ
        (h3TerminalVelocitySpectralStateAt_divergenceFree hH3 s hs)
        (h3TerminalVelocitySpectralStateAt_divergenceFree hH3 t ht)
        h3FourierPoint3_ae_ne_zero

    have hTrans :
        h3TerminalTransverseGoodConeSquareDefect
            (1 : Fin 3) κ Gs Gt
          ≤
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (1 : Fin 3) Gs Gt :=
      transverseGoodConeSquareDefect_le_globalNormSquare
        (1 : Fin 3) κ Gs Gt

    dsimp only [Gs, Gt] at hGood hTrans ⊢

    calc
      h3TerminalLongitudinalGoodConeScaledSquareDefect
          (1 : Fin 3) κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht)
          ≤
        h3TerminalTransverseGoodConeSquareDefect
          (1 : Fin 3) κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht) :=
            hGood
      _ ≤
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (1 : Fin 3)
            (h3TerminalVelocitySpectralStateAt hH3 s hs)
            (h3TerminalVelocitySpectralStateAt hH3 t ht) :=
              hTrans
      _ <
        4 * r ^ 2 := by
          nlinarith

  · have hEndpoint0 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (0 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    have hEndpoint1 :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 (1 : Fin 3) :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (by decide)
        hPhysical

    obtain
      ⟨η0, hη0, hC0⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint0 r hr

    obtain
      ⟨η1, hη1, hC1⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint1 r hr

    refine
      ⟨
        min η0 η1,
        lt_min hη0 hη1,
        ?_
      ⟩

    intro s hs t ht hsT htT

    have hs0 :
        dist s T < η0 :=
      lt_of_lt_of_le
        hsT
        (min_le_left _ _)

    have ht0 :
        dist t T < η0 :=
      lt_of_lt_of_le
        htT
        (min_le_left _ _)

    have hs1 :
        dist s T < η1 :=
      lt_of_lt_of_le
        hsT
        (min_le_right _ _)

    have ht1 :
        dist t T < η1 :=
      lt_of_lt_of_le
        htT
        (min_le_right _ _)

    have hN0 :=
      hC0
        s hs t ht
        hs0 ht0

    have hN1 :=
      hC1
        s hs t ht
        hs1 ht1

    have hN0sq :
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (0 : Fin 3) s hs
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (0 : Fin 3) t ht
          ) ^ 2
          <
        r ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hr.le
      ).2 hN0

    have hN1sq :
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (1 : Fin 3) s hs
              -
            h3TerminalVelocityComponentSpectralStateAt
                hH3 (1 : Fin 3) t ht
          ) ^ 2
          <
        r ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hr.le
      ).2 hN1

    let Gs :=
      h3TerminalVelocitySpectralStateAt
        hH3 s hs

    let Gt :=
      h3TerminalVelocitySpectralStateAt
        hH3 t ht

    have hGlobal :
        h3TerminalTransverseSpectralNormSquareMagnitude
            (2 : Fin 3) Gs Gt
          <
        2 * r ^ 2 := by

      dsimp only [Gs, Gt]

      simp [
        h3TerminalTransverseSpectralNormSquareMagnitude,
        h3TerminalVelocitySpectralStateAt_apply
      ]

      nlinarith

    have hGood :
        h3TerminalLongitudinalGoodConeScaledSquareDefect
            (2 : Fin 3) κ Gs Gt
          ≤
        h3TerminalTransverseGoodConeSquareDefect
            (2 : Fin 3) κ Gs Gt :=
      longitudinalGoodConeScaledSquareDefect_le_transverse
        hκ
        (h3TerminalVelocitySpectralStateAt_divergenceFree hH3 s hs)
        (h3TerminalVelocitySpectralStateAt_divergenceFree hH3 t ht)
        h3FourierPoint3_ae_ne_zero

    have hTrans :
        h3TerminalTransverseGoodConeSquareDefect
            (2 : Fin 3) κ Gs Gt
          ≤
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (2 : Fin 3) Gs Gt :=
      transverseGoodConeSquareDefect_le_globalNormSquare
        (2 : Fin 3) κ Gs Gt

    dsimp only [Gs, Gt] at hGood hTrans ⊢

    calc
      h3TerminalLongitudinalGoodConeScaledSquareDefect
          (2 : Fin 3) κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht)
          ≤
        h3TerminalTransverseGoodConeSquareDefect
          (2 : Fin 3) κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht) :=
            hGood
      _ ≤
        2 *
          h3TerminalTransverseSpectralNormSquareMagnitude
            (2 : Fin 3)
            (h3TerminalVelocitySpectralStateAt hH3 s hs)
            (h3TerminalVelocitySpectralStateAt hH3 t ht) :=
              hTrans
      _ <
        4 * r ^ 2 := by
          nlinarith

end

end Euclidean
end Bridge
end PrimeTensor
