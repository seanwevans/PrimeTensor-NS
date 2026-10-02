import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Criterion
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.State

/-!
# Canonical third-radial forcing state for the terminal cubic mass

The remaining scalar obstruction is

    Σ_j ∫ q(ξ)^3 |F_j(U(t),U(t))(ξ)|² dξ.

Since

    q(ξ)^3 = (2π)^6 |ξ|^6,

this is exactly a fixed positive constant times the squared Fourier `L²` norm
of the order-three radial forcing state.

This file constructs that physical third-radial forcing state directly from the
terminal spectral state.  No selected restart choice enters the definition.

The resulting exact identity is

    fullForcingCubicMass(t)
      =
    (2π)^6 Σ_j ‖F³_j(t)‖².

This is the quotient-safe Hilbert interface needed for the next temporal
continuity step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1600000

/-! ## Third-radial forcing is genuinely Fourier L² -/

/--
At every strict physical time, each nonlinear forcing coordinate has an
order-three radial Fourier `L²` representative.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdRadial_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          U U j ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      U U j

  have hN2 :
      MemLp
        N
        2
        (volume : Measure H3FourierPoint3) := by

    dsimp only [N]

    exact
      h3RawFinLerayOuterProductDivergence_memLp2
        U U j

  have hCubic :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 3
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    have hCubicRaw :=
      integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j

    unfold
      h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
      at hCubicRaw

    dsimp only [N, U, htAbs] at hCubicRaw ⊢

    exact hCubicRaw

  let c : ℝ :=
    (2 * Real.pi) ^ 6

  have hc :
      0 < c := by
    dsimp only [c]
    positivity

  have hRadial :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 6
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    have hScaled :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            c⁻¹
              *
            (
              h3FourierGradientSquare ξ ^ 3
                *
              ‖N ξ‖ ^ 2
            ))
          (volume : Measure H3FourierPoint3) :=
      hCubic.const_mul c⁻¹

    refine
      hScaled.congr ?_

    filter_upwards with ξ

    rw [
      h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six
    ]

    dsimp only [c]

    have hc0 :
        (2 * Real.pi) ^ 6 ≠ 0 := by
      positivity

    field_simp [hc0]

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ)
            *
          N ξ)
        (volume : Measure H3FourierPoint3) := by

    exact
      (
        Complex.continuous_ofReal.comp
          (continuous_norm.pow 3)
      ).aestronglyMeasurable.mul
        hN2.1

  rw [
    memLp_two_iff_integrable_sq_norm
      hMeas
  ]

  refine
    hRadial.congr ?_

  filter_upwards with ξ

  have hr0 :
      0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (pow_nonneg hr0 3),
    mul_pow
  ]

  ring

/-! ## Canonical quotient-safe physical state -/

/--
The canonical physical third-radial nonlinear forcing state at a strict
terminal time.
-/
noncomputable def h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  (
    h3TerminalPhysicalTopDissipationForcingThirdRadial_memLp2
      hH3 hClass ht j
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 3 : ℝ) : ℂ)
        *
      h3RawFinLerayOuterProductDivergence
        U U j ξ)

/--
The canonical third-radial forcing state has the expected physical raw Fourier
representative almost everywhere.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ((
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 3 : ℝ) : ℂ)
        *
      h3RawFinLerayOuterProductDivergence
        U U j ξ) := by

  dsimp only

  unfold
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At

  exact
    MemLp.coeFn_toLp
      (
        h3TerminalPhysicalTopDissipationForcingThirdRadial_memLp2
          hH3 hClass ht j
      )

/--
Exact norm-square formula for one physical third-radial forcing coordinate.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (
      ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
        hH3 hClass ht j‖ : ℝ
    ) ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖ξ‖ ^ 6
        *
      ‖h3RawFinLerayOuterProductDivergence
          U U j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  rw [
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq
  ]

  apply
    integral_congr_ae

  filter_upwards [
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At_ae
      hH3 hClass ht j
  ] with ξ hξ

  rw [hξ]

  have hr0 :
      0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (pow_nonneg hr0 3),
    mul_pow
  ]

  ring

/-! ## Cubic forcing mass is exactly a Hilbert norm-square mass -/

/--
One coordinate of the cubic forcing mass is exactly `(2π)^6` times the squared
norm of the canonical physical third-radial forcing state.
-/
theorem integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      ∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j ξ
        ∂(volume : Measure H3FourierPoint3)
    )
      =
    (2 * Real.pi) ^ 6
      *
    (
      ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
        hH3 hClass ht j‖ : ℝ
    ) ^ 2 := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  rw [
    norm_sq_h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
      hH3 hClass ht j
  ]

  rw [← integral_const_mul]

  apply
    integral_congr_ae

  filter_upwards with ξ

  unfold
    h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt

  dsimp only [htAbs, U]

  rw [
    h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six
  ]

  ring

/--
The complete cubic forcing mass is exactly `(2π)^6` times the sum of the three
third-radial forcing norm squares.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassAt_eq_sum_norm_sq_thirdRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht
      =
    (2 * Real.pi) ^ 6
      *
    ∑ j : Fin 3,
      (
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
          hH3 hClass ht j‖ : ℝ
      ) ^ 2 := by

  unfold
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt

  calc
    (∑ j : Fin 3,
      ∫ ξ : H3FourierPoint3,
        h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j ξ
        ∂(volume : Measure H3FourierPoint3))
        =
      ∑ j : Fin 3,
        (
          (2 * Real.pi) ^ 6
            *
          (
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
              hH3 hClass ht j‖ : ℝ
          ) ^ 2
        ) := by

      apply
        Finset.sum_congr rfl

      intro j hj

      exact
        integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_norm_sq
          hH3 hClass ht j

    _ =
      (2 * Real.pi) ^ 6
        *
      ∑ j : Fin 3,
        (
          ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
            hH3 hClass ht j‖ : ℝ
        ) ^ 2 := by

      rw [Finset.mul_sum]

end

end Euclidean
end Bridge
end PrimeTensor
