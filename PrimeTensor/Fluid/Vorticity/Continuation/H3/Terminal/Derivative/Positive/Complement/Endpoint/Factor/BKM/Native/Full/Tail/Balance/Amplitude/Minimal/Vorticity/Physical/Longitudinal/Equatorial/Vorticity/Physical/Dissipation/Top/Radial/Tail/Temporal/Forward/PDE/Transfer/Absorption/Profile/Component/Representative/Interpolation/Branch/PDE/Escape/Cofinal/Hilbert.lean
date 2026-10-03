import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal

/-!
# Canonical Hilbert realization of the lower forcing branch

The intrinsic three-way terminal obstruction still presents its lower branch
as the scalar mass

    M₂(t) = ∫ q(ξ)² |F_j(t,ξ)|² dξ.

This file packages the corresponding canonical Fourier `L²` factor

    C_j(t) = q(ξ) F_j(t,ξ),

so that

    ‖C_j(t)‖² = M₂(t).

The cofinal obstruction can then be written uniformly in Hilbert norm-square
language:

* `‖q F_j‖²` is cofinally unbounded; or
* `‖d/dt (q² û_j)‖²` is cofinally unbounded; or
* `‖q³ û_j‖²` is cofinally unbounded.

No lower-order temporal derivative is introduced in this checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForcingPDECofinalHilbert
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Canonical q forcing state -/

/--
At every strict physical time, the lower neighboring forcing factor `q F_j`
belongs to Fourier `L²`.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQ_memLp2
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
        ((h3FourierGradientSquare ξ : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          U U j ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U U j

  have hN2 :
      MemLp
        N
        2
        (volume : Measure H3FourierPoint3) := by

    dsimp only [N]

    exact
      h3RawFinLerayOuterProductDivergence_memLp2
        U U j

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ : ℝ) : ℂ)
            *
          N ξ)
        (volume : Measure H3FourierPoint3) := by

    exact
      (
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          h3FourierGradientSquare_aestronglyMeasurable
      ).mul
        hN2.1

  rw [
    memLp_two_iff_integrable_sq_norm
      hMeas
  ]

  have hDensityRaw :=
    integrable_h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
      hH3 hClass ht j

  unfold
    h3TerminalPhysicalTopDissipationForcingSecondQDensityAt
    at hDensityRaw

  dsimp only at hDensityRaw

  have hDensity :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 2
            *
          ‖N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    simpa only [htAbs, U, N] using
      hDensityRaw

  refine
    hDensity.congr
      ?_

  filter_upwards with ξ

  have hq :
      0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hq,
    mul_pow
  ]

/--
Canonical strict-time Fourier `L²` state representing `q F_j`.
-/
noncomputable def h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
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
    h3TerminalPhysicalTopDissipationForcingSecondQ_memLp2
      hH3 hClass ht j
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ : ℝ) : ℂ)
        *
      h3RawFinLerayOuterProductDivergence
        U U j ξ)

/--
The canonical lower forcing state has the literal `q F_j` representative.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_ae
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
      h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ : ℝ) : ℂ)
        *
      h3RawFinLerayOuterProductDivergence
        U U j ξ) := by

  dsimp only

  unfold
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At

  exact
    MemLp.coeFn_toLp
      (
        h3TerminalPhysicalTopDissipationForcingSecondQ_memLp2
          hH3 hClass ht j
      )

/--
The lower neighboring forcing mass is exactly the squared Hilbert norm of the
canonical `q F_j` state.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
          hH3 hClass ht j‖ : ℝ
    ) ^ 2
      =
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt
      hH3 hClass ht j := by

  rw [
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq
  ]

  unfold
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt

  apply
    integral_congr_ae

  filter_upwards [
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_ae
      hH3 hClass ht j
  ] with ξ hξ

  rw [hξ]

  unfold
    h3TerminalPhysicalTopDissipationForcingSecondQDensityAt

  dsimp only

  have hq :
      0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hq,
    mul_pow
  ]

/-! ## Zero-extended qF path -/

noncomputable def h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path,
    ht
  ]

theorem h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq_norm_sq_secondQFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingSecondQMassPath
        hH3 hClass j t
      =
    (
      ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
          hH3 hClass j t‖ : ℝ
    ) ^ 2 := by

  rw [
    h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq
      hH3 hClass ht j,
    norm_sq_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
      hH3 hClass ht j
  ]

/-! ## Uniform Hilbert form of the cofinal obstruction -/

/--
The intrinsic three-way terminal obstruction with every channel expressed as a
squared Hilbert norm.
-/
theorem exists_fixed_thirdRadialForcing_HilbertPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      (
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                M
                  <
                (
                  ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
                      hH3 hClass j₀ t‖ : ℝ
                ) ^ 2
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                M
                  <
                (
                  ‖deriv
                      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                        hH3 hClass j₀)
                      t‖ : ℝ
                ) ^ 2
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                M
                  <
                (
                  ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                      hH3 hClass j₀ t‖ : ℝ
                ) ^ 2
        )
      ) := by

  obtain
    ⟨j₀, hBranch⟩ :=
    exists_fixed_thirdRadialForcing_PDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  refine
    ⟨
      j₀,
      ?_
    ⟩

  rcases hBranch with hSecond | hTemporal | hDiffusion

  · left

    intro c hc M

    obtain
      ⟨t, htTail, hLarge⟩ :=
      hSecond c hc M

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htTail.1,
        htTail.2
      ⟩

    rw [
      h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq_norm_sq_secondQFourierL2Path
        hH3 hClass ht j₀
    ] at hLarge

    exact
      ⟨
        t,
        htTail,
        hLarge
      ⟩

  · right
    left

    exact hTemporal

  · right
    right

    exact hDiffusion

/-! ## Neutral continuation alternative in Hilbert form -/

/--
Neutral endpoint formulation with all three obstruction channels represented
as squared Hilbert norms.
-/
theorem smoothContinuationExtension_or_fixed_thirdRadialForcing_HilbertPDEChannel_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ j₀ : Fin 3,
        (
          (
            ∀ c : ℝ,
              c ∈ Set.Ioo a T →
              ∀ M : ℝ,
                ∃ t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  M
                    <
                  (
                    ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
                        hH3 hClass j₀ t‖ : ℝ
                  ) ^ 2
          )
            ∨
          (
            ∀ c : ℝ,
              c ∈ Set.Ioo a T →
              ∀ M : ℝ,
                ∃ t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  M
                    <
                  (
                    ‖deriv
                        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                          hH3 hClass j₀)
                        t‖ : ℝ
                  ) ^ 2
          )
            ∨
          (
            ∀ c : ℝ,
              c ∈ Set.Ioo a T →
              ∀ M : ℝ,
                ∃ t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  M
                    <
                  (
                    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                        hH3 hClass j₀ t‖ : ℝ
                  ) ^ 2
          )
        )
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_thirdRadialForcing_HilbertPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3
            hClass
            hPhysical
            hCauchy
            hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
