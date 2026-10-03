import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch

/-!
# Canonical fourth-order forcing state on the frozen adjacent branch

The fourth branch isolated above is the physical mass

    M₄(t) = ∫ q(ξ)^4 |F_j(t,ξ)|² dξ.

The already-closed fourth-radial PDE representative uses the Fourier `L²`
forcing factor

    q(ξ)^2 F_j(t,ξ).

This file identifies those two objects exactly.

At every strict physical time, package `q² F_j` as a canonical
`H3FourierComplexL2` state.  Its squared Hilbert norm is exactly `M₄`.

Consequently the frozen adjacent-order alternative can be sharpened without
changing its lower-order branch:

* either the second square-gradient forcing mass tends to `+∞`; or
* the squared norm of the canonical `q² F_j` PDE forcing state tends to `+∞`.

No derivative order is gained or discarded here; the fourth branch is only
rewritten in the exact Hilbert form used by the existing PDE identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForcingAdjacentBranchPDE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Canonical q² forcing state -/

/--
At every strict physical time, the fourth-order square-gradient forcing factor
`q² F_j` belongs to Fourier `L²`.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQ_memLp2
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
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
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
          ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          N ξ)
        (volume : Measure H3FourierPoint3) := by

    exact
      (
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          (h3FourierGradientSquare_aestronglyMeasurable.pow 2)
      ).mul
        hN2.1

  rw [
    memLp_two_iff_integrable_sq_norm
      hMeas
  ]

  have hDensityRaw :=
    integrable_h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
      hH3 hClass ht j

  unfold
    h3TerminalPhysicalTopDissipationForcingFourthQDensityAt
    at hDensityRaw

  dsimp only at hDensityRaw

  have hDensity :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 4
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
    abs_of_nonneg
      (pow_nonneg hq 2),
    mul_pow
  ]

  ring

/--
Canonical strict-time Fourier `L²` state representing `q² F_j`.
-/
noncomputable def h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
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
    h3TerminalPhysicalTopDissipationForcingFourthQ_memLp2
      hH3 hClass ht j
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
        *
      h3RawFinLerayOuterProductDivergence
        U U j ξ)

/--
The canonical fourth-order forcing state has exactly the `q² F_j` raw
representative used by the fourth-radial PDE factor theorem.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_ae
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
      h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
        *
      h3RawFinLerayOuterProductDivergence
        U U j ξ) := by

  dsimp only

  unfold
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At

  exact
    MemLp.coeFn_toLp
      (
        h3TerminalPhysicalTopDissipationForcingFourthQ_memLp2
          hH3 hClass ht j
      )

/--
The fourth square-gradient forcing mass is exactly the squared Hilbert norm of
the canonical `q² F_j` state.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
          hH3 hClass ht j‖ : ℝ
    ) ^ 2
      =
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt
      hH3 hClass ht j := by

  rw [
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq
  ]

  unfold
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt

  apply
    integral_congr_ae

  filter_upwards [
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_ae
      hH3 hClass ht j
  ] with ξ hξ

  rw [hξ]

  unfold
    h3TerminalPhysicalTopDissipationForcingFourthQDensityAt

  dsimp only

  have hq :
      0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (pow_nonneg hq 2),
    mul_pow
  ]

  ring

/-! ## Zero-extended PDE forcing state path -/

noncomputable def h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path,
    ht
  ]

theorem h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq_norm_sq_fourthQFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingFourthQMassPath
        hH3 hClass j t
      =
    (
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t‖ : ℝ
    ) ^ 2 := by

  rw [
    h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
      hH3 hClass ht j,
    norm_sq_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
      hH3 hClass ht j
  ]

/-! ## Frozen branch in exact PDE Hilbert form -/

/--
The frozen adjacent radial forcing alternative with the fourth branch expressed
as the squared norm of the canonical `q² F_j` Fourier `L²` state.
-/
theorem exists_fixed_thirdRadialForcing_adjacentQOrder_or_fourthQPDEFactor_blowupSubsequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      ∃ τ : ℕ → ℝ,
        (
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        (
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                  hH3 hClass j₀ (τ n)
            )
            atTop
            atTop
          ∨
          Tendsto
            (
              fun n : ℕ =>
                (
                  ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                      hH3 hClass j₀ (τ n)‖ : ℝ
                ) ^ 2
            )
            atTop
            atTop
        ) := by

  obtain
    ⟨
      j₀,
      τ,
      hTauData,
      hTauTendsto,
      hBranch
    ⟩ :=
    exists_fixed_thirdRadialForcing_adjacentQOrder_blowupSubsequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  refine
    ⟨
      j₀,
      τ,
      hTauData,
      hTauTendsto,
      ?_
    ⟩

  rcases hBranch with hSecond | hFourth

  · exact
      Or.inl hSecond

  · right

    have hEventuallyEq :
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingFourthQMassPath
              hH3 hClass j₀ (τ n)
        )
          =ᶠ[atTop]
        (
          fun n : ℕ =>
            (
              ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                  hH3 hClass j₀ (τ n)‖ : ℝ
            ) ^ 2
        ) := by

      exact
        Filter.Eventually.of_forall
          (
            fun n =>
              h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq_norm_sq_fourthQFourierL2Path
                hH3
                hClass
                (hTauData n).1
                j₀
          )

    exact
      hFourth.congr'
        hEventuallyEq

end

end Euclidean
end Bridge
end PrimeTensor
