import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Physical representative of the fixed third-radial forcing blowup

The preceding checkpoint freezes one coordinate `j₀ : Fin 3` for which the
canonical third-radial nonlinear-forcing Hilbert norm diverges on a strict
terminal sequence.

The state construction already proved the exact representative identity

    ‖F³_j(t)‖²
      =
    ∫ |ξ|⁶ |P div(U(t) ⊗ U(t))_j(ξ)|² dξ.

This file packages the right-hand side as a physical raw Fourier mass and
transfers the fixed-coordinate sequence to it.  Consequently one fixed
nonlinear PDE forcing coordinate satisfies

    n²
      <
    ∫ |ξ|⁶ |P div(U(τₙ) ⊗ U(τₙ))_{j₀}(ξ)|² dξ

along a sequence `τₙ -> T`, and the physical weighted Fourier integral itself
tends to `+∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1000000

/-! ## Raw physical weighted Fourier mass -/

/--
The actual order-three radial Fourier mass of one nonlinear forcing coordinate
at a strict physical time.
-/
noncomputable def h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 6
      *
    ‖h3RawFinLerayOuterProductDivergence
        U U j ξ‖ ^ 2
    ∂(volume : Measure H3FourierPoint3)

/--
The raw physical third-radial forcing mass is exactly the squared norm of the
canonical quotient-safe Hilbert state.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt_eq_norm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
        hH3 hClass ht j
      =
    (
      ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
          hH3 hClass ht j‖ : ℝ
    ) ^ 2 := by

  unfold
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt

  dsimp only

  exact
    (
      norm_sq_h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
        hH3 hClass ht j
    ).symm

/--
Zero-extended raw physical third-radial forcing mass path.
-/
noncomputable def h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    ℝ :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath,
    ht
  ]

/--
On the strict physical interval, the raw weighted Fourier mass path is exactly
the square of the canonical third-radial forcing Hilbert norm.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq_norm_sq_path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
        hH3 hClass j t
      =
    (
      ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t‖ : ℝ
    ) ^ 2 := by

  rw [
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
      hH3 hClass ht j
  ]

  exact
    h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt_eq_norm_sq
      hH3 hClass ht j

/-! ## Terminal sequence in the raw nonlinear PDE representative -/

/--
Under the retained endpoint hypotheses and hypothetical nonextension, one fixed
nonlinear forcing coordinate has divergent physical order-three radial Fourier
mass on a strict terminal sequence.
-/
theorem exists_fixed_thirdRadialForcingRawFourierMass_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
              ∧
            (n : ℝ) ^ 2
              <
            h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
              hH3 hClass j₀ (τ n)
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
                hH3 hClass j₀ (τ n)
          )
          atTop
          atTop := by

  obtain
    ⟨
      j₀,
      τ,
      hTauData,
      hTauTendsto,
      hNormTendsto
    ⟩ :=
    exists_fixed_thirdRadialForcingComponent_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  have hRawData :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T
          ∧
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T
          ∧
        (n : ℝ) ^ 2
          <
        h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
          hH3 hClass j₀ (τ n) := by

    intro n

    have hNorm :
        (n : ℝ)
          <
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass j₀ (τ n)‖ :=
      (hTauData n).2.2

    have hSq :
        (n : ℝ) ^ 2
          <
        (
          ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j₀ (τ n)‖ : ℝ
        ) ^ 2 :=
      pow_lt_pow_left₀
        hNorm
        (Nat.cast_nonneg n)
        (by norm_num)

    rw [
      h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq_norm_sq_path
        hH3 hClass (hTauData n).1 j₀
    ]

    exact
      ⟨
        (hTauData n).1,
        (hTauData n).2.1,
        hSq
      ⟩

  have hSqTendsto :
      Tendsto
        (
          fun n : ℕ =>
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j₀ (τ n)‖ : ℝ
            ) ^ 2
        )
        atTop
        atTop := by

    exact
      (
        tendsto_pow_atTop
          (α := ℝ)
          (by norm_num : (2 : ℕ) ≠ 0)
      ).comp
        hNormTendsto

  have hEventuallyEq :
      (
        fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
            hH3 hClass j₀ (τ n)
      )
        =ᶠ[atTop]
      (
        fun n : ℕ =>
          (
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j₀ (τ n)‖ : ℝ
          ) ^ 2
      ) := by

    exact
      Filter.Eventually.of_forall
        (fun n =>
          h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq_norm_sq_path
            hH3 hClass (hTauData n).1 j₀)

  have hRawTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
              hH3 hClass j₀ (τ n)
        )
        atTop
        atTop :=

    hSqTendsto.congr'
      hEventuallyEq.symm

  exact
    ⟨
      j₀,
      τ,
      hRawData,
      hTauTendsto,
      hRawTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
