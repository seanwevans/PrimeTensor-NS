import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fourier.Identification

/-!
# Identify the fourth-radial velocity channel with physical top dissipation

The resolved terminal PDE obstruction contains the componentwise Hilbert channel

    ‖q² û_j(t)‖².

The project already identifies the full physical top H³ dissipation block with

    velocityH3Dissipation3At u t
      =
    Σ_j ∫ q⁴ |û_j|².

This file closes the component/full bookkeeping:

* the squared norm of the terminal fourth-radial component is exactly its
  `q⁴ |û_j|²` integral;
* that component is bounded by the full fourth-radial moment;
* therefore componentwise cofinal escape forces
  `velocityH3Dissipation3At u t` itself to be cofinally unbounded.

The resolved terminal alternative can consequently be stated using the named
physical top-dissipation scalar instead of a coordinatewise Fourier state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalResolvedTopDissipation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## One fourth-radial component -/

/--
The squared Hilbert norm of one physical fourth-radial coordinate is exactly
that coordinate's `q⁴ |û_j|²` mass.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes htAbs
    (
      ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass ht j‖ : ℝ
    ) ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 4
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  rw [
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq
  ]

  apply integral_congr_ae

  filter_upwards [
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae
      hH3 hClass ht j
  ] with ξ hξ

  rw [hξ]

  unfold
    h3TerminalPhysicalTopDissipationFourthRadialComponent

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

/--
One fourth-radial coordinate is bounded by the full physical top H³
dissipation block.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_le_velocityH3Dissipation3At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    (
      ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass ht j‖ : ℝ
    ) ^ 2
      ≤
    velocityH3Dissipation3At u t := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  have hComponent :
      (
        ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
            hH3 hClass ht j‖ : ℝ
      ) ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 4
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
        ∂(volume : Measure H3FourierPoint3) := by

    simpa only [htAbs, hInt, hMeas] using
      (
        norm_sq_h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass ht j
      )

  have hMoment :
      velocityH3Dissipation3At u t
        =
      velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas := by

    simpa only [htAbs, hInt, hMeas] using
      (
        velocityH3Dissipation3At_eq_fourierFourthRadialMoment_on_h3Path
          hH3 hClass ht
      )

  rw [hComponent, hMoment]

  unfold
    velocityH3FourierFourthRadialMomentAt

  let componentMass : Fin 3 → ℝ :=
    fun k =>
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 4
          *
        ‖velocityH3BaseFourierAt
            u t hInt hMeas k ξ‖ ^ 2
        ∂(volume : Measure H3FourierPoint3)

  have hComponentNonneg :
      ∀ k : Fin 3,
        0 ≤ componentMass k := by

    intro k

    dsimp only [componentMass]

    exact
      integral_nonneg
        (fun ξ =>
          mul_nonneg
            (pow_nonneg
              (h3FourierGradientSquare_nonneg ξ)
              4)
            (sq_nonneg
              ‖velocityH3BaseFourierAt
                  u t hInt hMeas k ξ‖))

  change
    componentMass j
      ≤
    ∑ k : Fin 3, componentMass k

  exact
    Finset.single_le_sum
      (fun k _ =>
        hComponentNonneg k)
      (Finset.mem_univ j)

/-! ## Zero-extended top-dissipation profile -/

noncomputable def h3TerminalPhysicalTopDissipation3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) :
    ℝ :=
  if ht : t ∈ Set.Ioo a T then
    velocityH3Dissipation3At u t
  else
    0

theorem h3TerminalPhysicalTopDissipation3Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipation3Path hClass t
      =
    velocityH3Dissipation3At u t := by

  simp [
    h3TerminalPhysicalTopDissipation3Path,
    ht
  ]

/--
Cofinal escape of one fourth-radial component forces cofinal escape of the
whole physical top H³ dissipation block.
-/
theorem topDissipation3_cofinallyUnbounded_of_fourthRadialComponent_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hComponent :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∀ M : ℝ,
          ∃ t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            M
              <
            (
              ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j t‖ : ℝ
            ) ^ 2) :
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          M
            <
          h3TerminalPhysicalTopDissipation3Path
            hClass t := by

  intro c hc M

  obtain
    ⟨t, htTail, hLarge⟩ :=
    hComponent c hc M

  have ht :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hc.1 htTail.1,
      htTail.2
    ⟩

  rw [
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
      hH3 hClass ht j
  ] at hLarge

  have hLe :=
    norm_sq_h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_le_velocityH3Dissipation3At
      hH3 hClass ht j

  have hTop :
      M < velocityH3Dissipation3At u t :=
    lt_of_lt_of_le
      hLarge
      hLe

  exact
    ⟨
      t,
      htTail,
      by
        simpa only [
          h3TerminalPhysicalTopDissipation3Path_eq
            hClass ht
        ] using hTop
    ⟩

/-! ## Resolved terminal obstruction with named top dissipation -/

/--
The four-channel terminal obstruction with the coordinatewise fourth-radial
velocity branch replaced by the named physical top H³ dissipation scalar.
-/
theorem exists_fixed_thirdRadialForcing_resolvedPhysicalPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
                  ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
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
                h3TerminalPhysicalTopDissipation3Path
                  hClass t
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
    exists_fixed_thirdRadialForcing_resolvedHilbertPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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

  rcases hBranch with hRHS | hVelocity | hTemporal | hDiffusion

  · exact
      Or.inl hRHS

  · exact
      Or.inr
        (
          Or.inl
            (
              topDissipation3_cofinallyUnbounded_of_fourthRadialComponent_cofinallyUnbounded
                hH3
                hClass
                j₀
                hVelocity
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (Or.inl hTemporal)
        )

  · exact
      Or.inr
        (
          Or.inr
            (Or.inr hDiffusion)
        )

/--
Neutral continuation alternative with the top-order velocity branch expressed
as the named physical scalar `velocityH3Dissipation3At`.
-/
theorem smoothContinuationExtension_or_fixed_thirdRadialForcing_resolvedPhysicalPDEChannel_cofinallyUnbounded
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
                    ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
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
                  h3TerminalPhysicalTopDissipation3Path
                    hClass t
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

  · exact Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_thirdRadialForcing_resolvedPhysicalPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
