import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Diffusion.Continuity

/-!
# Lower weighted temporal derivative frontier

The only remaining algebraic channel in the resolved terminal PDE obstruction is

    R¹_j = -q² û_j - q F_j.

The canonical lower weighted velocity state itself already exists without any
new estimate: the spectral H³ library packages the raw Fourier Laplacian

    Δ û_j = -q û_j

as an `H3FourierComplexL2` state.  Negating it gives the canonical terminal
state

    L_j = q û_j.

This file packages `L_j` and isolates the exact remaining temporal frontier

    d/dt L_j = R¹_j.

No claim that this frontier is already closed is made here.  Instead, the final
theorem shows precisely what closing it buys: the hypothetical nonextension
alternative becomes a four-way statement involving only genuine temporal or
dissipative physical channels.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalLowerWeightedDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Canonical q-weighted physical velocity state -/

/--
Canonical strict-time lower weighted velocity state `q û_j`.

The spectral Laplacian is `-q û_j`, so this is its negative.
-/
noncomputable def h3TerminalPhysicalLowerWeightedVelocityFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  (-
    h3SpectralScalarLaplacianRawFourierL2
      ((h3TerminalVelocitySpectralStateAt hH3 t htAbs) j))

/--
The canonical lower weighted velocity state has the literal representative
`q(ξ) û_j(t,ξ)` almost everywhere.
-/
theorem h3TerminalPhysicalLowerWeightedVelocityFourierL2At_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    ((
      h3TerminalPhysicalLowerWeightedVelocityFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (h3FourierGradientSquare ξ : ℂ)
        *
      h3SpectralScalarRawFourierL2
        ((h3TerminalVelocitySpectralStateAt hH3 t htAbs) j)
        ξ) := by

  dsimp only

  let G : H3SpectralScalarState :=
    (h3TerminalVelocitySpectralStateAt
      hH3 t
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) j

  change
    (((-h3SpectralScalarLaplacianRawFourierL2 G :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (h3FourierGradientSquare ξ : ℂ)
        *
      h3SpectralScalarRawFourierL2 G ξ)

  have hLap :=
    h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
      G

  have hNeg :=
    MeasureTheory.Lp.coeFn_neg
      (h3SpectralScalarLaplacianRawFourierL2 G)

  filter_upwards [hNeg, hLap] with ξ hNegξ hLapξ

  rw [hNegξ]
  simp only [Pi.neg_apply]
  rw [hLapξ]
  ring

/-! ## Zero-extended lower weighted path -/

noncomputable def h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalLowerWeightedVelocityFourierL2At
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalLowerWeightedVelocityFourierL2At
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalLowerWeightedVelocityFourierL2Path,
    ht
  ]

/-! ## Exact remaining temporal frontier -/

/--
The precise lower weighted temporal frontier.

At every strict physical time and every coordinate, the canonical path
`q û_j` should have strong Fourier `L²` derivative equal to the already
canonical lower weighted PDE RHS

    -q² û_j - q F_j.
-/
def H3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∀ (t : ℝ),
    ∀ (ht : t ∈ Set.Ioo a T),
      ∀ j : Fin 3,
        HasDerivAt
          (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
            hH3 hClass j)
          (h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
            hH3 hClass ht j)
          t

/--
Under the lower weighted derivative frontier, the ordinary derivative of the
canonical `q û_j` path is exactly the canonical lower weighted PDE RHS.
-/
theorem deriv_h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq_lowerWeightedPDERHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDerivative :
      H3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint
        hH3 hClass)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    deriv
        (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
          hH3 hClass j)
        t
      =
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
      hH3 hClass ht j := by

  exact
    (hDerivative t ht j).deriv

/-! ## Fully temporal/dissipative obstruction under the frontier -/

/--
Once the lower weighted derivative frontier is closed, the resolved
nonextension obstruction contains no merely algebraic forcing channel.

For one fixed coordinate, one of the following is cofinally unbounded on every
strict terminal tail:

1. the strong temporal derivative of `q û_j`;
2. the named physical top H³ dissipation block;
3. the strong temporal derivative of `q² û_j`;
4. the sixth-radial diffusion state `q³ û_j`.
-/
theorem exists_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded_of_lowerWeightedDerivative_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDerivative :
      H3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint
        hH3 hClass)
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
                  ‖deriv
                      (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
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
    exists_fixed_thirdRadialForcing_resolvedPhysicalPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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

  rcases hBranch with hRHS | hTop | hTemporal | hDiffusion

  · left

    intro c hc M

    obtain
      ⟨t, htTail, hLarge⟩ :=
      hRHS c hc M

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htTail.1,
        htTail.2
      ⟩

    rw [
      h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path_eq
        hH3 hClass ht j₀
    ] at hLarge

    have hDeriv :=
      deriv_h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq_lowerWeightedPDERHS
        hH3 hClass hDerivative ht j₀

    exact
      ⟨
        t,
        htTail,
        by
          rw [hDeriv]
          exact hLarge
      ⟩

  · exact
      Or.inr
        (Or.inl hTop)

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
Neutral continuation alternative conditional only on the explicitly isolated
lower weighted derivative frontier.
-/
theorem smoothContinuationExtension_or_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded_of_lowerWeightedDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDerivative :
      H3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint
        hH3 hClass)
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
                    ‖deriv
                        (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
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

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded_of_lowerWeightedDerivative_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3
            hClass
            hDerivative
            hPhysical
            hCauchy
            hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
