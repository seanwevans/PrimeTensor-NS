import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance

/-!
# Resolve the lower forcing obstruction into terminal PDE channels

The lower forcing Hilbert channel satisfies, on every strict physical slice,

    C_j = -R¹_j - V_j,

where

    C_j  = q F_j,
    R¹_j = -q² û_j - q F_j,
    V_j  = q² û_j.

Hence

    ‖C_j‖² ≤ 2 (‖R¹_j‖² + ‖V_j‖²).

Cofinal unboundedness makes the binary alternative stronger than a mere
pointwise split.  If `R¹_j` is not cofinally unbounded, then it is bounded on
one terminal tail.  The cofinal escape of `C_j` on every smaller tail then
forces `V_j` to be cofinally unbounded on every terminal tail.

Thus the remaining forcing-type branch resolves without another subsequence.

Combining this with the preceding three-way Hilbert obstruction yields four
fixed physical terminal channels:

* lower weighted PDE RHS `R¹_j`;
* fourth-radial velocity/top-dissipation component `q² û_j`;
* fourth-radial temporal derivative `d/dt(q² û_j)`;
* sixth-radial diffusion component `q³ û_j`.

A neutral continuation alternative is recorded at the end.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalLowerWeightedPDEBalanceResolve
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Resolve one cofinally escaping lower forcing channel -/

/--
If the canonical lower forcing factor `q F_j` is cofinally unbounded on every
terminal tail, then either the lower weighted PDE RHS or the fourth-radial
velocity component is cofinally unbounded on every terminal tail.
-/
theorem lowerWeightedPDERHS_or_fourthRadial_cofinallyUnbounded_of_secondQForcing_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hForcing :
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
                  hH3 hClass j t‖ : ℝ
            ) ^ 2) :
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
                  hH3 hClass j t‖ : ℝ
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
              ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j t‖ : ℝ
            ) ^ 2
    ) := by

  classical

  by_cases hRHS :
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
                  hH3 hClass j t‖ : ℝ
            ) ^ 2

  · exact
      Or.inl hRHS

  · right

    push_neg at hRHS

    obtain
      ⟨c₀, hc₀, M₀, hRHSBound⟩ :=
      hRHS

    intro c hc M

    let d : ℝ :=
      max c c₀

    have hd :
        d ∈ Set.Ioo a T := by

      constructor

      · exact
          lt_of_lt_of_le
            hc.1
            (le_max_left c c₀)

      · dsimp only [d]

        exact
          max_lt
            hc.2
            hc₀.2

    let K : ℝ :=
      max M 0

    obtain
      ⟨t, htD, hForcingLarge⟩ :=
      hForcing
        d
        hd
        (2 * (M₀ + K))

    have htC :
        t ∈ Set.Ioo c T := by

      constructor

      · exact
          lt_of_le_of_lt
            (le_max_left c c₀)
            htD.1

      · exact htD.2

    have htC₀ :
        t ∈ Set.Ioo c₀ T := by

      constructor

      · exact
          lt_of_le_of_lt
            (le_max_right c c₀)
            htD.1

      · exact htD.2

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htC.1,
        htC.2
      ⟩

    have hRHSLe :
        (
          ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
              hH3 hClass j t‖ : ℝ
        ) ^ 2
          ≤
        M₀ :=
      hRHSBound
        t
        htC₀

    have hTriangle :=
      norm_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_le_lowerWeightedPDERHSPath_add_fourthRadialPath
        hH3
        hClass
        ht
        j

    have hForcingSq :
        (
          ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
              hH3 hClass j t‖ : ℝ
        ) ^ 2
          ≤
        (
          ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
              hH3 hClass j t‖
            +
          ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j t‖
        ) ^ 2 := by

      exact
        pow_le_pow_left₀
          (norm_nonneg _)
          hTriangle
          2

    have hSumSq :
        (
          ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
              hH3 hClass j t‖
            +
          ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j t‖
        ) ^ 2
          ≤
        2 *
          (
            (
              ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
                  hH3 hClass j t‖ : ℝ
            ) ^ 2
              +
            (
              ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j t‖ : ℝ
            ) ^ 2
          ) := by

      nlinarith
        [
          sq_nonneg
            (
              ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
                  hH3 hClass j t‖
                -
              ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j t‖
            )
        ]

    have hMLeK :
        M ≤ K := by

      dsimp only [K]

      exact
        le_max_left M 0

    have hVelocityLarge :
        M
          <
        (
          ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j t‖ : ℝ
        ) ^ 2 := by

      by_contra hNotLarge

      have hVelocityLeM :
          (
            ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass j t‖ : ℝ
          ) ^ 2
            ≤
          M :=
        le_of_not_gt hNotLarge

      have hVelocityLeK :
          (
            ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass j t‖ : ℝ
          ) ^ 2
            ≤
          K :=
        hVelocityLeM.trans
          hMLeK

      linarith

    exact
      ⟨
        t,
        htC,
        hVelocityLarge
      ⟩

/-! ## Four fixed terminal channels -/

/--
Under the retained endpoint hypotheses and hypothetical nonextension, one fixed
physical coordinate has one of four fixed Hilbert channels cofinally unbounded
on every strict terminal tail.
-/
theorem exists_fixed_thirdRadialForcing_resolvedHilbertPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
                (
                  ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
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
    exists_fixed_thirdRadialForcing_HilbertPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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

  rcases hBranch with hForcing | hTemporal | hDiffusion

  · have hLower :=
      lowerWeightedPDERHS_or_fourthRadial_cofinallyUnbounded_of_secondQForcing_cofinallyUnbounded
        hH3
        hClass
        j₀
        hForcing

    rcases hLower with hRHS | hVelocity

    · exact
        Or.inl hRHS

    · exact
        Or.inr
          (Or.inl hVelocity)

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

/-! ## Neutral continuation alternative -/

/--
Neutral endpoint formulation after resolving the last forcing-type branch.
-/
theorem smoothContinuationExtension_or_fixed_thirdRadialForcing_resolvedHilbertPDEChannel_cofinallyUnbounded
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
                  (
                    ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
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
          exists_fixed_thirdRadialForcing_resolvedHilbertPDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
