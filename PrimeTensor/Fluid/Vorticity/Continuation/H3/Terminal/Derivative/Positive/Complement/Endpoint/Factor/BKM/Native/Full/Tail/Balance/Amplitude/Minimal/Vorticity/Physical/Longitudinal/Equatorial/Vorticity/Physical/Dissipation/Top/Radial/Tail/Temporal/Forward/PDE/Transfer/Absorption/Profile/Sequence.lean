import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Terminal

/-!
# Terminal blowup sequence for the cubic forcing mass

The previous checkpoint proves that, under the retained endpoint hypotheses and
hypothetical nonextension, the continuous nonnegative cubic forcing profile has
infinite `L¹` mass on every terminal tail `(c,T)`.

On a finite interval this immediately rules out every finite pointwise upper
bound.  Indeed, if

    G(t) ≤ M  on (c,T),

then nonnegativity gives `|G(t)| = G(t) ≤ max M 0`, and the constant
`max M 0` is integrable on `(c,T)`.  Continuity supplies the required
measurability, contradicting terminal-tail nonintegrability.

Thus `G` is cofinally unbounded at `T`.  Choosing a point above level `n` in
the localized tail

    (T - 1/(n+1), T)

produces a strict preterminal sequence `τₙ -> T` with `G(τₙ) -> +∞`.

These remain necessary consequences conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingSequence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Cofinal pointwise unboundedness -/

/--
Under the retained endpoint hypotheses and nonextension, the physical cubic
forcing mass exceeds every finite threshold arbitrarily late on every strict
terminal tail.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          M
            <
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass t := by

  intro c hc M

  have hNotInt :
      ¬
        IntegrableOn
          (
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass
          )
          (Set.Ioo c T)
          volume :=
    not_integrableOn_fullForcingCubicMassProfile_every_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hc

  by_contra hExists

  have hBound :
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass t
          ≤
        M := by

    intro t ht

    by_contra hLe

    have hGt :
        M
          <
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass t :=
      lt_of_not_ge hLe

    exact
      hExists
        ⟨
          t,
          ht,
          hGt
        ⟩

  have hCont :
      ContinuousOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo c T) := by

    exact
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
          hH3 hClass
      ).mono
        (by
          intro t ht

          exact
            ⟨
              lt_trans
                hc.1
                ht.1,
              ht.2
            ⟩)

  have hMeas :
      AEStronglyMeasurable
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (
          (volume : Measure ℝ).restrict
            (Set.Ioo c T)
        ) :=
    ContinuousOn.aestronglyMeasurable
      hCont
      measurableSet_Ioo

  have hConst :
      IntegrableOn
        (fun _ : ℝ => max M 0)
        (Set.Ioo c T)
        volume := by

    exact
      integrableOn_const
        measure_Ioo_lt_top.ne

  have hInt :
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo c T)
        volume := by

    apply
      Integrable.mono'
        hConst
        hMeas

    filter_upwards
      [
        ae_restrict_mem
          measurableSet_Ioo
      ]
      with t ht

    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_nonneg
            hH3 hClass
        )
    ]

    exact
      (hBound t ht).trans
        (le_max_left M 0)

  exact
    hNotInt hInt

/-! ## Sequential extraction -/

/--
There is a strict preterminal sequence converging to `T` along which the
physical cubic forcing mass exceeds `n` and hence tends to `+∞`.
-/
theorem exists_h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          (n : ℝ)
            <
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass (τ n)
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass (τ n)
        )
        atTop
        atTop := by

  have hCofinal :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          t ∈ Set.Ioo a T
            ∧
          t ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass t := by

    intro n

    let ε : ℝ :=
      (1 : ℝ) / ((n : ℝ) + 1)

    have hε :
        0 < ε := by

      dsimp only [ε]
      positivity

    let l : ℝ :=
      max
        a
        (T - ε)

    have hlT :
        l < T := by

      dsimp only [l]

      exact
        max_lt
          hClass.terminal_start.2
          (by linarith)

    let c : ℝ :=
      h3BKMKineticTailMidpoint
        l
        T

    have hcL :
        c ∈ Set.Ioo l T := by

      dsimp only [c]

      exact
        h3BKMKineticTailMidpoint_mem_Ioo
          hlT

    have hc :
        c ∈ Set.Ioo a T := by

      exact
        ⟨
          lt_of_le_of_lt
            (le_max_left a (T - ε))
            hcL.1,
          hcL.2
        ⟩

    have hcNear :
        T - ε < c := by

      exact
        lt_of_le_of_lt
          (le_max_right a (T - ε))
          hcL.1

    obtain
      ⟨t, ht, hMass⟩ :=
      hCofinal
        c hc
        (n : ℝ)

    have htClass :
        t ∈ Set.Ioo a T := by

      exact
        ⟨
          lt_trans
            hc.1
            ht.1,
          ht.2
        ⟩

    have htNear :
        t ∈ Set.Ioo (T - ε) T := by

      exact
        ⟨
          lt_trans
            hcNear
            ht.1,
          ht.2
        ⟩

    exact
      ⟨
        t,
        htClass,
        by
          simpa only [ε] using htNear,
        hMass
      ⟩

  choose τ hτ using
    hChoice

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by

    rw [Metric.tendsto_atTop]

    intro ε hε

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        (1 / ε)

    refine
      ⟨
        N,
        ?_
      ⟩

    intro n hn

    have hDenN :
        0 < (N : ℝ) + 1 := by
      positivity

    have hInvN :
        (1 : ℝ) / ((n : ℝ) + 1)
          ≤
        1 / ((N : ℝ) + 1) := by

      exact
        one_div_le_one_div_of_le
          hDenN
          (by
            have hCast :
                (N : ℝ) ≤ n := by
              exact_mod_cast hn
            linarith)

    have hSmallN :
        1 / ((N : ℝ) + 1) < ε := by

      have hNPlus :
          1 / ε < (N : ℝ) + 1 := by
        linarith [hN]

      have hMulRaw :
          1 < ((N : ℝ) + 1) * ε :=
        (div_lt_iff₀ hε).1
          hNPlus

      exact
        (div_lt_iff₀ hDenN).2
          (by
            simpa only [mul_comm, one_mul] using hMulRaw)

    have hSmall :
        (1 : ℝ) / ((n : ℝ) + 1) < ε :=
      lt_of_le_of_lt
        hInvN
        hSmallN

    have hLower :=
      (hτ n).2.1.1

    have hUpper :=
      (hτ n).2.1.2

    rw [Real.dist_eq]

    have hDiffNonpos :
        τ n - T ≤ 0 := by
      linarith

    rw [abs_of_nonpos hDiffNonpos]

    linarith

  have hMassTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass (τ n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        M

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    have hNat :
        M < (n : ℝ) := by

      exact
        lt_of_lt_of_le
          hN
          (by exact_mod_cast hn)

    exact
      le_of_lt
        (
          lt_trans
            hNat
            (hτ n).2.2
        )

  exact
    ⟨
      τ,
      hτ,
      hTauTendsto,
      hMassTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
