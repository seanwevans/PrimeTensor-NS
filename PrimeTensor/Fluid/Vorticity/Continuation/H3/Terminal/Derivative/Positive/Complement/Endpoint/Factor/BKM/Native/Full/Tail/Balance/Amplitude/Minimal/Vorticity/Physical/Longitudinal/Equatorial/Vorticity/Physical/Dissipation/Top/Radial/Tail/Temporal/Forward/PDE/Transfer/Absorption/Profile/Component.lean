import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Sequence
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fixed third-radial forcing component on a terminal blowup sequence

The scalar cubic forcing obstruction satisfies the exact identity

    G(t)
      =
    (2π)^6
      Σ_{j : Fin 3} ‖F³_j(t)‖².

The preceding checkpoint shows that `G` is cofinally unbounded at the terminal
time under the retained endpoint hypotheses and hypothetical nonextension.

For index `n`, ask for a terminal time at which

    G(t) > (2π)^6 * 3 * n².

If every one of the three third-radial forcing coordinates had Hilbert norm at
most `n`, then the exact identity would give the opposite inequality.  Thus at
least one coordinate has norm greater than `n`.

There are only three coordinates.  A finite-component extraction freezes one
coordinate on a strictly increasing subsequence.  The standard terminal
localization survives because `n ≤ φ n`.

Hence one fixed physical third-radial forcing component has Hilbert norm
tending to `+∞` along a strict sequence converging to `T`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingComponent
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1400000

/-! ## Small sequence helpers -/

private theorem tendsto_terminal_of_one_div_natSucc_localization_cubicForcing
    {T : ℝ}
    {σ : ℕ → ℝ}
    (hσ :
      ∀ n : ℕ,
        σ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T) :
    Tendsto σ atTop (𝓝 T) := by

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
    (hσ n).1

  have hUpper :=
    (hσ n).2

  rw [Real.dist_eq]

  have hDiffNonpos :
      σ n - T ≤ 0 := by
    linarith

  rw [abs_of_nonpos hDiffNonpos]

  linarith

private theorem tendsto_atTop_of_natCast_lt_cubicForcing
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        (n : ℝ) < f n) :
    Tendsto f atTop atTop := by

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
          (hf n)
      )

/-! ## A moving coordinate above the indexed threshold -/

/--
Arbitrarily late scalar cubic-mass growth forces one of the three third-radial
forcing coordinates above the corresponding norm threshold.
-/
theorem exists_terminal_thirdRadialForcing_coordinate_above_index
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
    ∀ n : ℕ,
      ∃ t : ℝ,
        ∃ j : Fin 3,
          t ∈ Set.Ioo a T
            ∧
          t ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j t‖ := by

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

  let C : ℝ :=
    (2 * Real.pi) ^ 6

  have hC :
      0 < C := by
    dsimp only [C]
    positivity

  let M : ℝ :=
    C * (3 * (n : ℝ) ^ 2)

  obtain
    ⟨t, ht, hMass⟩ :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      c
      hc
      M

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

  have hSome :
      ∃ j : Fin 3,
        (n : ℝ)
          <
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass j t‖ := by

    by_contra hNo

    have hEach :
        ∀ j : Fin 3,
          ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j t‖
            ≤
          (n : ℝ) := by

      intro j

      exact
        le_of_not_gt
          (fun hj =>
            hNo
              ⟨
                j,
                hj
              ⟩)

    have hEachSq :
        ∀ j : Fin 3,
          (
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j t‖ : ℝ
          ) ^ 2
            ≤
          (n : ℝ) ^ 2 := by

      intro j

      exact
        pow_le_pow_left₀
          (norm_nonneg _)
          (hEach j)
          2

    have hSumLe :
        (
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j t‖ : ℝ
            ) ^ 2
        )
          ≤
        3 * (n : ℝ) ^ 2 := by

      calc
        (
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j t‖ : ℝ
            ) ^ 2
        )
            ≤
          ∑ _j : Fin 3,
            (n : ℝ) ^ 2 := by

              exact
                Finset.sum_le_sum
                  (fun j _hj =>
                    hEachSq j)

        _ =
          3 * (n : ℝ) ^ 2 := by
            simp

    have hProfileLe :
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass t
          ≤
        M := by

      rw [
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_sum_norm_sq_thirdRadialPath
          hH3 hClass htClass
      ]

      dsimp only [M, C]

      exact
        mul_le_mul_of_nonneg_left
          hSumLe
          (le_of_lt hC)

    exact
      (not_lt_of_ge hProfileLe)
        hMass

  obtain
    ⟨j, hj⟩ :=
    hSome

  exact
    ⟨
      t,
      j,
      htClass,
      by
        simpa only [ε] using htNear,
      hj
    ⟩

/-! ## Freeze the finite forcing coordinate -/

/--
Under the retained endpoint hypotheses and hypothetical nonextension, one fixed
third-radial nonlinear-forcing coordinate has Fourier `L²` norm tending to
`+∞` along a strict terminal sequence.

The same fixed coordinate is used at every selected time.
-/
theorem exists_fixed_thirdRadialForcingComponent_blowupSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
            (n : ℝ)
              <
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j₀ (τ n)‖
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j₀ (τ n)‖
          )
          atTop
          atTop := by

  have hChoice :
      ∀ n : ℕ,
        ∃ t : ℝ,
          ∃ j : Fin 3,
            t ∈ Set.Ioo a T
              ∧
            t ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            (n : ℝ)
              <
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j t‖ :=
    exists_terminal_thirdRadialForcing_coordinate_above_index
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  choose σ j hσ using
    hChoice

  let p : ℕ → Fin 3 :=
    fun n =>
      j n

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Fin 3,
          p n = q :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            p n,
            rfl
          ⟩
      )

  obtain
    ⟨
      q,
      hFrequently
    ⟩ :=
    (
      Filter.frequently_exists
    ).1
      hFrequentlySome

  obtain
    ⟨
      φ,
      hPhiMono,
      hFixed
    ⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hPhiTendsto :
      Tendsto φ atTop atTop :=
    hPhiMono.tendsto_atTop

  have hFixedCoordinate :
      ∀ n : ℕ,
        j (φ n) = q := by

    intro n

    simpa only [p] using
      hFixed n

  have hSigmaTendsto :
      Tendsto σ atTop (𝓝 T) :=
    tendsto_terminal_of_one_div_natSucc_localization_cubicForcing
      (fun n => (hσ n).2.1)

  let τ : ℕ → ℝ :=
    fun n =>
      σ (φ n)

  have hTauData :
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
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass q (τ n)‖ := by

    intro n

    have hOld :=
      hσ (φ n)

    have hIndexLeNat :
        n ≤ φ n :=
      hPhiMono.le_apply

    have hIndexLe :
        (n : ℝ) ≤ (φ n : ℝ) := by
      exact_mod_cast
        hIndexLeNat

    have hDenPos :
        0 < (n : ℝ) + 1 := by
      positivity

    have hDenLe :
        (n : ℝ) + 1
          ≤
        (φ n : ℝ) + 1 := by
      linarith

    have hInv :
        (1 : ℝ) / ((φ n : ℝ) + 1)
          ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le
        hDenPos
        hDenLe

    have hNear :
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T := by

      constructor

      · dsimp only [τ]

        have hOldLower :=
          hOld.2.1.1

        linarith

      · dsimp only [τ]

        exact
          hOld.2.1.2

    have hNorm :
        (n : ℝ)
          <
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass q (τ n)‖ := by

      have hOldNorm :=
        hOld.2.2

      rw [
        hFixedCoordinate n
      ] at hOldNorm

      dsimp only [τ]

      exact
        lt_of_le_of_lt
          hIndexLe
          hOldNorm

    exact
      ⟨
        by
          dsimp only [τ]
          exact hOld.1,
        hNear,
        hNorm
      ⟩

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by

    dsimp only [τ]

    exact
      hSigmaTendsto.comp
        hPhiTendsto

  have hNormTendsto :
      Tendsto
        (
          fun n : ℕ =>
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass q (τ n)‖
        )
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_cubicForcing
      (fun n => (hTauData n).2.2)

  exact
    ⟨
      q,
      τ,
      hTauData,
      hTauTendsto,
      hNormTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
