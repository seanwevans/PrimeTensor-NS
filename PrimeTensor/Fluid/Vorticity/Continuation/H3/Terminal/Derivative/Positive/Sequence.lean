import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Integrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Near.Alternative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Terminal blowup sequence for the positive H³-energy derivative

The preceding integral theorem shows that hypothetical nonextension forces
infinite positive H³-energy variation.  This file adds a pointwise terminal
statement.

Fix any terminal H³ energy-class tail `(a,T)`, any neighborhood size `ε > 0`,
and any derivative threshold `M`.  Choose a late anchor

    b ∈ (max a (T-ε), T).

The nonextension energy alternative supplies a later point `t ∈ (b,T)` with
energy so large that

    E(t) - E(b) > max(M,0) (T-b).

Since `t-b < T-b`, the secant slope from `b` to `t` is larger than `M`.
Compact-tail continuity and strict-tail differentiability allow Lagrange's
mean-value theorem to produce

    s ∈ (b,t),    M < E'(s).

Hence the raw H³-energy derivative is arbitrarily large arbitrarily near the
terminal time.  Choosing `ε_n = 1/(n+1)` and `M_n = n` gives a sequence
`s_n -> T` with `E'(s_n) -> +∞`.

Exact H³ balance then transfers the same sequence to the unnormalized
full-dissipation transport excess

    max(0, -T_H3 - 2D).

These are necessary consequences of hypothetical nonextension, not assertions
that such a path exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Arbitrarily large positive derivative arbitrarily near T -/

/--
Under hypothetical nonextension, the raw canonical H³-energy derivative is
arbitrarily large in every left neighborhood of `T`.

The selected time is also recorded inside the supplied energy-class tail so
that exact balance is immediately available there.
-/
theorem deriv_velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ ε : ℝ,
      0 < ε →
      ∀ M : ℝ,
        ∃ s : ℝ,
          s ∈ Set.Ioo (T - ε) T
            ∧
          s ∈ Set.Ioo a T
            ∧
          M < deriv (velocityH3EnergyAt u) s := by

  intro ε hε M

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

  let b : ℝ :=
    h3BKMKineticTailMidpoint
      l
      T

  have hb :
      b ∈ Set.Ioo l T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hlT

  have hab :
      a < b := by

    exact
      lt_of_le_of_lt
        (le_max_left a (T - ε))
        hb.1

  have hNear :
      T - ε < b := by

    exact
      lt_of_le_of_lt
        (le_max_right a (T - ε))
        hb.1

  have hbAbs :
      b ∈ Set.Ioo (0 : ℝ) T := by

    exact
      ⟨
        lt_trans
          hClass.terminal_start.1
          hab,
        hb.2
      ⟩

  let K : ℝ :=
    max M 0

  let N : ℝ :=
    velocityH3EnergyAt u b
      +
    K * (T - b)
      +
    1

  have hRadius :
      0 < T - b := by
    linarith [hb.2]

  obtain
    ⟨t, htNear, hEnergyLarge⟩ :=
    velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
      hH3
      hNoExtension
      (T - b)
      hRadius
      N

  have hbt :
      b < t := by

    have hLower :
        T - (T - b) = b := by
      ring

    rw [hLower] at htNear

    exact htNear.1

  have htT :
      t < T :=
    htNear.2

  have hContTail :
      CanonicalH3EnergyContinuousOnTail
        u b T :=
    hH3.canonicalH3EnergyContinuousOnTail
      hbAbs

  have hContinuous :
      ContinuousOn
        (velocityH3EnergyAt u)
        (Set.Icc b t) :=

    hContTail
      t
      ⟨
        le_of_lt hbt,
        htT
      ⟩

  have hDifferentiable :
      DifferentiableOn ℝ
        (velocityH3EnergyAt u)
        (Set.Ioo b t) := by

    intro s hs

    have hsClass :
        s ∈ Set.Ioo a T := by

      exact
        ⟨
          lt_trans
            hab
            hs.1,
          lt_trans
            hs.2
            htT
        ⟩

    have hDeriv :
        HasDerivAt
          (velocityH3EnergyAt u)
          (deriv (velocityH3EnergyAt u) s)
          s :=
      h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
        h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3
        a hClass
        s hsClass

    exact
      hDeriv.differentiableAt.differentiableWithinAt

  obtain
    ⟨s, hs, hSlope⟩ :=
    exists_deriv_eq_slope
      (velocityH3EnergyAt u)
      hbt
      hContinuous
      hDifferentiable

  have hKNonneg :
      0 ≤ K := by

    dsimp only [K]

    exact
      le_max_right
        M
        0

  have hMK :
      M ≤ K := by

    dsimp only [K]

    exact
      le_max_left
        M
        0

  have htGap :
      t - b < T - b := by
    linarith [htT]

  have hScaledGap :
      K * (t - b)
        ≤
      K * (T - b) :=

    mul_le_mul_of_nonneg_left
      (le_of_lt htGap)
      hKNonneg

  have hNumerator :
      K * (t - b)
        <
      velocityH3EnergyAt u t
        - velocityH3EnergyAt u b := by

    dsimp only [N] at hEnergyLarge

    linarith

  have hDenPos :
      0 < t - b := by
    linarith [hbt]

  have hSlopeLarge :
      K
        <
      (
        velocityH3EnergyAt u t
          - velocityH3EnergyAt u b
      )
        /
      (t - b) := by

    exact
      (lt_div_iff₀ hDenPos).2
        hNumerator

  have hDerivativeLarge :
      M
        <
      deriv (velocityH3EnergyAt u) s := by

    rw [hSlope]

    exact
      lt_of_le_of_lt
        hMK
        hSlopeLarge

  have hsNear :
      s ∈ Set.Ioo (T - ε) T := by

    exact
      ⟨
        lt_trans
          hNear
          hs.1,
        lt_trans
          hs.2
          htT
      ⟩

  have hsClass :
      s ∈ Set.Ioo a T := by

    exact
      ⟨
        lt_trans
          hab
          hs.1,
        lt_trans
          hs.2
          htT
      ⟩

  exact
    ⟨
      s,
      hsNear,
      hsClass,
      hDerivativeLarge
    ⟩

/-! ## Sequential form -/

/--
There is a strict preterminal sequence converging to `T` along which the raw
canonical H³-energy derivative tends to `+∞`.
-/
theorem exists_deriv_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T
            ∧
          σ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          deriv (velocityH3EnergyAt u) (σ n)
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ =>
          deriv (velocityH3EnergyAt u) (σ n))
        atTop
        atTop := by

  have hChoice :
      ∀ n : ℕ,
        ∃ s : ℝ,
          s ∈ Set.Ioo a T
            ∧
          s ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ)
            <
          deriv (velocityH3EnergyAt u) s := by

    intro n

    have hDen :
        0 < (n : ℝ) + 1 := by
      positivity

    have hε :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      exact one_div_pos.mpr hDen

    obtain
      ⟨s, hsNear, hsClass, hsDeriv⟩ :=
      deriv_velocityH3EnergyAt_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        ((1 : ℝ) / ((n : ℝ) + 1))
        hε
        (n : ℝ)

    exact
      ⟨
        s,
        hsClass,
        hsNear,
        hsDeriv
      ⟩

  choose σ hσ using hChoice

  have hSigmaTendsto :
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

    have hCast :
        (N : ℝ) ≤ n := by
      exact_mod_cast hn

    have hDenN :
        0 < (N : ℝ) + 1 := by
      positivity

    have hDenNPos :
        0 < (n : ℝ) + 1 := by
      positivity

    have hInvN :
        (1 : ℝ) / ((n : ℝ) + 1)
          ≤
        1 / ((N : ℝ) + 1) := by

      exact
        one_div_le_one_div_of_le
          hDenN
          (by linarith)

    have hSmallN :
        1 / ((N : ℝ) + 1) < ε := by

      have hεPos :
          0 < ε :=
        hε

      have hInvEps :
          1 / ε < (N : ℝ) :=
        hN

      have hNPlus :
          1 / ε < (N : ℝ) + 1 := by
        linarith

      have hMulRaw :
          1 < ((N : ℝ) + 1) * ε :=
        (div_lt_iff₀ hεPos).1
          hNPlus

      have hMul :
          1 < ε * ((N : ℝ) + 1) := by
        simpa only [mul_comm] using
          hMulRaw

      exact
        (div_lt_iff₀ hDenN).2
          (by
            simpa only [one_mul] using hMul)

    have hSmall :
        (1 : ℝ) / ((n : ℝ) + 1) < ε :=
      lt_of_le_of_lt
        hInvN
        hSmallN

    have hLower :=
      (hσ n).2.1.1

    have hUpper :=
      (hσ n).2.1.2

    rw [Real.dist_eq]

    have hDiffNonpos :
        σ n - T ≤ 0 := by
      linarith [hUpper]

    rw [abs_of_nonpos hDiffNonpos]

    linarith

  have hDerivativeTendsto :
      Tendsto
        (fun n : ℕ =>
          deriv (velocityH3EnergyAt u) (σ n))
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
        (lt_trans
          hNat
          (hσ n).2.2)

  exact
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hDerivativeTendsto
    ⟩

/-! ## Transfer the sequence through exact balance -/

/--
Along the same terminal sequence, the raw full-dissipation transport excess
tends to `+∞`.
-/
theorem exists_rawFullDissipationTransportExcessPart_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ =>
          h3PathRawFullDissipationTransportExcessPart
            u
            (σ n))
        atTop
        atTop := by

  obtain
    ⟨σ, hσ, hSigmaTendsto, hDerivativeTendsto⟩ :=
    exists_deriv_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hEventuallyEq :
      (
        fun n : ℕ =>
          h3PathRawFullDissipationTransportExcessPart
            u
            (σ n)
      )
        =ᶠ[atTop]
      (
        fun n : ℕ =>
          deriv (velocityH3EnergyAt u) (σ n)
      ) := by

    filter_upwards
      [eventually_ge_atTop 1]
      with n hn

    have hPositive :
        0 <
        deriv (velocityH3EnergyAt u) (σ n) := by

      have hOne :
          (1 : ℝ)
            ≤
          (n : ℝ) := by
        exact_mod_cast hn

      exact
        lt_of_lt_of_le
          (by norm_num)
          (le_of_lt
            (lt_of_le_of_lt
              hOne
              (hσ n).2.2))

    have hExact :=
      h3PathRawFullDissipationTransportExcessPart_eq_positiveEnergyTimeDerivativePart
        hH3
        hClass
        (hσ n).1

    rw [hExact]

    unfold
      h3PathPositiveEnergyTimeDerivativePart

    exact
      max_eq_right
        (le_of_lt hPositive)

  have hRawTendsto :
      Tendsto
        (fun n : ℕ =>
          h3PathRawFullDissipationTransportExcessPart
            u
            (σ n))
        atTop
        atTop :=

    hDerivativeTendsto.congr'
      hEventuallyEq.symm

  exact
    ⟨
      σ,
      (fun n => (hσ n).1),
      hSigmaTendsto,
      hRawTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
