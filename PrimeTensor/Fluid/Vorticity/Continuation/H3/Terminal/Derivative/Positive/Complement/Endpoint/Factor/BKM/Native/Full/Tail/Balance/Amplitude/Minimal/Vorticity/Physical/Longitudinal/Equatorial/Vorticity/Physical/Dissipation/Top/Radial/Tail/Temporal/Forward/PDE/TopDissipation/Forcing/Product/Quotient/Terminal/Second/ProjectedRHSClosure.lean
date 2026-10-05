import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.ProjectedRHS
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Close the second-q projected-RHS primitives

The second-q projected-RHS state is the same physical PDE right-hand side as
the already-closed fourth-q projected-RHS state.

Consequently:

* second-q raw `L²` escape gives H³-energy escape;
* second-q raw `L¹` escape gives energy or an existing higher-radial branch;
* second-q `M₆` escape forces, after cofinal extraction, either fourth-q raw
  `L¹` escape or fourth-q `M₁₀` escape, and both are already closed.

No projected-RHS primitive remains specific to the second-q branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

/-- Second-q projected-RHS raw `L²` escape is absorbed by physical H³ energy. -/
theorem velocityH3EnergyAt_tendstoAtTop_of_h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hRawTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        velocityH3EnergyAt u (τ n))
      atTop atTop := by

  have hEq :
      (fun n : ℕ =>
        h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
          hH3 hClass (hτ n) j i)
        =
      (fun n : ℕ =>
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
          hH3 hClass (hτ n) j i) := by
    funext n
    exact
      h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt_eq_fourthQ
        hH3 hClass (hτ n) j j i

  rw [hEq] at hRawTop

  exact
    velocityH3EnergyAt_tendstoAtTop_of_h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt_tendstoAtTop
      hH3 hClass j i τ hτ hRawTop

/--
Second-q projected-RHS raw `L¹` escape is exactly a fourth-q raw `L¹` escape,
hence resolves to physical energy or an existing higher-radial branch.
-/
theorem h3TerminalSecondQProjectedRHSRawL1_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hRawTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  have hEq :
      (fun n : ℕ =>
        h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
          hH3 hClass (hτ n) j i)
        =
      (fun n : ℕ =>
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
          hH3 hClass (hτ n) j i) := by
    funext n
    exact
      h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt_eq_fourthQ
        hH3 hClass (hτ n) j j i

  rw [hEq] at hRawTop

  exact
    h3TerminalFourthQProjectedRHSRawL1_escape_energy_or_fixedExtendedHigherRadial
      hH3 hClass j i τ hτ hTauTendsto hRawTop

/-! ## M6 resolves to fourth-q raw L1 or M10 -/

theorem h3TerminalSecondQProjectedRHSMoment6ResolverMax_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        max
          (h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
            hH3 hClass (hτ n) j i)
          (h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i))
      atTop atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ := max M 0

  have hMLe : M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        2 * R + 1
          <
        h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
          hH3 hClass (hτ n) j i :=
    hMomentTop.eventually
      (eventually_gt_atTop (2 * R + 1))

  filter_upwards [hLarge] with n hn

  let A : ℝ :=
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
      hH3 hClass (hτ n) j i

  let B : ℝ :=
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
      hH3 hClass (hτ n) j i

  let H : ℝ := max A B

  have hAH : A ≤ H := by
    dsimp only [H]
    exact le_max_left A B

  have hBH : B ≤ H := by
    dsimp only [H]
    exact le_max_right A B

  have hBound :=
    h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt_le_fourthQ_rawL1_add_moment10
      hH3 hClass (hτ n) j j i

  have hRLtH : R < H := by
    by_contra hNot

    have hHLe : H ≤ R :=
      le_of_not_gt hNot

    have hALe : A ≤ R :=
      hAH.trans hHLe

    have hBLe : B ≤ R :=
      hBH.trans hHLe

    have hSum : A + B ≤ 2 * R := by
      linarith

    have hMomentLe :
        h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
            hH3 hClass (hτ n) j i
          ≤
        2 * R := by
      dsimp only [A, B] at hBound hSum
      exact hBound.trans hSum

    linarith

  change
    M ≤
      max
        (h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
          hH3 hClass (hτ n) j i)
        (h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
          hH3 hClass (hτ n) j i)

  exact
    hMLe.trans
      (le_of_lt hRLtH)

noncomputable def h3TerminalSecondQProjectedRHSMoment6ResolverAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
      hH3 hClass ht j i
  else
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
      hH3 hClass ht j i

theorem exists_fixed_h3TerminalSecondQProjectedRHSMoment6Resolver_subsequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQProjectedRHSMoment6ResolverAt
              hH3 hClass (hτ (s n)) j i q)
          atTop atTop := by

  classical

  have hMaxTop :=
    h3TerminalSecondQProjectedRHSMoment6ResolverMax_tendstoAtTop
      hH3 hClass j i τ hτ hMomentTop

  let q : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i
          ≤
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
          hH3 hClass (hτ n) j i
      then 0
      else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalSecondQProjectedRHSMoment6ResolverAt
            hH3 hClass (hτ n) j i (q n)
          =
        max
          (h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
            hH3 hClass (hτ n) j i)
          (h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i) := by

    intro n
    dsimp only [q]

    by_cases h :
        h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i
          ≤
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
          hH3 hClass (hτ n) j i

    · simp only [if_pos h]
      unfold h3TerminalSecondQProjectedRHSMoment6ResolverAt
      simp only [if_pos]
      exact (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
              hH3 hClass (hτ n) j i
            ≤
          h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
            hH3 hClass (hτ n) j i :=
        le_of_lt (lt_of_not_ge h)

      unfold h3TerminalSecondQProjectedRHSMoment6ResolverAt
      simp only [if_neg, one_ne_zero]
      exact (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQProjectedRHSMoment6ResolverAt
            hH3 hClass (hτ n) j i (q n))
        atTop atTop := by
    simpa only [hChosen] using hMaxTop

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2,
          q n = q0 :=
    Frequently.of_forall
      (fun n => ⟨q n, rfl⟩)

  obtain ⟨q0, hFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySome

  obtain ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop hFrequently

  have hs :
      ∀ n : ℕ, n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop :
      Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop (𝓝 T) :=
    hTauTendsto.comp hsTop

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQProjectedRHSMoment6ResolverAt
            hH3 hClass (hτ (s n)) j i (q (s n)))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQProjectedRHSMoment6ResolverAt
            hH3 hClass (hτ (s n)) j i q0)
        atTop atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauSub, hTop⟩

/--
Second-q projected-RHS order-six moment escape is fully absorbed by the
already-closed fourth-q projected-RHS branches.
-/
theorem h3TerminalSecondQProjectedRHSMoment6_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMomentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  obtain
    ⟨q, s, hs, hsTop, hTauSub, hResolverTop⟩ :=
    exists_fixed_h3TerminalSecondQProjectedRHSMoment6Resolver_subsequence
      hH3 hClass j i τ hτ hTauTendsto hMomentTop

  fin_cases q

  · have hRawL1Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
              hH3 hClass (hτ (s n)) j i)
          atTop atTop := by
      simpa [
        h3TerminalSecondQProjectedRHSMoment6ResolverAt
      ] using hResolverTop

    rcases
      h3TerminalFourthQProjectedRHSRawL1_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass j i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        hRawL1Top
    with hEnergy | hHigher

    · rcases hEnergy with
        ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩

      have hComp :
          ∀ n : ℕ, n ≤ s (v n) := by
        intro n
        exact le_trans (hv n) (hs (v n))

      have hCompTop :
          Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
        hsTop.comp hvTop

      exact
        Or.inl
          ⟨
            (fun n : ℕ => s (v n)),
            hComp,
            hCompTop,
            hTauFinal,
            hEnergyTop
          ⟩

    · rcases hHigher with
        ⟨m, hm, v, hv, hvTop, hTauFinal, hHigherTop⟩

      have hComp :
          ∀ n : ℕ, n ≤ s (v n) := by
        intro n
        exact le_trans (hv n) (hs (v n))

      have hCompTop :
          Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
        hsTop.comp hvTop

      exact
        Or.inr
          ⟨
            m,
            hm,
            (fun n : ℕ => s (v n)),
            hComp,
            hCompTop,
            hTauFinal,
            hHigherTop
          ⟩

  · have hMoment10Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
              hH3 hClass (hτ (s n)) j i)
          atTop atTop := by
      simpa [
        h3TerminalSecondQProjectedRHSMoment6ResolverAt
      ] using hResolverTop

    rcases
      h3TerminalFourthQProjectedRHSMoment10_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass j i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        hMoment10Top
    with hEnergy | hHigher

    · rcases hEnergy with
        ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩

      have hComp :
          ∀ n : ℕ, n ≤ s (v n) := by
        intro n
        exact le_trans (hv n) (hs (v n))

      have hCompTop :
          Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
        hsTop.comp hvTop

      exact
        Or.inl
          ⟨
            (fun n : ℕ => s (v n)),
            hComp,
            hCompTop,
            hTauFinal,
            hEnergyTop
          ⟩

    · rcases hHigher with
        ⟨m, hm, v, hv, hvTop, hTauFinal, hHigherTop⟩

      have hComp :
          ∀ n : ℕ, n ≤ s (v n) := by
        intro n
        exact le_trans (hv n) (hs (v n))

      have hCompTop :
          Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
        hsTop.comp hvTop

      exact
        Or.inr
          ⟨
            m,
            hm,
            (fun n : ℕ => s (v n)),
            hComp,
            hCompTop,
            hTauFinal,
            hHigherTop
          ⟩

end

end Euclidean
end Bridge
end PrimeTensor
