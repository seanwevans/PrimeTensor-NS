import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.ProjectedRHSClosure
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Freeze one primitive from the second-q Young state-mass envelope

For one frozen second-q order-three convolution channel, the Young envelope is

    (L2(F) * L2(G))
      *
    (C6 * (M6(F) * L1(G) + L1(F) * M6(G))).

There are therefore only six nonnegative primitive masses:

1. `L2(F)`,
2. `L2(G)`,
3. `M6(F)`,
4. `L1(G)`,
5. `L1(F)`,
6. `M6(G)`.

Instead of reproducing the deeper fourth-q group/product hierarchy, this file
takes the maximum of those six primitives directly.  The full state-mass
envelope is bounded by a fixed coefficient times the fourth power of that
maximum.  Hence envelope escape freezes one primitive on a cofinal subsequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

/-- One of the six primitive masses in the second-q Young envelope. -/
noncomputable def h3TerminalSecondQForcingDerivativePrimitiveFactorAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 6) : ℝ :=
  let F :=
    h3TerminalSecondQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k
  let G :=
    h3TerminalSecondQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l
  ![
    ‖h3SpectralScalarRawFourierConjL2 F‖,
    ‖h3SpectralScalarRawFourierL2 G‖,
    h3SpectralScalarRawFourierMomentMass (6 : ℝ) F,
    h3SpectralScalarRawFourierL1Mass G,
    h3SpectralScalarRawFourierL1Mass F,
    h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
  ] q

theorem h3TerminalSecondQForcingDerivativePrimitiveFactorAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 6) :
    0 ≤
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
        hH3 hClass ht j o k l q := by

  fin_cases q <;>
    simp [
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt,
      h3SpectralScalarRawFourierMomentMass_nonneg,
      h3SpectralScalarRawFourierL1Mass_nonneg
    ]

/--
At each strict time, the complete second-q Young envelope is bounded by a fixed
coefficient times the fourth power of one maximizing primitive mass.
-/
theorem exists_primitive_h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    ∃ q : Fin 6,
      h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
          hH3 hClass ht j o k l
        ≤
      (
        2 * h3FourierMomentSplitCoefficient (6 : ℝ)
      )
        *
      (
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt
          hH3 hClass ht j o k l q
      ) ^ 4 := by

  classical

  let f : Fin 6 → ℝ :=
    fun q =>
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
        hH3 hClass ht j o k l q

  have hUnivNonempty :
      (Finset.univ : Finset (Fin 6)).Nonempty :=
    ⟨0, Finset.mem_univ _⟩

  obtain ⟨q, _hqMem, hqMax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin 6))
      f
      hUnivNonempty

  let F :=
    h3TerminalSecondQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k

  let G :=
    h3TerminalSecondQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l

  let H : ℝ := f q

  have hH0 :
      0 ≤ H := by
    dsimp only [H, f]
    exact
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt_nonneg
        hH3 hClass ht j o k l q

  have hL2F :
      ‖h3SpectralScalarRawFourierConjL2 F‖ ≤ H := by
    have h :=
      hqMax 0 (Finset.mem_univ _)
    simpa [
      H,
      f,
      F,
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
    ] using h

  have hL2G :
      ‖h3SpectralScalarRawFourierL2 G‖ ≤ H := by
    have h :=
      hqMax 1 (Finset.mem_univ _)
    simpa [
      H,
      f,
      G,
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
    ] using h

  have hM6F :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) F ≤ H := by
    have h :=
      hqMax 2 (Finset.mem_univ _)
    simpa [
      H,
      f,
      F,
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
    ] using h

  have hL1G :
      h3SpectralScalarRawFourierL1Mass G ≤ H := by
    have h :=
      hqMax 3 (Finset.mem_univ _)
    simpa [
      H,
      f,
      G,
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
    ] using h

  have hL1F :
      h3SpectralScalarRawFourierL1Mass F ≤ H := by
    have h :=
      hqMax 4 (Finset.mem_univ _)
    simpa [
      H,
      f,
      F,
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
    ] using h

  have hM6G :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) G ≤ H := by
    have h :=
      hqMax 5 (Finset.mem_univ _)
    simpa [
      H,
      f,
      G,
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
    ] using h

  have hL2F0 :
      0 ≤ ‖h3SpectralScalarRawFourierConjL2 F‖ :=
    norm_nonneg _

  have hL2G0 :
      0 ≤ ‖h3SpectralScalarRawFourierL2 G‖ :=
    norm_nonneg _

  have hM6F0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (6 : ℝ) F :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hM6G0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (6 : ℝ) G :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hL1F0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass F :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hL1G0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass G :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hC0 :
      0 ≤ h3FourierMomentSplitCoefficient (6 : ℝ) :=
    h3FourierMomentSplitCoefficient_nonneg (6 : ℝ)

  have hL2Product :
      ‖h3SpectralScalarRawFourierConjL2 F‖
          *
        ‖h3SpectralScalarRawFourierL2 G‖
        ≤
      H ^ 2 := by

    have hMul :
        ‖h3SpectralScalarRawFourierConjL2 F‖
            *
          ‖h3SpectralScalarRawFourierL2 G‖
          ≤
        H * H :=
      mul_le_mul
        hL2F
        hL2G
        hL2G0
        hH0

    simpa [pow_two] using hMul

  have hFirstMomentProduct :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) F
          *
        h3SpectralScalarRawFourierL1Mass G
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) F
            *
          h3SpectralScalarRawFourierL1Mass G
          ≤
        H * H :=
      mul_le_mul
        hM6F
        hL1G
        hL1G0
        hH0

    simpa [pow_two] using hMul

  have hSecondMomentProduct :
      h3SpectralScalarRawFourierL1Mass F
          *
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierL1Mass F
            *
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
          ≤
        H * H :=
      mul_le_mul
        hL1F
        hM6G
        hM6G0
        hH0

    simpa [pow_two] using hMul

  have hMomentSum :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) F
            *
          h3SpectralScalarRawFourierL1Mass G
        +
      h3SpectralScalarRawFourierL1Mass F
            *
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
        ≤
      2 * H ^ 2 := by
    linarith

  have hWeightedMoment :
      h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) F
              *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
        )
        ≤
      h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left
      hMomentSum
      hC0

  have hWeightedMoment0 :
      0 ≤
        h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) F
              *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
        ) := by

    apply mul_nonneg hC0
    exact
      add_nonneg
        (mul_nonneg hM6F0 hL1G0)
        (mul_nonneg hL1F0 hM6G0)

  have hEnvelope :
      h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
          hH3 hClass ht j o k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (2 * H ^ 2)
      ) := by

    unfold h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
    dsimp only [F, G]

    exact
      mul_le_mul
        hL2Product
        hWeightedMoment
        hWeightedMoment0
        (sq_nonneg H)

  refine ⟨q, ?_⟩

  calc
    h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
        hH3 hClass ht j o k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (6 : ℝ)
          *
        (2 * H ^ 2)
      ) :=
      hEnvelope
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (6 : ℝ)
      ) * H ^ 4 := by
      ring
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (6 : ℝ)
      )
        *
      (
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt
          hH3 hClass ht j o k l q
      ) ^ 4 := by
      rfl

/--
Escape of a fixed second-q state-mass envelope freezes one of its six primitive
masses on a cofinal subsequence.
-/
theorem exists_fixed_h3TerminalSecondQForcingDerivativePrimitiveFactor_subsequence_of_stateMassEnvelope_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hEnvelopeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
            hH3 hClass (hτ n) j o k l)
        atTop atTop) :
    ∃ q : Fin 6,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalSecondQForcingDerivativePrimitiveFactorAt
              hH3 hClass (hτ (s n)) j o k l q)
          atTop atTop := by

  classical

  have hChoice :
      ∀ n : ℕ,
        ∃ q : Fin 6,
          h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
              hH3 hClass (hτ n) j o k l
            ≤
          (
            2 * h3FourierMomentSplitCoefficient (6 : ℝ)
          )
            *
          (
            h3TerminalSecondQForcingDerivativePrimitiveFactorAt
              hH3 hClass (hτ n) j o k l q
          ) ^ 4 := by
    intro n
    exact
      exists_primitive_h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four
        hH3 hClass (hτ n) j o k l

  choose q hq using hChoice

  let C : ℝ :=
    2 * h3FourierMomentSplitCoefficient (6 : ℝ)

  have hC0 :
      0 ≤ C := by
    dsimp only [C]
    exact
      mul_nonneg
        (by norm_num)
        (h3FourierMomentSplitCoefficient_nonneg (6 : ℝ))

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativePrimitiveFactorAt
            hH3 hClass (hτ n) j o k l (q n))
        atTop atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    let R : ℝ := max M 1

    have hMLe :
        M ≤ R := by
      dsimp only [R]
      exact le_max_left M 1

    have hR0 :
        0 ≤ R := by
      dsimp only [R]
      exact
        le_trans
          (by norm_num)
          (le_max_right M 1)

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          C * R ^ 4 + 1
            <
          h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
            hH3 hClass (hτ n) j o k l :=
      hEnvelopeTop.eventually
        (eventually_gt_atTop (C * R ^ 4 + 1))

    filter_upwards [hLarge] with n hn

    let P : ℝ :=
      h3TerminalSecondQForcingDerivativePrimitiveFactorAt
        hH3 hClass (hτ n) j o k l (q n)

    have hP0 :
        0 ≤ P := by
      dsimp only [P]
      exact
        h3TerminalSecondQForcingDerivativePrimitiveFactorAt_nonneg
          hH3 hClass (hτ n) j o k l (q n)

    have hBound :
        h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
            hH3 hClass (hτ n) j o k l
          ≤
        C * P ^ 4 := by
      dsimp only [C, P]
      exact hq n

    have hRLtP :
        R < P := by

      by_contra hNot

      have hPLe :
          P ≤ R :=
        le_of_not_gt hNot

      have hPowLe :
          P ^ 4 ≤ R ^ 4 :=
        pow_le_pow_left₀ hP0 hPLe 4

      have hScaled :
          C * P ^ 4 ≤ C * R ^ 4 :=
        mul_le_mul_of_nonneg_left
          hPowLe
          hC0

      have hEnvelopeLe :
          h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
              hH3 hClass (hτ n) j o k l
            ≤
          C * R ^ 4 :=
        hBound.trans hScaled

      linarith

    exact
      hMLe.trans
        (le_of_lt hRLtP)

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 6,
          q n = q0 :=
    Frequently.of_forall
      (fun n => ⟨q n, rfl⟩)

  obtain ⟨q0, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

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
          h3TerminalSecondQForcingDerivativePrimitiveFactorAt
            hH3 hClass (hτ (s n)) j o k l (q (s n)))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSecondQForcingDerivativePrimitiveFactorAt
            hH3 hClass (hτ (s n)) j o k l q0)
        atTop atTop := by
    simpa only [hFixed] using
      hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauSub, hTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
