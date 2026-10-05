import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Primitive terminal mass factor for the third-q forcing branch

The preceding checkpoint leaves one nontrivial Young product

    M14(k) * L1(l)

or

    L1(k) * M14(l).

This file resolves that final product into one primitive nonnegative factor on
a cofinal subsequence.  The surviving primitive factor is therefore either an
order-fourteen raw Fourier moment mass or an unweighted raw Fourier `L¹` mass.

The raw-`L²` alternative from the preceding checkpoint is already primitive and
is carried forward unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalThirdQForcingPrimitiveMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQForcingPrimitiveMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic two-factor extraction -/

private theorem primitive_max_tendstoAtTop_of_mul_tendstoAtTop
    (A B : ℕ → ℝ)
    (hA : ∀ n : ℕ, 0 ≤ A n)
    (hB : ∀ n : ℕ, 0 ≤ B n)
    (hProduct :
      Tendsto
        (fun n : ℕ => A n * B n)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ => max (A n) (B n))
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ :=
    max M 0

  have hR0 :
      0 ≤ R := by
    dsimp only [R]
    exact le_max_right M 0

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R ^ 2 < A n * B n :=
    hProduct.eventually
      (eventually_gt_atTop (R ^ 2))

  filter_upwards [hLarge] with n hn

  let H : ℝ :=
    max (A n) (B n)

  have hAH :
      A n ≤ H := by
    dsimp only [H]
    exact le_max_left _ _

  have hBH :
      B n ≤ H := by
    dsimp only [H]
    exact le_max_right _ _

  have hH0 :
      0 ≤ H :=
    (hA n).trans hAH

  have hProductLe :
      A n * B n ≤ H ^ 2 := by

    have hFirst :
        A n * B n ≤ H * B n :=
      mul_le_mul_of_nonneg_right
        hAH
        (hB n)

    have hSecond :
        H * B n ≤ H * H :=
      mul_le_mul_of_nonneg_left
        hBH
        hH0

    calc
      A n * B n ≤ H * B n := hFirst
      _ ≤ H * H := hSecond
      _ = H ^ 2 := by ring

  have hRSqLt :
      R ^ 2 < H ^ 2 :=
    lt_of_lt_of_le
      hn
      hProductLe

  have hRLt :
      R < H := by
    nlinarith

  change M ≤ max (A n) (B n)

  exact
    hMLe.trans
      (le_of_lt hRLt)

private theorem exists_fixed_primitive_fin2_subsequence_of_max_tendstoAtTop
    (F : Fin 2 → ℕ → ℝ)
    (hMax :
      Tendsto
        (fun n : ℕ => max (F 0 n) (F 1 n))
        atTop
        atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => F q (s n))
          atTop
          atTop := by

  classical

  let q : ℕ → Fin 2 :=
    fun n =>
      if F 1 n ≤ F 0 n then
        0
      else
        1

  have hChosen :
      ∀ n : ℕ,
        F (q n) n
          =
        max (F 0 n) (F 1 n) := by

    intro n

    dsimp only [q]

    by_cases h :
        F 1 n ≤ F 0 n

    · simp only [if_pos h]
      exact
        (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          F 0 n ≤ F 1 n :=
        le_of_lt
          (lt_of_not_ge h)

      exact
        (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (fun n : ℕ => F (q n) n)
        atTop
        atTop := by
    simpa only [hChosen] using
      hMax

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2,
          q n = q0 :=
    Frequently.of_forall
      (
        fun n =>
          ⟨q n, rfl⟩
      )

  obtain
    ⟨q0, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hs :
      ∀ n : ℕ,
        n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop :
      Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ => F (q (s n)) (s n))
        atTop
        atTop :=
    hChosenTop.comp
      hsTop

  have hTop :
      Tendsto
        (fun n : ℕ => F q0 (s n))
        atTop
        atTop := by
    simpa only [hFixed] using
      hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTop⟩

/-! ## Primitive factors of the frozen moment/L¹ product -/

/--
Primitive factors of a frozen order-fourteen-moment/raw-`L¹` Young product.

For product channel `r = 0`:
* primitive `0` is `M14(k)`;
* primitive `1` is `L1(l)`.

For product channel `r = 1`:
* primitive `0` is `L1(k)`;
* primitive `1` is `M14(l)`.
-/
noncomputable def h3TerminalForcingThirdQMomentL1PrimitiveAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (r q : Fin 2) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  if r = 0 then
    if q = 0 then
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U k)
    else
      h3SpectralScalarRawFourierL1Mass (U l)
  else
    if q = 0 then
      h3SpectralScalarRawFourierL1Mass (U k)
    else
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U l)

theorem h3TerminalForcingThirdQMomentL1PrimitiveAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (r q : Fin 2) :
    0 ≤
      h3TerminalForcingThirdQMomentL1PrimitiveAt
        hH3 hClass ht k l r q := by

  unfold h3TerminalForcingThirdQMomentL1PrimitiveAt
  dsimp only

  by_cases hr : r = 0
  · simp only [if_pos hr]
    by_cases hq : q = 0
    · simp only [if_pos hq]
      exact
        h3SpectralScalarRawFourierMomentMass_nonneg
          (14 : ℝ) _
    · simp only [if_neg hq]
      exact
        h3SpectralScalarRawFourierL1Mass_nonneg _
  · simp only [if_neg hr]
    by_cases hq : q = 0
    · simp only [if_pos hq]
      exact
        h3SpectralScalarRawFourierL1Mass_nonneg _
    · simp only [if_neg hq]
      exact
        h3SpectralScalarRawFourierMomentMass_nonneg
          (14 : ℝ) _

/--
Each frozen Young product is exactly the product of its two primitive factors.
-/
theorem h3TerminalForcingThirdQMomentL1ProductAt_eq_primitives
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (r : Fin 2) :
    h3TerminalForcingThirdQMomentL1ProductAt
        hH3 hClass ht k l r
      =
    h3TerminalForcingThirdQMomentL1PrimitiveAt
        hH3 hClass ht k l r 0
      *
    h3TerminalForcingThirdQMomentL1PrimitiveAt
        hH3 hClass ht k l r 1 := by

  fin_cases r <;>
    simp [
      h3TerminalForcingThirdQMomentL1ProductAt,
      h3TerminalForcingThirdQMomentL1PrimitiveAt
    ]

/--
Escape of one frozen moment/`L¹` product admits a cofinal subsequence on which
one fixed primitive mass diverges.
-/
theorem exists_fixed_h3TerminalForcingThirdQMomentL1Primitive_subsequence_of_product_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (r : Fin 2)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hProductTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMomentL1ProductAt
              hH3 hClass (hτ n) k l r
        )
        atTop
        atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQMomentL1PrimitiveAt
                hH3 hClass (hτ (s n)) k l r q
          )
          atTop
          atTop := by

  have hPrimitiveProductTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMomentL1PrimitiveAt
                hH3 hClass (hτ n) k l r 0
              *
            h3TerminalForcingThirdQMomentL1PrimitiveAt
              hH3 hClass (hτ n) k l r 1
        )
        atTop
        atTop := by
    simpa only [
      ← h3TerminalForcingThirdQMomentL1ProductAt_eq_primitives
    ] using hProductTop

  have hMaxTop :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                h3TerminalForcingThirdQMomentL1PrimitiveAt
                  hH3 hClass (hτ n) k l r 0
              )
              (
                h3TerminalForcingThirdQMomentL1PrimitiveAt
                  hH3 hClass (hτ n) k l r 1
              )
        )
        atTop
        atTop :=
    primitive_max_tendstoAtTop_of_mul_tendstoAtTop
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQMomentL1PrimitiveAt
            hH3 hClass (hτ n) k l r 0
      )
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQMomentL1PrimitiveAt
            hH3 hClass (hτ n) k l r 1
      )
      (
        fun n =>
          h3TerminalForcingThirdQMomentL1PrimitiveAt_nonneg
            hH3 hClass (hτ n) k l r 0
      )
      (
        fun n =>
          h3TerminalForcingThirdQMomentL1PrimitiveAt_nonneg
            hH3 hClass (hτ n) k l r 1
      )
      hPrimitiveProductTop

  obtain
    ⟨q, s, hs, hsTop, hPrimitiveTop⟩ :=
    exists_fixed_primitive_fin2_subsequence_of_max_tendstoAtTop
      (
        fun q n =>
          h3TerminalForcingThirdQMomentL1PrimitiveAt
            hH3 hClass (hτ n) k l r q
      )
      hMaxTop

  exact
    ⟨
      q,
      s,
      hs,
      hsTop,
      hTauTendsto.comp hsTop,
      hPrimitiveTop
    ⟩

/--
The sixth-diffusion frontier now has only primitive forcing-mass alternatives:
a fixed raw-`L²` factor or a fixed order-fourteen moment/raw-`L¹` primitive.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingPrimitiveMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hSixth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
              (τ n)
        )
        atTop
        atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass 4
                (τ (s n))
                (hτ (s n))
          )
          atTop
          (𝓝 ∞)
    )
      ∨
    (
      ∃ k l : Fin 3,
        (
          (
            ∃ r : Fin 2,
              ∃ s : ℕ → ℕ,
                (∀ n : ℕ, n ≤ s n)
                  ∧
                Tendsto s atTop atTop
                  ∧
                Tendsto
                  (fun n : ℕ => τ (s n))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      h3TerminalForcingThirdQRawL2FactorAt
                        hH3 hClass (hτ (s n)) k l r
                  )
                  atTop
                  atTop
          )
            ∨
          (
            ∃ r q : Fin 2,
              ∃ s : ℕ → ℕ,
                (∀ n : ℕ, n ≤ s n)
                  ∧
                Tendsto s atTop atTop
                  ∧
                Tendsto
                  (fun n : ℕ => τ (s n))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      h3TerminalForcingThirdQMomentL1PrimitiveAt
                        hH3 hClass (hτ (s n)) k l r q
                  )
                  atTop
                  atTop
          )
        )
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingStateMassFactor
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigher
    |
    hFactor

  · exact
      Or.inl hHigher

  · rcases hFactor with
      ⟨k, l, hRaw | hMomentL1⟩

    · exact
        Or.inr
          ⟨k, l, Or.inl hRaw⟩

    · rcases hMomentL1 with
        ⟨r, s, hs, hsTop, hTauSub, hProductTop⟩

      obtain
        ⟨q, v, hv, hvTop, hTauFinal, hPrimitiveTop⟩ :=
        exists_fixed_h3TerminalForcingThirdQMomentL1Primitive_subsequence_of_product_tendstoAtTop
          hH3 hClass k l r
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hTauSub
          hProductTop

      have hComp :
          ∀ n : ℕ,
            n ≤ s (v n) := by
        intro n
        exact
          le_trans
            (hv n)
            (hs (v n))

      have hCompTop :
          Tendsto
            (fun n : ℕ => s (v n))
            atTop
            atTop :=
        hsTop.comp hvTop

      exact
        Or.inr
          ⟨
            k,
            l,
            Or.inr
              ⟨
                r,
                q,
                (fun n : ℕ => s (v n)),
                hComp,
                hCompTop,
                hTauFinal,
                hPrimitiveTop
              ⟩
          ⟩

end

end Euclidean
end Bridge
end PrimeTensor
