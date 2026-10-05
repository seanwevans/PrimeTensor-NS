import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Split the frozen third-q Young envelope into two terminal state-mass groups

The preceding checkpoint bounds the frozen order-seven radial convolution by
an explicit Young state-mass envelope.  That envelope is the product of two
nonnegative groups:

* the product of the two raw Fourier `L²` norms;
* the order-fourteen moment / raw-`L¹` Young mixture.

If their product tends to `+∞`, the maximum of the two groups tends to `+∞`.
A finite extraction then freezes one of the two groups on a cofinal
subsequence, preserving convergence of the selected times to the terminal
time.

This is an algebraic finite-channel reduction only.  No new analytic estimate
is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalThirdQForcingStateMassGroup
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQForcingStateMassGroup :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The raw-Fourier `L²` product appearing in the fixed-pair Young envelope.
-/
noncomputable def h3TerminalForcingThirdQRawL2ProductAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ‖h3SpectralScalarRawFourierConjL2 (U k)‖ *
    ‖h3SpectralScalarRawFourierL2 (U l)‖

/--
The order-fourteen moment / raw-`L¹` Young mixture appearing in the fixed-pair
state-mass envelope.
-/
noncomputable def h3TerminalForcingThirdQMomentL1MixAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  h3FourierMomentSplitCoefficient (14 : ℝ)
    *
  (
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U k)
      *
    h3SpectralScalarRawFourierL1Mass (U l)
    +
    h3SpectralScalarRawFourierL1Mass (U k)
      *
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U l)
  )

theorem h3TerminalForcingThirdQRawL2ProductAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    0 ≤
      h3TerminalForcingThirdQRawL2ProductAt
        hH3 hClass ht k l := by

  unfold h3TerminalForcingThirdQRawL2ProductAt
  dsimp only
  positivity

theorem h3TerminalForcingThirdQMomentL1MixAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    0 ≤
      h3TerminalForcingThirdQMomentL1MixAt
        hH3 hClass ht k l := by

  unfold h3TerminalForcingThirdQMomentL1MixAt
  dsimp only

  apply mul_nonneg
  · exact h3FourierMomentSplitCoefficient_nonneg (14 : ℝ)

  apply add_nonneg
  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (14 : ℝ) _)
        (h3SpectralScalarRawFourierL1Mass_nonneg _)
  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierL1Mass_nonneg _)
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (14 : ℝ) _)

/--
The fixed-pair Young state-mass envelope is exactly the product of the two
named nonnegative state-mass groups.
-/
theorem h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt_eq_groups
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
        hH3 hClass ht k l
      =
    h3TerminalForcingThirdQRawL2ProductAt
        hH3 hClass ht k l
      *
    h3TerminalForcingThirdQMomentL1MixAt
        hH3 hClass ht k l := by
  rfl

/--
The two state-mass groups are packaged as a finite channel.  Channel `0` is
the raw-`L²` product and channel `1` is the moment/`L¹` Young mixture.
-/
noncomputable def h3TerminalForcingThirdQStateMassGroupAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalForcingThirdQRawL2ProductAt
      hH3 hClass ht k l
  else
    h3TerminalForcingThirdQMomentL1MixAt
      hH3 hClass ht k l

theorem h3TerminalForcingThirdQStateMassGroupAt_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQStateMassGroupAt
        hH3 hClass ht k l 0
      =
    h3TerminalForcingThirdQRawL2ProductAt
      hH3 hClass ht k l := by
  simp [h3TerminalForcingThirdQStateMassGroupAt]

theorem h3TerminalForcingThirdQStateMassGroupAt_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQStateMassGroupAt
        hH3 hClass ht k l 1
      =
    h3TerminalForcingThirdQMomentL1MixAt
      hH3 hClass ht k l := by
  simp [h3TerminalForcingThirdQStateMassGroupAt]

/--
Escape of the fixed-pair state-mass envelope forces escape of the maximum of
its two nonnegative groups.
-/
theorem h3TerminalForcingThirdQStateMassGroupMax_tendstoAtTop_of_envelope_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hEnvelopeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
              hH3 hClass (hτ n) k l
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          max
            (
              h3TerminalForcingThirdQRawL2ProductAt
                hH3 hClass (hτ n) k l
            )
            (
              h3TerminalForcingThirdQMomentL1MixAt
                hH3 hClass (hτ n) k l
            )
      )
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ :=
    max M 0

  have hRNonneg :
      0 ≤ R := by
    dsimp only [R]
    exact le_max_right M 0

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R ^ 2
          <
        h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
          hH3 hClass (hτ n) k l :=
    hEnvelopeTop.eventually
      (eventually_gt_atTop (R ^ 2))

  filter_upwards [hLarge] with n hn

  let A : ℝ :=
    h3TerminalForcingThirdQRawL2ProductAt
      hH3 hClass (hτ n) k l

  let B : ℝ :=
    h3TerminalForcingThirdQMomentL1MixAt
      hH3 hClass (hτ n) k l

  let H : ℝ :=
    max A B

  have hA0 :
      0 ≤ A := by
    dsimp only [A]
    exact
      h3TerminalForcingThirdQRawL2ProductAt_nonneg
        hH3 hClass (hτ n) k l

  have hB0 :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3TerminalForcingThirdQMomentL1MixAt_nonneg
        hH3 hClass (hτ n) k l

  have hAH :
      A ≤ H := by
    dsimp only [H]
    exact le_max_left A B

  have hBH :
      B ≤ H := by
    dsimp only [H]
    exact le_max_right A B

  have hH0 :
      0 ≤ H :=
    hA0.trans hAH

  have hABLe :
      A * B ≤ H ^ 2 := by
    have hFirst :
        A * B ≤ H * B :=
      mul_le_mul_of_nonneg_right hAH hB0
    have hSecond :
        H * B ≤ H * H :=
      mul_le_mul_of_nonneg_left hBH hH0
    calc
      A * B ≤ H * B := hFirst
      _ ≤ H * H := hSecond
      _ = H ^ 2 := by ring

  have hEnvelopeEq :
      h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
          hH3 hClass (hτ n) k l
        =
      A * B := by
    dsimp only [A, B]
    exact
      h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt_eq_groups
        hH3 hClass (hτ n) k l

  have hRSqLtHSq :
      R ^ 2 < H ^ 2 := by
    calc
      R ^ 2
          <
        h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
          hH3 hClass (hτ n) k l := hn
      _ = A * B := hEnvelopeEq
      _ ≤ H ^ 2 := hABLe

  have hRLtH :
      R < H := by
    nlinarith

  change
    M
      ≤
    max
      (
        h3TerminalForcingThirdQRawL2ProductAt
          hH3 hClass (hτ n) k l
      )
      (
        h3TerminalForcingThirdQMomentL1MixAt
          hH3 hClass (hτ n) k l
      )

  exact
    hMLe.trans
      (le_of_lt hRLtH)

/--
At every index one of the two finite state-mass groups realizes their maximum.
-/
theorem exists_h3TerminalForcingThirdQStateMassGroupAt_eq_max
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    ∃ q : Fin 2,
      h3TerminalForcingThirdQStateMassGroupAt
          hH3 hClass ht k l q
        =
      max
        (
          h3TerminalForcingThirdQRawL2ProductAt
            hH3 hClass ht k l
        )
        (
          h3TerminalForcingThirdQMomentL1MixAt
            hH3 hClass ht k l
        ) := by

  by_cases h :
      h3TerminalForcingThirdQMomentL1MixAt
          hH3 hClass ht k l
        ≤
      h3TerminalForcingThirdQRawL2ProductAt
        hH3 hClass ht k l

  · refine ⟨0, ?_⟩
    rw [
      h3TerminalForcingThirdQStateMassGroupAt_zero,
      max_eq_left h
    ]

  · have hReverse :
        h3TerminalForcingThirdQRawL2ProductAt
            hH3 hClass ht k l
          ≤
        h3TerminalForcingThirdQMomentL1MixAt
          hH3 hClass ht k l :=
      le_of_not_ge h

    refine ⟨1, ?_⟩
    rw [
      h3TerminalForcingThirdQStateMassGroupAt_one,
      max_eq_right hReverse
    ]

/--
Escape of the fixed-pair Young envelope admits a cofinal subsequence on which
one fixed state-mass group diverges.
-/
theorem exists_fixed_h3TerminalForcingThirdQStateMassGroup_subsequence_of_envelope_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hEnvelopeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
              hH3 hClass (hτ n) k l
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
              h3TerminalForcingThirdQStateMassGroupAt
                hH3 hClass (hτ (s n)) k l q
          )
          atTop
          atTop := by

  classical

  have hMaxTop :=
    h3TerminalForcingThirdQStateMassGroupMax_tendstoAtTop_of_envelope_tendstoAtTop
      hH3 hClass k l τ hτ hEnvelopeTop

  have hChoice :
      ∀ n : ℕ,
        ∃ q : Fin 2,
          h3TerminalForcingThirdQStateMassGroupAt
              hH3 hClass (hτ n) k l q
            =
          max
            (
              h3TerminalForcingThirdQRawL2ProductAt
                hH3 hClass (hτ n) k l
            )
            (
              h3TerminalForcingThirdQMomentL1MixAt
                hH3 hClass (hτ n) k l
            ) := by
    intro n
    exact
      exists_h3TerminalForcingThirdQStateMassGroupAt_eq_max
        hH3 hClass (hτ n) k l

  choose q hq using hChoice

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQStateMassGroupAt
              hH3 hClass (hτ n) k l (q n)
        )
        atTop
        atTop := by
    simpa only [hq] using hMaxTop

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2,
          q n = q0 :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            q n,
            rfl
          ⟩
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

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp
      hsTop

  have hGroupTopBeforeRewrite :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQStateMassGroupAt
              hH3 hClass (hτ (s n)) k l (q (s n))
        )
        atTop
        atTop :=
    hChosenTop.comp
      hsTop

  have hGroupTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQStateMassGroupAt
              hH3 hClass (hτ (s n)) k l q0
        )
        atTop
        atTop := by
    simpa only [hFixed] using
      hGroupTopBeforeRewrite

  exact
    ⟨
      q0,
      s,
      hs,
      hsTop,
      hTauSub,
      hGroupTop
    ⟩

/--
The sixth-diffusion frontier now reduces to either the existing shift-four
higher-radial velocity moment or one fixed Young state-mass group (`L²`
product versus moment/`L¹` mixture) on a cofinal terminal subsequence.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingStateMassGroup
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
                  h3TerminalForcingThirdQStateMassGroupAt
                    hH3 hClass (hτ (s n)) k l q
              )
              atTop
              atTop
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingStateMassEnvelope
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigher
    |
    hEnvelope

  · exact
      Or.inl hHigher

  · rcases hEnvelope with
      ⟨k, l, s, hs, hsTop, hTauSub, hEnvelopeTop⟩

    obtain
      ⟨q, r, hr, hrTop, hTauSubSub, hGroupTop⟩ :=
      exists_fixed_h3TerminalForcingThirdQStateMassGroup_subsequence_of_envelope_tendstoAtTop
        hH3 hClass k l
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        hEnvelopeTop

    have hComp :
        ∀ n : ℕ,
          n ≤ s (r n) := by
      intro n
      exact
        le_trans
          (hr n)
          (hs (r n))

    have hCompTop :
        Tendsto
          (fun n : ℕ => s (r n))
          atTop
          atTop :=
      hsTop.comp
        hrTop

    exact
      Or.inr
        ⟨
          k,
          l,
          q,
          (fun n : ℕ => s (r n)),
          hComp,
          hCompTop,
          hTauSubSub,
          hGroupTop
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
