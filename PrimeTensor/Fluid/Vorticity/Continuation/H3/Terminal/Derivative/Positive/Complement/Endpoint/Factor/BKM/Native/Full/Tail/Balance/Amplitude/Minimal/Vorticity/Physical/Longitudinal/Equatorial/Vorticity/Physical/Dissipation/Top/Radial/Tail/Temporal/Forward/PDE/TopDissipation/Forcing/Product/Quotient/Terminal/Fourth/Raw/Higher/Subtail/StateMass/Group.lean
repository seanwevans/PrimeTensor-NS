import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Split the fourth-q forcing derivative Young envelope into two mass groups

The frozen order-five product channel is controlled by the product of two
nonnegative groups:

* the raw Fourier `L²` product of its oriented scalar factors;
* the order-ten moment / raw-`L¹` Young mixture.

Escape of their product forces escape of their maximum.  Since there are only
two groups, a cofinal extraction freezes one group while preserving terminal
time convergence.

This is algebraic channel reduction only; no projected-RHS estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthQForcingDerivativeStateMassGroup
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingDerivativeStateMassGroup :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

/-- Raw-Fourier `L²` product of the two oriented scalar factors. -/
noncomputable def h3TerminalFourthQForcingDerivativeRawL2ProductAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) : ℝ :=
  let F :=
    h3TerminalFourthQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k
  let G :=
    h3TerminalFourthQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l
  ‖h3SpectralScalarRawFourierConjL2 F‖ *
    ‖h3SpectralScalarRawFourierL2 G‖

/-- Order-ten moment/raw-`L¹` Young mixture of the oriented scalar factors. -/
noncomputable def h3TerminalFourthQForcingDerivativeMomentL1MixAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) : ℝ :=
  let F :=
    h3TerminalFourthQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k
  let G :=
    h3TerminalFourthQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l
  h3FourierMomentSplitCoefficient (10 : ℝ)
    *
  (
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
      *
    h3SpectralScalarRawFourierL1Mass G
    +
    h3SpectralScalarRawFourierL1Mass F
      *
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
  )

theorem h3TerminalFourthQForcingDerivativeRawL2ProductAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    0 ≤
      h3TerminalFourthQForcingDerivativeRawL2ProductAt
        hH3 hClass ht j o k l := by
  unfold h3TerminalFourthQForcingDerivativeRawL2ProductAt
  dsimp only
  positivity

theorem h3TerminalFourthQForcingDerivativeMomentL1MixAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    0 ≤
      h3TerminalFourthQForcingDerivativeMomentL1MixAt
        hH3 hClass ht j o k l := by
  unfold h3TerminalFourthQForcingDerivativeMomentL1MixAt
  dsimp only

  apply mul_nonneg
  · exact h3FourierMomentSplitCoefficient_nonneg (10 : ℝ)

  apply add_nonneg
  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (10 : ℝ) _)
        (h3SpectralScalarRawFourierL1Mass_nonneg _)
  · exact
      mul_nonneg
        (h3SpectralScalarRawFourierL1Mass_nonneg _)
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (10 : ℝ) _)

/-- The explicit state-mass envelope is exactly the product of the two groups. -/
theorem h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt_eq_groups
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
        hH3 hClass ht j o k l
      =
    h3TerminalFourthQForcingDerivativeRawL2ProductAt
        hH3 hClass ht j o k l
      *
    h3TerminalFourthQForcingDerivativeMomentL1MixAt
        hH3 hClass ht j o k l := by
  rfl

/--
Two-channel packaging: `0` is the raw-`L²` product and `1` is the
moment/raw-`L¹` mixture.
-/
noncomputable def h3TerminalFourthQForcingDerivativeStateMassGroupAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalFourthQForcingDerivativeRawL2ProductAt
      hH3 hClass ht j o k l
  else
    h3TerminalFourthQForcingDerivativeMomentL1MixAt
      hH3 hClass ht j o k l

theorem h3TerminalFourthQForcingDerivativeStateMassGroupAt_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    h3TerminalFourthQForcingDerivativeStateMassGroupAt
        hH3 hClass ht j o k l 0
      =
    h3TerminalFourthQForcingDerivativeRawL2ProductAt
      hH3 hClass ht j o k l := by
  simp [h3TerminalFourthQForcingDerivativeStateMassGroupAt]

theorem h3TerminalFourthQForcingDerivativeStateMassGroupAt_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    h3TerminalFourthQForcingDerivativeStateMassGroupAt
        hH3 hClass ht j o k l 1
      =
    h3TerminalFourthQForcingDerivativeMomentL1MixAt
      hH3 hClass ht j o k l := by
  simp [h3TerminalFourthQForcingDerivativeStateMassGroupAt]

/-- Envelope escape forces escape of the maximum of its two nonnegative groups. -/
theorem h3TerminalFourthQForcingDerivativeStateMassGroupMax_tendstoAtTop_of_envelope_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hEnvelopeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
              hH3 hClass (hτ n) j o k l
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          max
            (
              h3TerminalFourthQForcingDerivativeRawL2ProductAt
                hH3 hClass (hτ n) j o k l
            )
            (
              h3TerminalFourthQForcingDerivativeMomentL1MixAt
                hH3 hClass (hτ n) j o k l
            )
      )
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_
  intro M

  let R0 : ℝ := max M 0

  have hR0Nonneg : 0 ≤ R0 := by
    dsimp only [R0]
    exact le_max_right M 0

  have hMLe : M ≤ R0 := by
    dsimp only [R0]
    exact le_max_left M 0

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R0 ^ 2
          <
        h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
          hH3 hClass (hτ n) j o k l :=
    hEnvelopeTop.eventually
      (eventually_gt_atTop (R0 ^ 2))

  filter_upwards [hLarge] with n hn

  let A : ℝ :=
    h3TerminalFourthQForcingDerivativeRawL2ProductAt
      hH3 hClass (hτ n) j o k l
  let B : ℝ :=
    h3TerminalFourthQForcingDerivativeMomentL1MixAt
      hH3 hClass (hτ n) j o k l
  let H : ℝ := max A B

  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact
      h3TerminalFourthQForcingDerivativeRawL2ProductAt_nonneg
        hH3 hClass (hτ n) j o k l

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact
      h3TerminalFourthQForcingDerivativeMomentL1MixAt_nonneg
        hH3 hClass (hτ n) j o k l

  have hAH : A ≤ H := by
    dsimp only [H]
    exact le_max_left A B

  have hBH : B ≤ H := by
    dsimp only [H]
    exact le_max_right A B

  have hH0 : 0 ≤ H :=
    hA0.trans hAH

  have hABLe : A * B ≤ H ^ 2 := by
    have hFirst : A * B ≤ H * B :=
      mul_le_mul_of_nonneg_right hAH hB0
    have hSecond : H * B ≤ H * H :=
      mul_le_mul_of_nonneg_left hBH hH0
    calc
      A * B ≤ H * B := hFirst
      _ ≤ H * H := hSecond
      _ = H ^ 2 := by ring

  have hEnvelopeEq :
      h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
          hH3 hClass (hτ n) j o k l
        =
      A * B := by
    dsimp only [A, B]
    exact
      h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt_eq_groups
        hH3 hClass (hτ n) j o k l

  have hR0SqLtHSq : R0 ^ 2 < H ^ 2 := by
    calc
      R0 ^ 2
          <
        h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
          hH3 hClass (hτ n) j o k l := hn
      _ = A * B := hEnvelopeEq
      _ ≤ H ^ 2 := hABLe

  have hR0LtH : R0 < H := by
    nlinarith

  change
    M ≤
      max
        (h3TerminalFourthQForcingDerivativeRawL2ProductAt
          hH3 hClass (hτ n) j o k l)
        (h3TerminalFourthQForcingDerivativeMomentL1MixAt
          hH3 hClass (hτ n) j o k l)

  exact hMLe.trans (le_of_lt hR0LtH)

/-- At each time one of the two groups realizes their maximum. -/
theorem exists_h3TerminalFourthQForcingDerivativeStateMassGroupAt_eq_max
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    ∃ q : Fin 2,
      h3TerminalFourthQForcingDerivativeStateMassGroupAt
          hH3 hClass ht j o k l q
        =
      max
        (
          h3TerminalFourthQForcingDerivativeRawL2ProductAt
            hH3 hClass ht j o k l
        )
        (
          h3TerminalFourthQForcingDerivativeMomentL1MixAt
            hH3 hClass ht j o k l
        ) := by

  by_cases h :
      h3TerminalFourthQForcingDerivativeMomentL1MixAt
          hH3 hClass ht j o k l
        ≤
      h3TerminalFourthQForcingDerivativeRawL2ProductAt
        hH3 hClass ht j o k l

  · refine ⟨0, ?_⟩
    rw [
      h3TerminalFourthQForcingDerivativeStateMassGroupAt_zero,
      max_eq_left h
    ]

  · have hReverse :
        h3TerminalFourthQForcingDerivativeRawL2ProductAt
            hH3 hClass ht j o k l
          ≤
        h3TerminalFourthQForcingDerivativeMomentL1MixAt
          hH3 hClass ht j o k l :=
      le_of_not_ge h

    refine ⟨1, ?_⟩
    rw [
      h3TerminalFourthQForcingDerivativeStateMassGroupAt_one,
      max_eq_right hReverse
    ]

/-- Freeze one escaping group on a cofinal subsequence. -/
theorem exists_fixed_h3TerminalFourthQForcingDerivativeStateMassGroup_subsequence_of_envelope_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
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
            h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
              hH3 hClass (hτ n) j o k l
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
              h3TerminalFourthQForcingDerivativeStateMassGroupAt
                hH3 hClass (hτ (s n)) j o k l q
          )
          atTop
          atTop := by

  classical

  have hMaxTop :=
    h3TerminalFourthQForcingDerivativeStateMassGroupMax_tendstoAtTop_of_envelope_tendstoAtTop
      hH3 hClass j o k l τ hτ hEnvelopeTop

  have hChoice :
      ∀ n : ℕ,
        ∃ q : Fin 2,
          h3TerminalFourthQForcingDerivativeStateMassGroupAt
              hH3 hClass (hτ n) j o k l q
            =
          max
            (
              h3TerminalFourthQForcingDerivativeRawL2ProductAt
                hH3 hClass (hτ n) j o k l
            )
            (
              h3TerminalFourthQForcingDerivativeMomentL1MixAt
                hH3 hClass (hτ n) j o k l
            ) := by
    intro n
    exact
      exists_h3TerminalFourthQForcingDerivativeStateMassGroupAt_eq_max
        hH3 hClass (hτ n) j o k l

  choose q hq using hChoice

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeStateMassGroupAt
              hH3 hClass (hτ n) j o k l (q n)
        )
        atTop
        atTop := by
    simpa only [hq] using hMaxTop

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

  have hs : ∀ n : ℕ, n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop : Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTauSub :
      Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) :=
    hTauTendsto.comp hsTop

  have hGroupTopBeforeRewrite :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeStateMassGroupAt
              hH3 hClass (hτ (s n)) j o k l (q (s n))
        )
        atTop
        atTop :=
    hChosenTop.comp hsTop

  have hGroupTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeStateMassGroupAt
              hH3 hClass (hτ (s n)) j o k l q0
        )
        atTop
        atTop := by
    simpa only [hFixed] using hGroupTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauSub, hGroupTop⟩

/--
Fourth-temporal escape now resolves to energy, a fixed nonzero higher-radial
moment, or one fixed state-mass group of a fixed oriented velocity/projected-RHS
pair.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativeStateMassGroup
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hFourth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
              (τ n)
        )
        atTop
        atTop) :
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
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass m
                  (τ (s n))
                  (hτ (s n))
            )
            atTop (𝓝 ∞)
    )
      ∨
    (
      ∃ o q : Fin 2,
        ∃ k l : Fin 3,
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n) ∧
            Tendsto s atTop atTop ∧
            Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalFourthQForcingDerivativeStateMassGroupAt
                    hH3 hClass (hτ (s n)) j o k l q
              )
              atTop atTop
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativeStateMassEnvelope
      hH3 hClass j τ hτ hTauTendsto hFourth
  with
    hEnergy
    |
    hRest

  · exact Or.inl hEnergy

  · rcases hRest with
      hHigher
      |
      hEnvelope

    · exact Or.inr (Or.inl hHigher)

    · rcases hEnvelope with
        ⟨o, k, l, s, hs, hsTop, hTauSub, hEnvelopeTop⟩

      obtain
        ⟨q, r, hr, hrTop, hTauSubSub, hGroupTop⟩ :=
        exists_fixed_h3TerminalFourthQForcingDerivativeStateMassGroup_subsequence_of_envelope_tendstoAtTop
          hH3 hClass j o k l
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hTauSub
          hEnvelopeTop

      have hComp :
          ∀ n : ℕ,
            n ≤ s (r n) := by
        intro n
        exact le_trans (hr n) (hs (r n))

      have hCompTop :
          Tendsto (fun n : ℕ => s (r n)) atTop atTop :=
        hsTop.comp hrTop

      exact
        Or.inr
          (
            Or.inr
              ⟨
                o,
                q,
                k,
                l,
                (fun n : ℕ => s (r n)),
                hComp,
                hCompTop,
                hTauSubSub,
                hGroupTop
              ⟩
          )

end

end Euclidean
end Bridge
end PrimeTensor
