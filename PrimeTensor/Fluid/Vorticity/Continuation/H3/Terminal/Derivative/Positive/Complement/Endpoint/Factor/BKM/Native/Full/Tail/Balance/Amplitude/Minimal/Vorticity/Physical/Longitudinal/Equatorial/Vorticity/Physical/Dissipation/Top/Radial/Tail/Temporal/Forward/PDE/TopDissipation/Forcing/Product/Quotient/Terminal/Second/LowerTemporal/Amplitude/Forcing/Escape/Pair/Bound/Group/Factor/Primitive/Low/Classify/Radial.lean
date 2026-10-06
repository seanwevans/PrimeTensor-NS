import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Reduce the terminal order-ten fourth-q forcing moment to neighboring radial L² levels

The surviving genuinely high fourth-q forcing-side primitive is

    ∫ |ξ|^10 |û_j(ξ)| dξ.

The repository already contains the inverse-Bessel Cauchy--Schwarz bridge

    M_p(F) ≤ C_Bessel (‖|ξ|^p F‖₂ + ‖|ξ|^(p+2) F‖₂),

together with arbitrary-order terminal radial `L²` representatives.

For `p = 10`, order-ten moment escape therefore forces escape of one of the
neighboring radial square masses at orders `10` or `12`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable local instance axisFintypeH3TerminalFourthQMoment10Radial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQMoment10Radial :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Squared radial `L²` mass of one terminal physical velocity coordinate at
natural radial order `p`.
-/
noncomputable def h3TerminalForcingFourthQRawRadialSquareMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (p : ℕ)
    (j : Fin 3) : ℝ :=
  h3TerminalForcingThirdQRawRadialSquareMassAt
    hH3 hClass ht p j

theorem h3TerminalForcingFourthQRawRadialSquareMassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (p : ℕ)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingFourthQRawRadialSquareMassAt
        hH3 hClass ht p j := by
  exact
    h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
      hH3 hClass ht p j

/--
The order-ten raw Fourier moment is bounded by neighboring terminal radial
`L²` square masses at orders ten and twelve.
-/
theorem h3TerminalForcingFourthQMoment10MassAt_le_bessel_radial10_12
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalForcingFourthQMoment10MassAt
        hH3 hClass ht j
      ≤
    h3StandardInverseBesselWeightL2Factor
      *
    (
      Real.sqrt
        (h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 10 j)
        +
      Real.sqrt
        (h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 12 j)
    ) := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  obtain ⟨G10, hG10⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 10 (by norm_num) j

  obtain ⟨G12, hG12⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 12 (by norm_num) j

  have hBound :=
    integral_h3RawFourier_natMoment_le_bessel_mul_norms
      10
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier (U j) ξ)
      G10
      G12
      hG10
      hG12

  have h10Sq :
      ‖G10‖ ^ 2
        =
      h3TerminalForcingFourthQRawRadialSquareMassAt
        hH3 hClass ht 10 j := by
    unfold h3TerminalForcingFourthQRawRadialSquareMassAt
    exact
      norm_sq_eq_h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass ht 10 j G10 hG10

  have h12Sq :
      ‖G12‖ ^ 2
        =
      h3TerminalForcingFourthQRawRadialSquareMassAt
        hH3 hClass ht 12 j := by
    unfold h3TerminalForcingFourthQRawRadialSquareMassAt
    exact
      norm_sq_eq_h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass ht 12 j G12 hG12

  have h10Norm :
      ‖G10‖
        =
      Real.sqrt
        (h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 10 j) := by
    rw [← h10Sq]
    symm
    simpa only [
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg G10)
    ]

  have h12Norm :
      ‖G12‖
        =
      Real.sqrt
        (h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 12 j) := by
    rw [← h12Sq]
    symm
    simpa only [
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg G12)
    ]

  unfold h3TerminalForcingFourthQMoment10MassAt
  unfold h3SpectralScalarRawFourierMomentMass
  dsimp only [U] at hBound ⊢

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (10 : ℝ) ξ *
          ‖h3SpectralScalarRawFourier
              (h3TerminalVelocitySpectralStateAt hH3 t htAbs j) ξ‖
      ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 10 *
          ‖h3SpectralScalarRawFourier
              (h3TerminalVelocitySpectralStateAt hH3 t htAbs j) ξ‖
      ∂volume := by
        apply integral_congr_ae
        filter_upwards with ξ
        unfold h3FourierMomentWeight
        have hPow :
            ‖ξ‖ ^ (10 : ℝ)
              =
            ‖ξ‖ ^ (10 : ℕ) :=
          Real.rpow_natCast ‖ξ‖ 10
        rw [hPow]
    _ ≤
      h3StandardInverseBesselWeightL2Factor
        *
      (
        Real.sqrt
          (h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass ht 10 j)
          +
        Real.sqrt
          (h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass ht 12 j)
      ) := by
        simpa only [h10Norm, h12Norm] using hBound

/--
Order-ten raw-moment escape forces the maximum of the order-ten and
order-twelve radial square masses to tend to `+∞`.
-/
theorem h3TerminalForcingFourthQRawRadialSquareMassMax_tendstoAtTop_of_moment10_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10MassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          max
            (h3TerminalForcingFourthQRawRadialSquareMassAt
              hH3 hClass (hτ n) 10 j)
            (h3TerminalForcingFourthQRawRadialSquareMassAt
              hH3 hClass (hτ n) 12 j)
      )
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ := max M 0
  let C : ℝ := h3StandardInverseBesselWeightL2Factor

  have hMLe : M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact h3StandardInverseBesselWeightL2Factor_nonneg

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        C * (2 * Real.sqrt R) + 1
          <
        h3TerminalForcingFourthQMoment10MassAt
          hH3 hClass (hτ n) j :=
    hMomentTop.eventually
      (eventually_gt_atTop
        (C * (2 * Real.sqrt R) + 1))

  filter_upwards [hLarge] with n hn

  let A : ℝ :=
    h3TerminalForcingFourthQRawRadialSquareMassAt
      hH3 hClass (hτ n) 10 j

  let B : ℝ :=
    h3TerminalForcingFourthQRawRadialSquareMassAt
      hH3 hClass (hτ n) 12 j

  let H : ℝ := max A B

  have hAH : A ≤ H := by
    dsimp only [H]
    exact le_max_left A B

  have hBH : B ≤ H := by
    dsimp only [H]
    exact le_max_right A B

  have hBound :=
    h3TerminalForcingFourthQMoment10MassAt_le_bessel_radial10_12
      hH3 hClass (hτ n) j

  have hRLtH : R < H := by
    by_contra hNot

    have hHLe : H ≤ R :=
      le_of_not_gt hNot

    have hALe : A ≤ R :=
      hAH.trans hHLe

    have hBLe : B ≤ R :=
      hBH.trans hHLe

    have hSqrtA :
        Real.sqrt A ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt hALe

    have hSqrtB :
        Real.sqrt B ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt hBLe

    have hSum :
        Real.sqrt A + Real.sqrt B
          ≤
        2 * Real.sqrt R := by
      linarith

    have hScaled :
        C * (Real.sqrt A + Real.sqrt B)
          ≤
        C * (2 * Real.sqrt R) :=
      mul_le_mul_of_nonneg_left hSum hC0

    have hMomentLe :
        h3TerminalForcingFourthQMoment10MassAt
            hH3 hClass (hτ n) j
          ≤
        C * (2 * Real.sqrt R) := by
      dsimp only [A, B, C] at hBound ⊢
      exact hBound.trans hScaled

    linarith

  change
    M
      ≤
    max
      (h3TerminalForcingFourthQRawRadialSquareMassAt
        hH3 hClass (hτ n) 10 j)
      (h3TerminalForcingFourthQRawRadialSquareMassAt
        hH3 hClass (hτ n) 12 j)

  exact
    hMLe.trans
      (le_of_lt hRLtH)

/--
Finite channel packaging of the neighboring radial square masses:
channel `0` is order `10`, channel `1` is order `12`.
-/
noncomputable def h3TerminalForcingFourthQMoment10RadialSquareChannelAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalForcingFourthQRawRadialSquareMassAt
      hH3 hClass ht 10 j
  else
    h3TerminalForcingFourthQRawRadialSquareMassAt
      hH3 hClass ht 12 j

/--
Order-ten moment escape admits a cofinal subsequence on which one fixed
neighboring radial square level (`10` or `12`) diverges.
-/
theorem exists_fixed_h3TerminalForcingFourthQMoment10RadialSquareChannel_subsequence
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
    (hMomentTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10MassAt
              hH3 hClass (hτ n) j
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
              h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                hH3 hClass (hτ (s n)) j q
          )
          atTop
          atTop := by

  classical

  have hMaxTop :=
    h3TerminalForcingFourthQRawRadialSquareMassMax_tendstoAtTop_of_moment10_tendstoAtTop
      hH3 hClass j τ hτ hMomentTop

  let q : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 12 j
          ≤
        h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass (hτ n) 10 j
      then 0
      else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalForcingFourthQMoment10RadialSquareChannelAt
            hH3 hClass (hτ n) j (q n)
          =
        max
          (h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 10 j)
          (h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 12 j) := by

    intro n
    dsimp only [q]

    by_cases h :
        h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 12 j
          ≤
        h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass (hτ n) 10 j

    · simp only [if_pos h]
      unfold h3TerminalForcingFourthQMoment10RadialSquareChannelAt
      simp only [if_pos]
      exact (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          h3TerminalForcingFourthQRawRadialSquareMassAt
              hH3 hClass (hτ n) 10 j
            ≤
          h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 12 j :=
        le_of_lt (lt_of_not_ge h)

      unfold h3TerminalForcingFourthQMoment10RadialSquareChannelAt
      simp only [if_neg, one_ne_zero]
      exact (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10RadialSquareChannelAt
              hH3 hClass (hτ n) j (q n)
        )
        atTop
        atTop := by
    simpa only [hChosen] using hMaxTop

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2,
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
        atTop
        (𝓝 T) :=
    hTauTendsto.comp hsTop

  have hTopBeforeRewrite :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10RadialSquareChannelAt
              hH3 hClass (hτ (s n)) j (q (s n))
        )
        atTop
        atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQMoment10RadialSquareChannelAt
              hH3 hClass (hτ (s n)) j q0
        )
        atTop
        atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauSub, hTop⟩

/--
The order-ten fourth-q forcing obstruction has now been converted into one
fixed neighboring radial square level (`10` or `12`).  The higher-radial and
H³-energy alternatives are unchanged.
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_energy_or_fixedRadial10_12
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
    (hAmplitudeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
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
                hH3 hClass 2
                (τ (s n))
                (hτ (s n))
          )
          atTop
          (𝓝 ∞)
    )
      ∨
    (
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
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n)))
            atTop
            atTop
      )
        ∨
      (
        ∃ m : Fin 3,
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
                    h3TerminalForcingFourthQMoment10RadialSquareChannelAt
                      hH3 hClass (hτ (s n)) m q
                )
                atTop
                atTop
      )
    ) := by

  rcases
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_energy_or_fixedMoment10
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with
    hHigher
    |
    hRest

  · exact Or.inl hHigher

  · rcases hRest with
      hEnergy
      |
      hMoment

    · exact
        Or.inr
          (Or.inl hEnergy)

    · rcases hMoment with
        ⟨m, s, hs, hsTop, hTauSub, hMomentTop⟩

      obtain
        ⟨q, v, hv, hvTop, hTauFinal, hRadialTop⟩ :=
        exists_fixed_h3TerminalForcingFourthQMoment10RadialSquareChannel_subsequence
          hH3 hClass m
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hTauSub
          hMomentTop

      have hComp :
          ∀ n : ℕ,
            n ≤ s (v n) := by
        intro n
        exact le_trans (hv n) (hs (v n))

      have hCompTop :
          Tendsto
            (fun n : ℕ => s (v n))
            atTop
            atTop :=
        hsTop.comp hvTop

      exact
        Or.inr
          (
            Or.inr
              ⟨
                m,
                q,
                (fun n : ℕ => s (v n)),
                hComp,
                hCompTop,
                hTauFinal,
                hRadialTop
              ⟩
          )

end

end Euclidean
end Bridge
end PrimeTensor
