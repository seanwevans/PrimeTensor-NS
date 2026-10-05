import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Bound.Forcing.Moment
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Reduce the terminal order-fourteen forcing moment to neighboring radial L² levels

The surviving genuinely high forcing-side primitive is

    ∫ |ξ|^14 |û_j(ξ)| dξ.

The repository already contains the inverse-Bessel Cauchy--Schwarz bridge

    M_p(F) ≤ C_Bessel (‖|ξ|^p F‖₂ + ‖|ξ|^(p+2) F‖₂).

At every strict physical time the local canonical restart provides the required
arbitrary-order selected radial `L²` representatives, and selected/physical
agreement identifies their raw Fourier coordinate with the terminal physical
velocity.

For `p = 14`, order-fourteen moment escape therefore forces escape of one of
the neighboring radial square masses of order `14` or `16`.  This is the
intermediate form needed before identifying those levels with shifts `10` and
`12` of the extended higher-radial physical hierarchy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable local instance axisFintypeH3TerminalThirdQMoment14Radial
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQMoment14Radial :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Intrinsic radial square masses -/

/--
Squared radial `L²` mass of one terminal physical velocity coordinate at
natural radial order `p`.
-/
noncomputable def h3TerminalForcingThirdQRawRadialSquareMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (p : ℕ)
    (j : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ∫ ξ : H3FourierPoint3,
    norm
      (
        (((‖ξ‖ ^ p : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ)
      ) ^ 2
    ∂volume

theorem h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (p : ℕ)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass ht p j := by

  unfold h3TerminalForcingThirdQRawRadialSquareMassAt
  dsimp only

  exact
    integral_nonneg
      (fun ξ => sq_nonneg _)

/-! ## Arbitrary-order terminal radial L² representative -/

/--
At every strict physical time and every natural radial order `p ≥ 2`, one
Fourier `L²` state realizes the literal terminal raw representative
`|ξ|^p û_j(ξ)`.
-/
theorem exists_h3TerminalVelocityNatRadialFourierL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (p : ℕ)
    (hp : 2 ≤ p)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ∃ G : H3FourierComplexL2,
      ((G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ p : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ) := by

  dsimp only

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  rcases
    hH3.exists_localCanonicalRestartWindowAt htAbs
  with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hGap0, hGapR, hTarget, htS⟩

  have hS : 0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hS hST.le

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₀ hNSShort ht₀ hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₀ hNSShort ht₀ hTail

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₀ hNSShort ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort ht₀ hE hTail hWeakFTC

  let q : ℝ := t - t₀
  let R : ℝ := h3FinHeatLerayRestartRadius (1 : ℝ) E
  let B : ℝ := min (2 * q) R
  let Q : ℝ := (q + B) / 2

  have hq0 : 0 < q := by
    dsimp only [q]
    exact hGap0

  have hqR : q < R := by
    dsimp only [q, R]
    exact hGapR

  have hqB : q < B := by
    dsimp only [B]
    exact lt_min (by linarith [hq0]) hqR

  have hB_le_twoq : B ≤ 2 * q := by
    dsimp only [B]
    exact min_le_left _ _

  have hB_le_R : B ≤ R := by
    dsimp only [B]
    exact min_le_right _ _

  have hQ : 0 < Q := by
    dsimp only [Q]
    linarith [hq0, hqB]

  have hqUpper : q < Q := by
    dsimp only [Q]
    linarith [hqB]

  have hqLower : Q / 2 < q := by
    dsimp only [Q]
    linarith [hB_le_twoq, hq0]

  have hQR : Q < R := by
    dsimp only [Q]
    linarith [hqR, hB_le_R]

  let qSlab : Set.Icc (Q / 2) Q :=
    ⟨q, hqLower.le, hqUpper.le⟩

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNSShort ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNSShort ht₀ hE hTail

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ q

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hState :
      Usel = Uterm := by

    dsimp only [Usel, Uterm, U₀, hA, hU₀]

    simpa only [q] using
      h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
        hH3 hClass hNSShort ht₀ hE hTail hPhysical
        hQ hQR ht htS
        ⟨
          by simpa only [q] using hqLower.le,
          by simpa only [q] using hqUpper.le
        ⟩

  let hhalf : 0 < Q / 2 := by
    positivity

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      p hp
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR qSlab j

  have hGAE :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      p hp
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR qSlab j

  have hRaw :
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ q j
        =
      h3SpectralScalarRawFourierL2
        (Uterm j) := by

    rw [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_eq_scalarRawFourierL2
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j
    ]

    change
      h3SpectralScalarRawFourierL2
          (Usel j)
        =
      h3SpectralScalarRawFourierL2
          (Uterm j)

    rw [hState]

  have hRawAE :=
    h3SpectralScalarRawFourierL2_ae
      (Uterm j)

  refine ⟨G, ?_⟩

  filter_upwards [hGAE, hRawAE]
    with ξ hGξ hRawξ

  rw [hGξ]
  rw [hRaw]
  rw [hRawξ]

/--
The norm square of any terminal radial representative is exactly the intrinsic
radial square mass.
-/
theorem norm_sq_eq_h3TerminalForcingThirdQRawRadialSquareMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (p : ℕ)
    (j : Fin 3)
    (G : H3FourierComplexL2)
    (hG :
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      ((G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ p : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ)) :
    ‖G‖ ^ 2
      =
    h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass ht p j := by

  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  unfold h3TerminalForcingThirdQRawRadialSquareMassAt
  dsimp only at hG ⊢

  apply integral_congr_ae

  filter_upwards [hG] with ξ hGξ

  rw [hGξ]

/-! ## Inverse-Bessel bound at p = 14 -/

/--
The fixed order-fourteen raw Fourier moment is bounded by the neighboring
terminal radial `L²` square masses at orders fourteen and sixteen.
-/
theorem h3TerminalForcingThirdQMoment14MassAt_le_bessel_radial14_16
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalForcingThirdQMoment14MassAt
        hH3 hClass ht j
      ≤
    h3StandardInverseBesselWeightL2Factor
      *
    (
      Real.sqrt
        (h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 14 j)
        +
      Real.sqrt
        (h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 16 j)
    ) := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  obtain ⟨G14, hG14⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 14 (by norm_num) j

  obtain ⟨G16, hG16⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 16 (by norm_num) j

  have hBound :=
    integral_h3RawFourier_natMoment_le_bessel_mul_norms
      14
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier (U j) ξ)
      G14
      G16
      hG14
      hG16

  have h14Sq :
      ‖G14‖ ^ 2
        =
      h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass ht 14 j :=
    norm_sq_eq_h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass ht 14 j G14 hG14

  have h16Sq :
      ‖G16‖ ^ 2
        =
      h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass ht 16 j :=
    norm_sq_eq_h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass ht 16 j G16 hG16

  have h14Norm :
      ‖G14‖
        =
      Real.sqrt
        (h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 14 j) := by

    rw [← h14Sq]
    symm
    simpa only [
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg G14)
    ]

  have h16Norm :
      ‖G16‖
        =
      Real.sqrt
        (h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 16 j) := by

    rw [← h16Sq]
    symm
    simpa only [
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg G16)
    ]

  unfold h3TerminalForcingThirdQMoment14MassAt
  unfold h3SpectralScalarRawFourierMomentMass
  dsimp only [U] at hBound ⊢

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (14 : ℝ) ξ *
          ‖h3SpectralScalarRawFourier
              (h3TerminalVelocitySpectralStateAt hH3 t htAbs j) ξ‖
      ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 14 *
          ‖h3SpectralScalarRawFourier
              (h3TerminalVelocitySpectralStateAt hH3 t htAbs j) ξ‖
      ∂volume := by
        apply integral_congr_ae
        filter_upwards with ξ
        unfold h3FourierMomentWeight
        have hPow :
            ‖ξ‖ ^ (14 : ℝ)
              =
            ‖ξ‖ ^ (14 : ℕ) :=
          Real.rpow_natCast ‖ξ‖ 14
        rw [hPow]
    _ ≤
      h3StandardInverseBesselWeightL2Factor
        *
      (
        Real.sqrt
          (h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass ht 14 j)
          +
        Real.sqrt
          (h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass ht 16 j)
      ) := by
        simpa only [h14Norm, h16Norm] using hBound

/-! ## Escape transfer to one neighboring radial square mass -/

/--
Order-fourteen raw-moment escape forces the maximum of the order-fourteen and
order-sixteen radial square masses to tend to `+∞`.
-/
theorem h3TerminalForcingThirdQRawRadialSquareMassMax_tendstoAtTop_of_moment14_tendstoAtTop
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
            h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          max
            (h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 14 j)
            (h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 16 j)
      )
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ :=
    max M 0

  let C : ℝ :=
    h3StandardInverseBesselWeightL2Factor

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hR0 :
      0 ≤ R := by
    dsimp only [R]
    exact le_max_right M 0

  have hC0 :
      0 ≤ C := by
    dsimp only [C]
    exact h3StandardInverseBesselWeightL2Factor_nonneg

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        C * (2 * Real.sqrt R) + 1
          <
        h3TerminalForcingThirdQMoment14MassAt
          hH3 hClass (hτ n) j :=
    hMomentTop.eventually
      (eventually_gt_atTop
        (C * (2 * Real.sqrt R) + 1))

  filter_upwards [hLarge] with n hn

  let A : ℝ :=
    h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass (hτ n) 14 j

  let B : ℝ :=
    h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass (hτ n) 16 j

  let H : ℝ :=
    max A B

  have hA0 :
      0 ≤ A := by
    dsimp only [A]
    exact
      h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
        hH3 hClass (hτ n) 14 j

  have hB0 :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3TerminalForcingThirdQRawRadialSquareMassAt_nonneg
        hH3 hClass (hτ n) 16 j

  have hAH :
      A ≤ H := by
    dsimp only [H]
    exact le_max_left A B

  have hBH :
      B ≤ H := by
    dsimp only [H]
    exact le_max_right A B

  have hBound :=
    h3TerminalForcingThirdQMoment14MassAt_le_bessel_radial14_16
      hH3 hClass (hτ n) j

  have hRLtH :
      R < H := by

    by_contra hNot

    have hHLe :
        H ≤ R :=
      le_of_not_gt hNot

    have hALe :
        A ≤ R :=
      hAH.trans hHLe

    have hBLe :
        B ≤ R :=
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
      mul_le_mul_of_nonneg_left
        hSum
        hC0

    have hMomentLe :
        h3TerminalForcingThirdQMoment14MassAt
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
      (h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass (hτ n) 14 j)
      (h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass (hτ n) 16 j)

  exact
    hMLe.trans
      (le_of_lt hRLtH)

/--
Finite channel packaging of the neighboring radial square masses:
channel `0` is order `14`, channel `1` is order `16`.
-/
noncomputable def h3TerminalForcingThirdQMoment14RadialSquareChannelAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass ht 14 j
  else
    h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass ht 16 j

/--
Order-fourteen moment escape admits a cofinal subsequence on which one fixed
neighboring radial square level (`14` or `16`) diverges.
-/
theorem exists_fixed_h3TerminalForcingThirdQMoment14RadialSquareChannel_subsequence
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
            h3TerminalForcingThirdQMoment14MassAt
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
              h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                hH3 hClass (hτ (s n)) j q
          )
          atTop
          atTop := by

  classical

  have hMaxTop :=
    h3TerminalForcingThirdQRawRadialSquareMassMax_tendstoAtTop_of_moment14_tendstoAtTop
      hH3 hClass j τ hτ hMomentTop

  let q : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j
          ≤
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass (hτ n) 14 j
      then 0
      else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalForcingThirdQMoment14RadialSquareChannelAt
            hH3 hClass (hτ n) j (q n)
          =
        max
          (h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 14 j)
          (h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j) := by

    intro n

    dsimp only [q]

    by_cases h :
        h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j
          ≤
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass (hτ n) 14 j

    · simp only [if_pos h]
      unfold h3TerminalForcingThirdQMoment14RadialSquareChannelAt
      simp only [if_pos]
      exact
        (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 14 j
            ≤
          h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j :=
        le_of_lt
          (lt_of_not_ge h)

      unfold h3TerminalForcingThirdQMoment14RadialSquareChannelAt
      simp only [if_neg, one_ne_zero]
      exact
        (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareChannelAt
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
    hTauTendsto.comp hsTop

  have hTopBeforeRewrite :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareChannelAt
              hH3 hClass (hτ (s n)) j (q (s n))
        )
        atTop
        atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQMoment14RadialSquareChannelAt
              hH3 hClass (hτ (s n)) j q0
        )
        atTop
        atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauSub, hTop⟩

/-! ## Sixth-diffusion frontier with radial L² forcing obstruction -/

/--
The order-fourteen forcing obstruction has now been converted into one fixed
neighboring radial square level (`14` or `16`).  The other alternatives are
unchanged.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_energy_or_fixedRadial14_16
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
                    h3TerminalForcingThirdQMoment14RadialSquareChannelAt
                      hH3 hClass (hτ (s n)) m q
                )
                atTop
                atTop
      )
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_energy_or_fixedMoment14
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigher
    |
    hRest

  · exact
      Or.inl hHigher

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
        exists_fixed_h3TerminalForcingThirdQMoment14RadialSquareChannel_subsequence
          hH3 hClass m
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hTauSub
          hMomentTop

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
