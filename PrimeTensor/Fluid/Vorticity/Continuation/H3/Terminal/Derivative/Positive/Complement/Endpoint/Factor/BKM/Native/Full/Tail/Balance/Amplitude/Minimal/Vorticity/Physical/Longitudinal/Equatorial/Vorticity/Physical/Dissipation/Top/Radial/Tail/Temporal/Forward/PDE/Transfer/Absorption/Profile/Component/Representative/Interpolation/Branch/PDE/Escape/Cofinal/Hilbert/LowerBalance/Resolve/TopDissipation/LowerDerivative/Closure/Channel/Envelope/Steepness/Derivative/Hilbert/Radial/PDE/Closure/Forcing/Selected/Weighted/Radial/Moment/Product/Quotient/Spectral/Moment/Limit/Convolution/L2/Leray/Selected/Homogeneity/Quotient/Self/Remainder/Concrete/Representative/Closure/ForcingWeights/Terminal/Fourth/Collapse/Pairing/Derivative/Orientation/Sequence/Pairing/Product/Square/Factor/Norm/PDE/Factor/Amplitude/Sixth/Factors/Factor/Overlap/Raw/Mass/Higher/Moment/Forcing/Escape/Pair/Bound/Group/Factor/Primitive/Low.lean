import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive
import PrimeTensor.Fluid.Vorticity.Continuation.H3.BKM.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.From.Derivative.Identities
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.Lower.Radial

/-!
# Exclude the primitive raw-L² third-q forcing branch

The primitive third-q forcing reduction leaves a raw Fourier `L²` alternative
and an order-fourteen-moment/raw-`L¹` alternative.

The raw `L²` alternative is not a new terminal obstruction.  Pointwise complex
conjugation preserves the Fourier `L²` norm, each raw velocity component is
bounded by the physical zeroth-order kinetic energy, and that kinetic energy is
already antitone on every strict H³ path tail by the closed energy identities.

Consequently no fixed primitive raw-`L²` factor can diverge along a sequence
converging to the terminal time.  The sixth-diffusion frontier therefore
reduces further to the old shift-four higher-radial branch or the remaining
moment/`L¹` primitive branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalThirdQForcingPrimitiveLow
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQForcingPrimitiveLow :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Conjugation does not change the raw Fourier L² norm -/

/--
Pointwise complex conjugation preserves the raw Fourier `L²` norm.
-/
theorem norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarRawFourierConjL2 G‖
      =
    ‖h3SpectralScalarRawFourierL2 G‖ := by

  have hAE :=
    h3SpectralScalarRawFourierConjL2_ae G

  have hRawAE :=
    h3SpectralScalarRawFourierL2_ae G

  have hSq :
      ‖h3SpectralScalarRawFourierConjL2 G‖ ^ 2
        =
      ‖h3SpectralScalarRawFourierL2 G‖ ^ 2 := by

    rw [
      h3FourierComplexL2_norm_sq_eq_integral_norm_sq,
      h3FourierComplexL2_norm_sq_eq_integral_norm_sq
    ]

    apply integral_congr_ae

    filter_upwards [hAE, hRawAE] with ξ hξ hRawξ

    rw [hξ, hRawξ]

    simp [Complex.conjCLE_apply]

  have hLeft0 :
      0 ≤ ‖h3SpectralScalarRawFourierConjL2 G‖ :=
    norm_nonneg _

  have hRight0 :
      0 ≤ ‖h3SpectralScalarRawFourierL2 G‖ :=
    norm_nonneg _

  nlinarith

/-! ## Raw velocity L² is contained in the kinetic block -/

/--
At every strict H³-path time, one raw Fourier velocity component has squared
`L²` norm bounded by the exact zeroth-order kinetic energy.
-/
theorem sq_norm_h3TerminalVelocityRawFourierL2_le_energy0
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ‖h3SpectralScalarRawFourierL2 (U j)‖ ^ 2
      ≤
    velocityH3Energy0At u t := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hRaw :
      h3SpectralScalarRawFourierL2 (U j)
        =
      velocityH3BaseFourierAt
        u t hInt hMeas j := by

    dsimp only [U]

    unfold h3TerminalVelocitySpectralStateAt

    exact
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        hFourier j

  let componentMass : Fin 3 → ℝ :=
    fun k =>
      ∫ ξ : H3FourierPoint3,
        ‖velocityH3BaseFourierAt
            u t hInt hMeas k ξ‖ ^ 2
        ∂(volume : Measure H3FourierPoint3)

  have hComponentNonneg :
      ∀ k : Fin 3,
        0 ≤ componentMass k := by

    intro k

    dsimp only [componentMass]

    exact
      integral_nonneg
        (fun ξ =>
          sq_nonneg
            ‖velocityH3BaseFourierAt
                u t hInt hMeas k ξ‖)

  have hComponentLe :
      componentMass j
        ≤
      velocityH3FourierZerothRadialMomentAt
        u t hInt hMeas := by

    unfold velocityH3FourierZerothRadialMomentAt

    change
      componentMass j
        ≤
      ∑ k : Fin 3, componentMass k

    exact
      Finset.single_le_sum
        (fun k _ =>
          hComponentNonneg k)
        (Finset.mem_univ j)

  have hNormSq :
      ‖h3SpectralScalarRawFourierL2 (U j)‖ ^ 2
        =
      componentMass j := by

    rw [
      h3FourierComplexL2_norm_sq_eq_integral_norm_sq,
      hRaw
    ]

  have hEnergy :
      velocityH3Energy0At u t
        =
      velocityH3FourierZerothRadialMomentAt
        u t hInt hMeas :=
    velocityH3Energy0At_eq_fourierZerothRadialMoment
      hInt hMeas

  rw [hNormSq]

  exact
    hComponentLe.trans_eq
      hEnergy.symm

/--
Either primitive raw-`L²` factor from the Young decomposition has square
bounded by the physical kinetic energy.
-/
theorem sq_h3TerminalForcingThirdQRawL2FactorAt_le_energy0
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 2) :
    (
      h3TerminalForcingThirdQRawL2FactorAt
        hH3 hClass ht k l q
    ) ^ 2
      ≤
    velocityH3Energy0At u t := by

  fin_cases q

  · simpa [
      h3TerminalForcingThirdQRawL2FactorAt,
      norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2
    ] using
      sq_norm_h3TerminalVelocityRawFourierL2_le_energy0
        hH3 hClass ht k

  · simpa [
      h3TerminalForcingThirdQRawL2FactorAt
    ] using
      sq_norm_h3TerminalVelocityRawFourierL2_le_energy0
        hH3 hClass ht l

/-! ## Terminal exclusion -/

/--
A fixed primitive raw Fourier `L²` factor cannot diverge along a strict
sequence converging to the terminal time.
-/
theorem not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (q : Fin 2)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T)) :
    ¬
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQRawL2FactorAt
              hH3 hClass (hτ n) k l q
        )
        atTop
        atTop := by

  intro hFactorTop

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hTauAbove :
      ∀ᶠ n : ℕ in atTop,
        b < τ n :=
    (tendsto_order.1 hTauTendsto).1
      b
      hb.2

  have hSquareBound :
      ∀ᶠ n : ℕ in atTop,
        (
          h3TerminalForcingThirdQRawL2FactorAt
            hH3 hClass (hτ n) k l q
        ) ^ 2
          ≤
        velocityH3Energy0At u b := by

    filter_upwards [hTauAbove] with n hbn

    have hKinetic :
        velocityH3Energy0At u (τ n)
          ≤
        velocityH3Energy0At u b :=
      hKineticAnti
        hb
        (hτ n)
        (le_of_lt hbn)

    exact
      (
        sq_h3TerminalForcingThirdQRawL2FactorAt_le_energy0
          hH3 hClass (hτ n) k l q
      ).trans
        hKinetic

  have hE0 :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  let C : ℝ :=
    velocityH3Energy0At u b + 1

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        C
          <
        h3TerminalForcingThirdQRawL2FactorAt
          hH3 hClass (hτ n) k l q :=
    hFactorTop.eventually
      (eventually_gt_atTop C)

  obtain
    ⟨n, hnLarge, hnSq⟩ :=
    (hLarge.and hSquareBound).exists

  let X : ℝ :=
    h3TerminalForcingThirdQRawL2FactorAt
      hH3 hClass (hτ n) k l q

  have hXPos :
      0 < X := by
    dsimp only [X, C] at hnLarge
    linarith

  have hXOne :
      1 < X := by
    dsimp only [X, C] at hnLarge
    linarith

  have hXSq :
      X < X ^ 2 := by
    have hPositive :
        0 < X * (X - 1) :=
      mul_pos
        hXPos
        (sub_pos.mpr hXOne)

    nlinarith

  have hEX :
      velocityH3Energy0At u b < X := by
    dsimp only [X, C] at hnLarge
    linarith

  have hContr :
      velocityH3Energy0At u b < X ^ 2 :=
    hEX.trans hXSq

  dsimp only [X] at hContr
  exact
    (not_lt_of_ge hnSq)
      hContr

/-! ## Remove the low primitive branch from the sixth-diffusion frontier -/

/--
The primitive raw-`L²` alternative is impossible.  Hence sixth-diffusion
escape reduces to either the pre-existing shift-four extended higher-radial
velocity moment or one fixed moment/`L¹` primitive on a cofinal terminal
subsequence.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingMomentL1Primitive
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
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingPrimitiveMass
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigher
    |
    hPrimitive

  · exact
      Or.inl hHigher

  · rcases hPrimitive with
      ⟨k, l, hRaw | hMomentL1⟩

    · rcases hRaw with
        ⟨r, s, hs, hsTop, hTauSub, hRawTop⟩

      have hNot :=
        not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
          hH3 hClass k l r
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hTauSub

      exact
        False.elim
          (hNot hRawTop)

    · exact
        Or.inr
          ⟨k, l, hMomentL1⟩

end

end Euclidean
end Bridge
end PrimeTensor
