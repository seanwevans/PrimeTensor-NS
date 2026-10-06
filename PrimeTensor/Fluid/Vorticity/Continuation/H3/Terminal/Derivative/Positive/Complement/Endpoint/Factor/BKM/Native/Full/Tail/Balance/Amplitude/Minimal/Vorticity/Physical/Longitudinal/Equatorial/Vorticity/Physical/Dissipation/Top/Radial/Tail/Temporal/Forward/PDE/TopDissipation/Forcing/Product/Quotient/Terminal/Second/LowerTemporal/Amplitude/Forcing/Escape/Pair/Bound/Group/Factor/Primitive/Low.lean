import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low

/-!
# Exclude the primitive raw-L² fourth-q forcing branch

The primitive fourth-q forcing reduction leaves a raw Fourier `L²` alternative
and an order-ten-moment/raw-`L¹` alternative.

The raw `L²` alternative is not a new terminal obstruction.  The generic
kinetic-energy estimates already proved for the terminal spectral velocity
show that either raw `L²` factor has square bounded by the zeroth-order kinetic
energy.  That energy is antitone on each strict H³ path tail, so no fixed raw
`L²` factor can diverge along a sequence converging to terminal time.

Thus the fourth-temporal frontier reduces to the existing shift-two
higher-radial branch or one fixed order-ten moment/raw-`L¹` primitive.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalFourthQForcingPrimitiveLow
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingPrimitiveLow :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Either primitive fourth-q raw-`L²` factor has square bounded by the physical
zeroth-order kinetic energy.
-/
theorem sq_h3TerminalForcingFourthQRawL2FactorAt_le_energy0
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 2) :
    (
      h3TerminalForcingFourthQRawL2FactorAt
        hH3 hClass ht k l q
    ) ^ 2
      ≤
    velocityH3Energy0At u t := by

  fin_cases q

  · simpa [
      h3TerminalForcingFourthQRawL2FactorAt,
      norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2
    ] using
      sq_norm_h3TerminalVelocityRawFourierL2_le_energy0
        hH3 hClass ht k

  · simpa [
      h3TerminalForcingFourthQRawL2FactorAt
    ] using
      sq_norm_h3TerminalVelocityRawFourierL2_le_energy0
        hH3 hClass ht l

/--
A fixed primitive fourth-q raw Fourier `L²` factor cannot diverge along a
strict sequence converging to terminal time.
-/
theorem not_h3TerminalForcingFourthQRawL2FactorAt_tendstoAtTop
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
            h3TerminalForcingFourthQRawL2FactorAt
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
          h3TerminalForcingFourthQRawL2FactorAt
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
        sq_h3TerminalForcingFourthQRawL2FactorAt_le_energy0
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
        h3TerminalForcingFourthQRawL2FactorAt
          hH3 hClass (hτ n) k l q :=
    hFactorTop.eventually
      (eventually_gt_atTop C)

  obtain
    ⟨n, hnLarge, hnSq⟩ :=
    (hLarge.and hSquareBound).exists

  let X : ℝ :=
    h3TerminalForcingFourthQRawL2FactorAt
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

/--
The primitive raw-`L²` alternative is impossible.  Hence fourth-temporal
amplitude escape reduces to either the pre-existing shift-two extended
higher-radial velocity moment or one fixed order-ten moment/raw-`L¹`
primitive on a cofinal terminal subsequence.
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_fixedForcingMomentL1Primitive
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
                  h3TerminalForcingFourthQMomentL1PrimitiveAt
                    hH3 hClass (hτ (s n)) k l r q
              )
              atTop
              atTop
    ) := by

  rcases
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_fixedForcingPrimitiveMass
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
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
        not_h3TerminalForcingFourthQRawL2FactorAt_tendstoAtTop
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
