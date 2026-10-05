import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.Fourth

/-!
# Exact product-rule representative of the terminal q²-forcing derivative

The fourth-temporal frontier has been reduced to physical H³-energy escape,
extended higher-radial escape, or divergence of

    ‖d/dt (q² F_j)‖₂.

The terminal `q² F_j` path is already known to be strongly differentiable.
This file retains more information from that proof.

At every strict physical time `t`, choose the same local canonical restart
window used in the differentiability argument.  At the corresponding selected
elapsed time there are two genuine spectral states:

* `U`, the selected velocity state;
* `R`, the selected projected-RHS state, i.e. the spectral time derivative.

Both carry raw Fourier moment order ten, which is exactly the moment required
by the radial-order-four Leray product theorem.  The actual terminal derivative
is then the fixed `(2π)^4` multiple of a Fourier `L²` state `D` whose a.e.
representative is

    |ξ|⁴ [ N(R,U)_j(ξ) + N(U,R)_j(ξ) ].

This is the terminal representation needed to reuse the finite Leray/state-mass
machinery without retaining restart-window parameters in later statements.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthQForcingDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingDerivative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 3200000

/--
At each strict physical time, the derivative of the terminal `q² F_j` path is
a fixed scalar multiple of the canonical radial-order-four product-rule state.

The selected velocity state `U` and projected-RHS state `R` both retain order
ten raw Fourier moments, precisely the input required by the generic
radial-order-four Leray bounds.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_deriv_exists_productRuleRepresentative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ∃ U R : H3SpectralFinVectorState,
      ∃ D : H3FourierComplexL2,
        (∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (10 : ℝ)
            (U k))
          ∧
        (∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (10 : ℝ)
            (R k))
          ∧
        deriv
            (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
              hH3 hClass j)
            t
          =
        ((2 * Real.pi) ^ 4 : ℝ) • D
          ∧
        (
          ((D : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ)
            =ᵐ[(volume : Measure H3FourierPoint3)]
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
              (
                h3RawFinLerayOuterProductDivergence
                    R U j ξ
                  +
                h3RawFinLerayOuterProductDivergence
                    U R j ξ
              ))
        ) := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  rcases
    hH3.exists_localCanonicalRestartWindowAt htAbs
  with
    ⟨
      t₀,
      S,
      E,
      ht₀,
      hST,
      hE,
      hTail,
      hGap0,
      hGapR,
      hTarget,
      htS
    ⟩

  have hS :
      0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes
      hS
      (le_of_lt hST)

  let restartRadius : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hRestartRadius :
      0 < restartRadius := by
    dsimp only [restartRadius]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  let δ : ℝ :=
    min
      (restartRadius / 2)
      ((t - t₀) / 2)

  have hGapHalf :
      0 < (t - t₀) / 2 := by
    linarith [hGap0]

  have hRadiusHalf :
      0 < restartRadius / 2 := by
    linarith

  have hδ0 :
      0 < δ := by
    dsimp only [δ]
    exact
      lt_min
        hRadiusHalf
        hGapHalf

  have hδRadiusHalf :
      δ ≤ restartRadius / 2 := by
    dsimp only [δ]
    exact min_le_left _ _

  have hδGapHalf :
      δ ≤ (t - t₀) / 2 := by
    dsimp only [δ]
    exact min_le_right _ _

  let t₁ : ℝ :=
    t - δ

  have ht₀t₁ :
      t₀ ≤ t₁ := by
    dsimp only [t₁]
    linarith [hδGapHalf]

  have ht₁t :
      t₁ < t := by
    dsimp only [t₁]
    linarith [hδ0]

  have ht₁S :
      t₁ < S :=
    lt_trans ht₁t htS

  have ht₁0 :
      0 < t₁ :=
    lt_of_lt_of_le
      ht₀.1
      ht₀t₁

  have ht₁ :
      t₁ ∈ Set.Ioo (0 : ℝ) S :=
    ⟨ht₁0, ht₁S⟩

  have hTail₁ :
      CanonicalH3TailDataFrom u t₁ S E :=
    canonicalH3TailDataFrom_mono_start
      ht₀t₁
      ht₁S
      hTail

  let q : ℝ :=
    t - t₁

  have hqδ :
      q = δ := by
    dsimp only [q, t₁]
    ring

  have hq0 :
      0 < q := by
    rw [hqδ]
    exact hδ0

  have hqRadiusHalf :
      q ≤ restartRadius / 2 := by
    rw [hqδ]
    exact hδRadiusHalf

  have htq :
      t₁ + q = t := by
    dsimp only [q]
    ring

  let Q : ℝ :=
    3 * q / 2

  have hQ :
      0 < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hqLower :
      Q / 2 < q := by
    dsimp only [Q]
    linarith [hq0]

  have hqUpper :
      q < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hQR :
      Q < h3FinHeatLerayRestartRadius (1 : ℝ) E := by

    have hThreeQuarter :
        3 * restartRadius / 4 < restartRadius := by
      linarith [hRestartRadius]

    have hQLe :
        Q ≤ 3 * restartRadius / 4 := by
      dsimp only [Q]
      linarith [hqRadiusHalf]

    have hQR' :
        Q < restartRadius :=
      lt_of_le_of_lt
        hQLe
        hThreeQuarter

    simpa only [restartRadius] using hQR'

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₁ hNSShort ht₁ hE hTail₁ :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₁ hNSShort ht₁ hTail₁

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₁ hNSShort ht₁ hE hTail₁ :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort
      ht₁
      hE
      hTail₁
      hWeakFTC

  let qSlab :
      Set.Icc (Q / 2) Q :=
    ⟨q, hqLower.le, hqUpper.le⟩

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNSShort ht₁ hE hTail₁
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR qSlab)

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR qSlab

  have hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (10 : ℝ)
          (U k) := by

    intro k

    dsimp only [U]

    exact
      h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
        10
        hNSShort
        ht₁
        hE
        hTail₁
        hQ
        hQR
        qSlab
        k

  have hR :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (10 : ℝ)
          (R k) := by

    intro k

    dsimp only [R]

    exact
      h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
        10
        (by norm_num)
        hNSShort
        ht₁
        hE
        hTail₁
        hQ
        hQR
        k
        qSlab

  let D : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
      4 hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

  let W : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingFourthQTimeDerivativeFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

  have hW :
      W = ((2 * Real.pi) ^ 4 : ℝ) • D := by
    rfl

  let Fselected :
      ℝ → H3FourierComplexL2 :=
    fun r =>
      h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension
        hNSShort ht₁ hE hTail₁ hQ hQR j
        (r - t₁)

  let Fphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j

  have hRelative :=
    h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension_hasDerivAt
      hNSShort
      ht₁
      hE
      hTail₁
      hQ
      hQR
      j
      ⟨hqLower, hqUpper⟩

  have hShift :
      HasDerivAt
        (fun r : ℝ => r - t₁)
        1
        t := by
    simpa using
      (hasDerivAt_id t).sub_const t₁

  have hSelectedAbsolute :
      HasDerivAt
        Fselected
        W
        t := by

    have hComp :=
      hRelative.scomp
        t
        hShift

    dsimp only [
      Fselected,
      W,
      qSlab,
      q
    ] at hComp ⊢

    simpa only [
      Function.comp_def,
      one_smul
    ] using hComp

  have hClassNeighborhood :
      Set.Ioo a T ∈ 𝓝 t :=
    Ioo_mem_nhds
      ht.1
      ht.2

  have hSlabLeft :
      t₁ + Q / 2 < t := by
    linarith [htq, hqLower]

  have hSlabRight :
      t < t₁ + Q := by
    linarith [htq, hqUpper]

  have hSlabNeighborhood :
      Set.Ioo
          (t₁ + Q / 2)
          (t₁ + Q)
        ∈
      𝓝 t :=
    Ioo_mem_nhds
      hSlabLeft
      hSlabRight

  have hSNeighborhood :
      Set.Iio S ∈ 𝓝 t :=
    Iio_mem_nhds htS

  have hEventuallyEq :
      Fphysical =ᶠ[𝓝 t] Fselected := by

    filter_upwards [
      hClassNeighborhood,
      hSlabNeighborhood,
      hSNeighborhood
    ] with r hrClass hrSlabAbs hrS

    have hrSlab :
        r - t₁ ∈ Set.Icc (Q / 2) Q := by
      constructor
      · linarith [hrSlabAbs.1]
      · linarith [hrSlabAbs.2]

    have hBridge :=
      h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension_eq_terminalPhysicalForcingFourthQFourierL2At
        hH3
        hClass
        hNSShort
        ht₁
        hE
        hTail₁
        hPhysical
        hQ
        hQR
        hrClass
        hrS
        hrSlab
        j

    have hPhysicalAt :
        Fphysical r
          =
        h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
          hH3 hClass hrClass j := by
      dsimp only [Fphysical]
      exact
        h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
          hH3 hClass hrClass j

    calc
      Fphysical r
          =
        h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
          hH3 hClass hrClass j :=
        hPhysicalAt
      _ =
        h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension
          hNSShort ht₁ hE hTail₁ hQ hQR j
          (r - t₁) := by
        exact hBridge.symm
      _ =
        Fselected r := by
        rfl

  have hPhysicalDerivative :
      HasDerivAt
        Fphysical
        W
        t :=
    hSelectedAbsolute.congr_of_eventuallyEq
      hEventuallyEq

  have hDerivEq :
      deriv Fphysical t = W :=
    hPhysicalDerivative.deriv

  have hDAE :=
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab_ae
      4
      hNSShort
      ht₁
      hE
      hTail₁
      hQ
      hQR
      j
      qSlab

  refine
    ⟨
      U,
      R,
      D,
      hU,
      hR,
      ?_,
      ?_
    ⟩

  · dsimp only [Fphysical] at hDerivEq
    rw [hW] at hDerivEq
    exact hDerivEq

  · dsimp only [D] at hDAE
    simpa only [U, R] using hDAE

end

end Euclidean
end Bridge
end PrimeTensor
