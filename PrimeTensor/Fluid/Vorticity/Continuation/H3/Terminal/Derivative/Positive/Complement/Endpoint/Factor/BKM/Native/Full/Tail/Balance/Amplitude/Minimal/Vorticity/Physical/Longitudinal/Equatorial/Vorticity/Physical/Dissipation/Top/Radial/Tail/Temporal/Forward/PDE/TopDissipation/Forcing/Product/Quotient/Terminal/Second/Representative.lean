import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second

/-!
# Exact product-rule representative of the terminal q-forcing derivative

The lower-temporal frontier has one remaining forcing branch,

    ‖d/dt (q F_j)‖₂.

`Terminal.Second` already proves that the terminal `q F_j` path is strongly
differentiable.  This file retains the selected product-rule data from the same
local restart argument.

At every strict physical time `t`, there are selected states

* `U`, the velocity state;
* `R`, the projected-RHS state, i.e. the spectral time derivative;

with raw Fourier moment order six, such that

    d/dt (q F_j)
      = (2π)² D,

where `D` has a.e. representative

    |ξ|² [N(R,U)_j + N(U,R)_j].

The chosen `U` is exactly the terminal velocity state, and `R` retains the
exact raw PDE identity.  This is the lower-order analogue of the already
closed fourth-q representative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQForcingDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQForcingDerivative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 3200000

/--
At each strict physical time, the derivative of the terminal `q F_j` path is a
fixed scalar multiple of the canonical radial-order-two product-rule state.

The selected velocity state `U` and projected-RHS state `R` both retain order
six raw Fourier moments, precisely the input required by the generic
radial-order-two Leray bounds.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_deriv_exists_productRuleRepresentative
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
            (6 : ℝ)
            (U k))
          ∧
        (∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (6 : ℝ)
            (R k))
          ∧
        U =
          h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
          ∧
        (∀ k : Fin 3,
          (
            (
              h3SpectralScalarRawFourierL2 (R k) :
              H3FourierComplexL2
            ) :
            H3FourierPoint3 → ℂ
          )
            =ᵐ[(volume : Measure H3FourierPoint3)]
          (fun ξ : H3FourierPoint3 =>
            -(h3FourierGradientSquare ξ : ℂ)
                *
              (
                (
                  h3SpectralScalarRawFourierL2 (U k) :
                  H3FourierComplexL2
                ) ξ
              )
              -
            h3RawFinLerayOuterProductDivergence
              U U k ξ))
          ∧
        deriv
            (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
              hH3 hClass j)
            t
          =
        ((2 * Real.pi) ^ 2 : ℝ) • D
          ∧
        (
          ((D : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ)
            =ᵐ[(volume : Measure H3FourierPoint3)]
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
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
          (6 : ℝ)
          (U k) := by

    intro k

    dsimp only [U]

    exact
      h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
        6
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
          (6 : ℝ)
          (R k) := by

    intro k

    dsimp only [R]

    exact
      h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
        6
        (by norm_num)
        hNSShort
        ht₁
        hE
        hTail₁
        hQ
        hQR
        k
        qSlab

  have hUTerm :
      U =
        h3TerminalVelocitySpectralStateAt
          hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ := by

    dsimp only [U]

    unfold h3PreterminalSelectedUnitSpectralStateOnRadius

    rw [h3SelectedProjectedRHSSlabRadius_coe]

    simpa only [q, qSlab] using
      h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
        hH3 hClass hNSShort ht₁ hE hTail₁ hPhysical
        hQ hQR ht htS
        ⟨
          by simpa only [q] using hqLower.le,
          by simpa only [q] using hqUpper.le
        ⟩

  have hRPDE :
      ∀ k : Fin 3,
        (
          (
            h3SpectralScalarRawFourierL2 (R k) :
            H3FourierComplexL2
          ) :
          H3FourierPoint3 → ℂ
        )
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          -(h3FourierGradientSquare ξ : ℂ)
              *
            (
              (
                h3SpectralScalarRawFourierL2 (U k) :
                H3FourierComplexL2
              ) ξ
            )
            -
          h3RawFinLerayOuterProductDivergence
            U U k ξ) := by

    intro k

    have hDeweight :=
      h3SpectralScalarRawFourierL2_h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab_apply_eq
        hNSShort ht₁ hE hTail₁ hQ hQR qSlab k

    have hPDE :=
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_ae_eq_unitPDE
        hNSShort ht₁ hE hTail₁
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR qSlab)
        k

    rw [hDeweight]

    simpa only [U] using hPDE

  let D : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
      2 hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

  let W : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingSecondQTimeDerivativeFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

  have hW :
      W = ((2 * Real.pi) ^ 2 : ℝ) • D := by
    rfl

  let Fselected :
      ℝ → H3FourierComplexL2 :=
    fun r =>
      h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension
        hNSShort ht₁ hE hTail₁ hQ hQR j
        (r - t₁)

  let Fphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
      hH3 hClass j

  have hRelative :=
    h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension_hasDerivAt
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
      h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension_eq_terminalPhysicalForcingSecondQFourierL2At
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
        h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
          hH3 hClass hrClass j := by
      dsimp only [Fphysical]
      exact
        h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq
          hH3 hClass hrClass j

    calc
      Fphysical r
          =
        h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
          hH3 hClass hrClass j :=
        hPhysicalAt
      _ =
        h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension
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
      2
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
      hUTerm,
      hRPDE,
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
