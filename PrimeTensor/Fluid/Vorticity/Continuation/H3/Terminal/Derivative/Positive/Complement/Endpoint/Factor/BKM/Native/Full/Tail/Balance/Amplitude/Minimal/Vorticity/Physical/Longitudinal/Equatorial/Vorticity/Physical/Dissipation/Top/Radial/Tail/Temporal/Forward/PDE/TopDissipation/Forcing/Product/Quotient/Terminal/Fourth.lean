import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second

/-!
# Differentiate the canonical terminal q² F forcing path

The selected intrinsic `q² F_j` path is strongly differentiable at every
strict interior restart-slab time, and the selected/terminal overlap theorem
identifies it with the canonical terminal `q² F_j` state.

This transports that derivative through the same local canonical restart
window used for `q F_j`.  Consequently the fourth-temporal forcing-driven
Hilbert obstruction cannot use its nondifferentiability branch; only the
cofinally unbounded Hilbert pairing remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2600000

/-! ## Global strict-time terminal q² F differentiability -/

/--
At every strict physical time, the canonical terminal `q² F_j` path has a
strong Fourier `L²` derivative.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_differentiableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    DifferentiableAt ℝ
      (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j)
      t := by

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

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  let δ : ℝ :=
    min
      (R / 2)
      ((t - t₀) / 2)

  have hGapHalf :
      0 < (t - t₀) / 2 := by
    linarith [hGap0]

  have hRHalf :
      0 < R / 2 := by
    linarith

  have hδ0 :
      0 < δ := by
    dsimp only [δ]
    exact
      lt_min
        hRHalf
        hGapHalf

  have hδRHalf :
      δ ≤ R / 2 := by
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

  have hqRHalf :
      q ≤ R / 2 := by
    rw [hqδ]
    exact hδRHalf

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
      Q < R := by
    have hThreeQuarter :
        3 * R / 4 < R := by
      linarith [hR]

    have hQLe :
        Q ≤ 3 * R / 4 := by
      dsimp only [Q]
      linarith [hqRHalf]

    exact
      lt_of_le_of_lt
        hQLe
        hThreeQuarter

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

  let W : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingFourthQTimeDerivativeFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

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

  exact
    hPhysicalDerivative.differentiableAt

/-! ## Collapse the fourth-temporal forcing-driven obstruction -/

/--
Once the terminal `q² F_j` path is differentiable at every strict preterminal
time, a fourth-temporal forcing-driven Hilbert obstruction can only occupy its
cofinally unbounded pairing branch.
-/
theorem fourthTemporal_pairing_cofinallyUnbounded_of_forcingDrivenHilbertDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalForcingDrivenHilbertDerivativeObstruction
        (a := a) (T := T)
        (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j)
        (h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j)) :
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃ r : ℝ,
          r ∈ Set.Ioo c T
            ∧
          M
            <
          abs
            (
              2 *
                inner ℝ
                  (h3TerminalResolvedFourthTemporalHilbertState
                    hH3 hClass j r)
                  (
                    deriv
                      (h3TerminalResolvedFourthTemporalHilbertState
                        hH3 hClass j)
                      r
                  )
            ) := by

  intro c hc

  rcases
    hObstruction c hc
  with hFail | hLarge

  · obtain
      ⟨t, htTail, hNotDiff⟩ :=
      hFail

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htTail.1,
        htTail.2
      ⟩

    exact
      False.elim
        (
          hNotDiff
            (
              h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_differentiableAt
                hH3 hClass ht j
            )
        )

  · exact hLarge

end

end Euclidean
end Bridge
end PrimeTensor
