import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Sliding.Energy.Class
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Curl.Weak.FTC.Global.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Global.Closure

/-!
# Close the global physical fourth-radial Hilbert derivative

The selected weighted state now has a genuine cutoff-free strong Fourier `L²`
derivative, and the preceding checkpoint identifies that state exactly with the
old physical `q² û_j` state on every strict selected/old overlap.

This file performs the final germ transport.

At one strict physical time `t`:

1. choose a local canonical restart window around `t`;
2. slide its anchor forward so the elapsed target `q` is at most half the
   restart radius;
3. choose `Q = 3q/2`, putting `q` strictly inside `(Q/2,Q)` while keeping
   `Q` strictly below the restart radius;
4. apply the selected weighted strong derivative theorem at elapsed time `q`;
5. compose with the physical-time shift `r ↦ r - t₁`;
6. use selected/old weighted-state equality on a neighborhood of `t`;
7. transport the derivative by `EventuallyEq`.

Thus all three global terminal physical fourth-radial coordinates possess
strong Fourier `L²` derivatives at every strict preterminal time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedOldDerivativeClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2500000

/--
The cutoff-independent terminal physical `q² û_j` strong derivative datum is
closed outright from the selected weighted derivative and local selected/old
agreement.
-/
theorem h3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertDerivativeAtEndpoint_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertDerivativeAtEndpoint
      hH3 hClass := by

  intro t ht

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

  /-
  Slide the anchor forward by a positive amount `δ` small enough that the new
  elapsed target lies at most at half the restart radius.
  -/
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

  let W : Fin 3 → H3FourierComplexL2 :=
    fun j =>
      h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
        hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

  refine
    ⟨
      W,
      ?_
    ⟩

  intro j

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j

  let Vselected :
      ℝ → H3FourierComplexL2 :=
    fun r =>
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        Vclosed
        (r - t₁)

  let Vphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j

  have hRelative :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_hasDerivAt
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
        Vselected
        (W j)
        t := by

    have hComp :=
      hRelative.scomp
        t
        hShift

    dsimp only [Vselected, Vclosed, W, qSlab, q] at hComp ⊢

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
      Vphysical =ᶠ[𝓝 t] Vselected := by

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

    let rSlab :
        Set.Icc (Q / 2) Q :=
      ⟨r - t₁, hrSlab⟩

    have hBridge :=
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_eq_terminalPhysicalFourthRadialL2At
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
        Vphysical r
          =
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass hrClass j := by
      dsimp only [Vphysical]
      exact
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
          hH3 hClass hrClass j

    have hSelectedAt :
        Vselected r
          =
        Vclosed rSlab := by

      dsimp only [Vselected]

      rw [
        Set.IccExtend_of_mem
          (by linarith : Q / 2 ≤ Q)
          Vclosed
          hrSlab
      ]

    calc
      Vphysical r
          =
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass hrClass j :=
        hPhysicalAt
      _ =
        h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
          hNSShort ht₁ hE hTail₁ hQ hQR j rSlab := by
        exact hBridge.symm
      _ =
        Vselected r := by
        exact hSelectedAt.symm

  have hPhysicalDerivative :
      HasDerivAt
        Vphysical
        (W j)
        t :=
    hSelectedAbsolute.congr_of_eventuallyEq
      hEventuallyEq

  dsimp only [Vphysical] at hPhysicalDerivative ⊢

  exact hPhysicalDerivative

end

end Euclidean
end Bridge
end PrimeTensor
