import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Closure
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# C¹ regularity of the physical top-tail weighted Hilbert path

The selected weighted Fourier `L²` path is now known to be `C¹` on every
positive compact restart slab.  The global physical fourth-radial path

    q² û_j(t)

agrees with that selected path on a neighborhood of every strict preterminal
time.  Therefore the entire `C¹` germ, not merely the first derivative value,
transports to the physical path.

A fixed sharp radial cutoff is a continuous linear restriction map.  Composing
the physical `C¹` coordinate paths with that restriction and then taking
Hilbert norm squares preserves `C¹`.  Summing the three coordinates gives
`C¹` regularity of every natural sharp top-dissipation radial-tail scalar path
on `(a,T)`.

Consequently the ordinary derivative of every natural tail is continuous on
the strict interval and hence interval-integrable on every compact strict
subinterval.  This closes the local derivative-integrability condition in the
one-sided localized-PDE continuation criterion without introducing any new
estimate or endpoint hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedOldRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-! ## Physical fourth-radial coordinate is locally C¹ -/

/--
At every strict physical time, one global physical fourth-radial Fourier
coordinate `q² û_j` is `C¹` as an `H3FourierComplexL2`-valued path.
-/
theorem h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_contDiffAt_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ContDiffAt ℝ 1
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
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

  have hqR :
      q ≤ R := by
    exact
      hqRHalf.trans
        (by linarith [hR])

  have htq :
      t₁ + q = t := by
    dsimp only [q]
    ring

  have hEnd :
      t₁ + q < S := by
    rw [htq]
    exact htS

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

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j

  let Vrelative :
      ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      (by linarith : Q / 2 ≤ Q)
      Vclosed

  have hRelativeC1 :
      ContDiffOn ℝ 1
        Vrelative
        (Set.Ioo (Q / 2) Q) := by

    simpa only [Vrelative, Vclosed] using
      (
        h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_contDiffOn_one
          hNSShort ht₁ hE hTail₁ hQ hQR j
      )

  have hRelativeAt :
      ContDiffAt ℝ 1 Vrelative q :=
    hRelativeC1.contDiffAt
      (Ioo_mem_nhds
        hqLower
        hqUpper)

  let shift : ℝ → ℝ :=
    fun r : ℝ => r - t₁

  have hShiftC1 :
      ContDiffAt ℝ 1 shift t := by

    have hShiftGlobal :
        ContDiff ℝ 1 shift := by
      dsimp only [shift]
      exact
        contDiff_id.sub
          contDiff_const

    exact
      hShiftGlobal.contDiffAt

  have hRelativeAtShift :
      ContDiffAt ℝ 1
        Vrelative
        (shift t) := by
    simpa only [shift, q] using
      hRelativeAt

  let Vselected :
      ℝ → H3FourierComplexL2 :=
    Vrelative ∘ shift

  have hSelectedC1 :
      ContDiffAt ℝ 1 Vselected t := by

    have hComp :=
      hRelativeAtShift.comp
        t
        hShiftC1

    simpa only [Vselected] using
      hComp

  let Vphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j

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

      dsimp only [
        Vselected,
        Function.comp_apply,
        Vrelative,
        shift
      ]

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

  have hPhysicalC1 :
      ContDiffAt ℝ 1 Vphysical t :=
    hSelectedC1.congr_of_eventuallyEq
      hEventuallyEq

  simpa only [Vphysical] using
    hPhysicalC1

/-! ## Natural sharp-tail scalar path is C¹ -/

/--
Every natural sharp top-dissipation radial-tail scalar path is `C¹` at every
strict preterminal time.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_contDiffAt_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ)
    (ht : t ∈ Set.Ioo a T) :
    ContDiffAt ℝ 1
      (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n)
      t := by

  let R : ℝ :=
    (n : ℝ) + 1

  have hEach :
      ∀ j : Fin 3,
        ContDiffAt ℝ 1
          (fun r : ℝ =>
            (
              ‖h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass R j r‖ : ℝ
            ) ^ 2)
          t := by

    intro j

    have hGlobal :
        ContDiffAt ℝ 1
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          t :=
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_contDiffAt_one
        hH3 hClass ht j

    have hRestricted :
        ContDiffAt ℝ 1
          (h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
            hH3 hClass R j)
          t := by

      unfold
        h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path

      have hComp :=
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictCLM R
        ).contDiff.contDiffAt.comp
          t
          hGlobal

      simpa only [Function.comp_def] using
        hComp

    exact
      hRestricted.norm_sq ℂ

  have hSum :
      ContDiffAt ℝ 1
        (fun r : ℝ =>
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass R j r‖ : ℝ
            ) ^ 2)
        t := by

    apply
      ContDiffAt.sum

    intro j hj

    exact
      hEach j

  rw [
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq_sum_norm_sq_restricted
      hH3 hClass n
  ]

  simpa only [R] using
    hSum

/--
Every natural sharp top-dissipation radial-tail scalar path is `C¹` on the
whole strict energy-class interval.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailPath_contDiffOn_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ) :
    ContDiffOn ℝ 1
      (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass n)
      (Set.Ioo a T) := by

  rw [
    isOpen_Ioo.contDiffOn_iff
  ]

  intro t ht

  exact
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath_contDiffAt_one
      hH3 hClass n ht

/-! ## Local derivative integrability is closed -/

/--
The ordinary derivative of every natural sharp top-dissipation radial-tail
path is interval-integrable on every compact strict subinterval of `(a,T)`.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable
      hH3 hClass := by

  intro n s hs t ht hst

  let F : ℝ → ℝ :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath
      hH3 hClass n

  have hC1 :
      ContDiffOn ℝ 1
        F
        (Set.Ioo a T) := by

    dsimp only [F]

    exact
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath_contDiffOn_one
        hH3 hClass n

  have hCriterion :
      ContDiffOn ℝ 1
          F
          (Set.Ioo a T)
        ↔
      DifferentiableOn ℝ
          F
          (Set.Ioo a T)
        ∧
      ContinuousOn
          (deriv F)
          (Set.Ioo a T) := by

    simpa using
      (
        contDiffOn_succ_iff_deriv_of_isOpen
          (𝕜 := ℝ)
          (f := F)
          (s := Set.Ioo a T)
          (n := 0)
          isOpen_Ioo
      )

  have hDerivContinuous :
      ContinuousOn
        (deriv F)
        (Set.Ioo a T) :=
    (hCriterion.1 hC1).2

  have hIccSubset :
      Set.Icc s t
        ⊆
      Set.Ioo a T := by

    intro r hr

    exact
      ⟨
        lt_of_lt_of_le
          hs.1
          hr.1,
        lt_of_le_of_lt
          hr.2
          ht.2
      ⟩

  apply
    ContinuousOn.intervalIntegrable

  rw [
    uIcc_of_le hst
  ]

  exact
    hDerivContinuous.mono
      hIccSubset

end

end Euclidean
end Bridge
end PrimeTensor
