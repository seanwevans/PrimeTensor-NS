import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedCurlGradientOrientation

/-!
# Fixed orientations for both members of the terminal curl / gradient pair

The preceding theorem fixes

* one structurally valid curl / constituent-gradient pair,
* one common terminal spacetime sequence,
* one fixed orientation of the curl,

while the constituent gradient is still recorded only through its magnitude.

There are only two gradient orientations.  The same finite-choice argument
used for the curl fixes one of them without losing the already-fixed curl
orientation or the same-point coupling.

This file packages the six structural possibilities into one finite type, so
the conclusion becomes:

    ∃ pair, curlOrientation, gradientOrientation, terminal sequence,

on which both oriented real quantities exceed `n` and both tend to `+∞`.

Thus, along one common terminal spacetime sequence, the fixed curl component
tends to one of `±∞` and its fixed constituent derivative also tends to one of
`±∞`.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## The six structural curl / constituent-gradient pairs -/

inductive H3TerminalCurlGradientPair
  | x_yz
  | x_zy
  | y_zx
  | y_xz
  | z_xy
  | z_yx
  deriving DecidableEq

noncomputable def h3TerminalCurlFieldForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    H3TerminalCurlGradientPair → ℝ → Point3 → ℝ
  | .x_yz, t, x =>
      realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
  | .x_zy, t, x =>
      realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
  | .y_zx, t, x =>
      realVorticityY
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
  | .y_xz, t, x =>
      realVorticityY
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
  | .z_xy, t, x =>
      realVorticityZ
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
  | .z_yx, t, x =>
      realVorticityZ
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x

def h3TerminalGradientDerivativeAxisForPair :
    H3TerminalCurlGradientPair →
      PrimeTensor.Axis Depth.three
  | .x_yz => yAxis
  | .x_zy => zAxis
  | .y_zx => zAxis
  | .y_xz => xAxis
  | .z_xy => xAxis
  | .z_yx => yAxis

def h3TerminalGradientComponentAxisForPair :
    H3TerminalCurlGradientPair →
      PrimeTensor.Axis Depth.three
  | .x_yz => zAxis
  | .x_zy => yAxis
  | .y_zx => xAxis
  | .y_xz => zAxis
  | .z_xy => yAxis
  | .z_yx => xAxis

noncomputable def h3TerminalGradientFieldForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    spatial3.d
      (h3TerminalGradientDerivativeAxisForPair p)
      (
        fun y =>
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u t y
          ).component
            (h3TerminalGradientComponentAxisForPair p)
      )
      x

/-! ## Double orientation -/

def H3TerminalScalarDoubleOrientedPairSamePointCofinallyUnbounded
    (a T : ℝ)
    (H F : ℝ → Point3 → ℝ)
    (sH sF : H3TerminalOrientation) : Prop :=
  ∀
    c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃
          t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ∃ x : Point3,
              M <
                h3TerminalOrientedValue
                  sH
                  (H t x)
                ∧
              M <
                h3TerminalOrientedValue
                  sF
                  (F t x)

def H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
    (a T : ℝ)
    (H F : ℝ → Point3 → ℝ)
    (sH sF : H3TerminalOrientation) : Prop :=
  ∃
    τ : ℕ → ℝ,
    ∃ x : ℕ → Point3,
      (
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ) <
            h3TerminalOrientedValue
              sH
              (H (τ n) (x n))
            ∧
          (n : ℝ) <
            h3TerminalOrientedValue
              sF
              (F (τ n) (x n))
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sH
              (H (τ n) (x n))
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sF
              (F (τ n) (x n))
        )
        atTop
        atTop

/--
Once the orientation of `H` is fixed and `|F|` is jointly cofinally unbounded
with that oriented `H`, one fixed orientation of `F` can also be chosen.
-/
theorem exists_second_orientation_of_oriented_absPair_cofinallyUnbounded
    {a T : ℝ}
    {H F : ℝ → Point3 → ℝ}
    {sH : H3TerminalOrientation}
    (hPair :
      H3TerminalScalarOrientedPairSamePointCofinallyUnbounded
        a T H F sH) :
    ∃ sF : H3TerminalOrientation,
      H3TerminalScalarDoubleOrientedPairSamePointCofinallyUnbounded
        a T H F sH sF := by

  classical

  by_cases hPos :
      H3TerminalScalarDoubleOrientedPairSamePointCofinallyUnbounded
        a T H F
        sH
        H3TerminalOrientation.positive

  · exact
      ⟨
        H3TerminalOrientation.positive,
        hPos
      ⟩

  have hPosBound := hPos

  unfold H3TerminalScalarDoubleOrientedPairSamePointCofinallyUnbounded at hPosBound

  push Not at hPosBound

  obtain
    ⟨
      c₀,
      hc₀,
      M₀,
      hFailPos
    ⟩ :=
    hPosBound

  refine
    ⟨
      H3TerminalOrientation.negative,
      ?_
    ⟩

  unfold H3TerminalScalarDoubleOrientedPairSamePointCofinallyUnbounded

  intro c hc M

  let d : ℝ :=
    max c c₀

  have hd :
      d ∈ Set.Ioo a T := by

    constructor

    · dsimp only [d]

      exact
        lt_of_lt_of_le
          hc.1
          (le_max_left _ _)

    · dsimp only [d]

      exact
        max_lt
          hc.2
          hc₀.2

  let K : ℝ :=
    max
      (max M M₀)
      0

  obtain
    ⟨
      t,
      ht,
      x,
      hAbsF,
      hOrientedH
    ⟩ :=
    hPair
      d hd K

  have htC :
      t ∈ Set.Ioo c T := by

    exact
      ⟨
        lt_of_le_of_lt
          (by
            dsimp only [d]
            exact le_max_left c c₀)
          ht.1,
        ht.2
      ⟩

  have ht₀ :
      t ∈ Set.Ioo c₀ T := by

    exact
      ⟨
        lt_of_le_of_lt
          (by
            dsimp only [d]
            exact le_max_right c c₀)
          ht.1,
        ht.2
      ⟩

  have hMleK :
      M ≤ K := by

    dsimp only [K]

    exact
      le_trans
        (le_max_left M M₀)
        (le_max_left _ _)

  have hM₀leK :
      M₀ ≤ K := by

    dsimp only [K]

    exact
      le_trans
        (le_max_right M M₀)
        (le_max_left _ _)

  have hKnonneg :
      0 ≤ K := by

    dsimp only [K]

    exact
      le_max_right _ _

  have hM₀ltH :
      M₀ <
        h3TerminalOrientedValue
          sH
          (H t x) :=
    lt_of_le_of_lt
      hM₀leK
      hOrientedH

  have hFle :
      F t x ≤ M₀ := by

    have hAt :=
      hFailPos
        t ht₀ x

    simpa only [
      h3TerminalOrientedValue_positive
    ] using
      hAt hM₀ltH

  have hFneg :
      F t x < 0 := by

    by_contra hNotNeg

    have hFnonneg :
        0 ≤ F t x :=
      le_of_not_gt
        hNotNeg

    have hAbsEq :
        abs (F t x) = F t x :=
      abs_of_nonneg hFnonneg

    have hAbsLe :
        abs (F t x) ≤ K := by

      rw [hAbsEq]

      exact
        le_trans
          hFle
          hM₀leK

    exact
      (not_lt_of_ge hAbsLe)
        hAbsF

  have hNegLarge :
      K < - F t x := by

    rw [abs_of_neg hFneg] at hAbsF

    exact
      hAbsF

  refine
    ⟨
      t,
      htC,
      x,
      ?_,
      ?_
    ⟩

  · exact
      lt_of_le_of_lt
        hMleK
        hOrientedH

  · simpa only [
      h3TerminalOrientedValue_negative
    ] using
      (
        lt_of_le_of_lt
          hMleK
          hNegLarge
      )

/-! ## Sequence extraction -/

private theorem tendsto_terminal_of_double_oriented_localization
    {T : ℝ}
    {τ : ℕ → ℝ}
    (hτ :
      ∀ n : ℕ,
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T) :
    Tendsto τ atTop (𝓝 T) := by

  rw [Metric.tendsto_atTop]

  intro ε hε

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt
      (1 / ε)

  refine
    ⟨
      N,
      ?_
    ⟩

  intro n hn

  have hDenN :
      0 < (N : ℝ) + 1 := by
    positivity

  have hInv :
      (1 : ℝ) / ((n : ℝ) + 1)
        ≤
      1 / ((N : ℝ) + 1) := by

    exact
      one_div_le_one_div_of_le
        hDenN
        (by
          have hCast :
              (N : ℝ) ≤ n := by
            exact_mod_cast hn
          linarith)

  have hSmallN :
      1 / ((N : ℝ) + 1) < ε := by

    have hNPlus :
        1 / ε < (N : ℝ) + 1 := by
      linarith [hN]

    have hMul :
        1 < ((N : ℝ) + 1) * ε :=
      (div_lt_iff₀ hε).1
        hNPlus

    exact
      (div_lt_iff₀ hDenN).2
        (by
          simpa only [mul_comm, one_mul] using hMul)

  have hSmall :
      (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    lt_of_le_of_lt
      hInv
      hSmallN

  have hLower :=
    (hτ n).1

  have hUpper :=
    (hτ n).2

  rw [Real.dist_eq]

  have hDiffNonpos :
      τ n - T ≤ 0 := by
    linarith

  rw [abs_of_nonpos hDiffNonpos]

  linarith

private theorem tendsto_atTop_of_natCast_lt_double_oriented
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        (n : ℝ) < f n) :
    Tendsto f atTop atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt
      M

  filter_upwards
    [eventually_ge_atTop N]
    with n hn

  have hNat :
      M < (n : ℝ) := by

    exact
      lt_of_lt_of_le
        hN
        (by exact_mod_cast hn)

  exact
    le_of_lt
      (
        lt_trans
          hNat
          (hf n)
      )

private theorem double_oriented_samePoint_blowupSequence_of_cofinallyUnbounded
    {a T : ℝ}
    {H F : ℝ → Point3 → ℝ}
    {sH sF : H3TerminalOrientation}
    (haT : a < T)
    (hPair :
      H3TerminalScalarDoubleOrientedPairSamePointCofinallyUnbounded
        a T H F sH sF) :
    H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
      a T H F sH sF := by

  have hChoice :
      ∀ n : ℕ,
        ∃
          t : ℝ,
          ∃ x : Point3,
            t ∈ Set.Ioo a T
              ∧
            t ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            (n : ℝ) <
              h3TerminalOrientedValue
                sH
                (H t x)
              ∧
            (n : ℝ) <
              h3TerminalOrientedValue
                sF
                (F t x) := by

    intro n

    let ε : ℝ :=
      (1 : ℝ) / ((n : ℝ) + 1)

    have hε :
        0 < ε := by

      dsimp only [ε]

      positivity

    let l : ℝ :=
      max
        a
        (T - ε)

    have hlT :
        l < T := by

      dsimp only [l]

      exact
        max_lt
          haT
          (by linarith)

    let c : ℝ :=
      h3BKMKineticTailMidpoint
        l
        T

    have hcL :
        c ∈ Set.Ioo l T := by

      dsimp only [c]

      exact
        h3BKMKineticTailMidpoint_mem_Ioo
          hlT

    have hc :
        c ∈ Set.Ioo a T := by

      exact
        ⟨
          lt_of_le_of_lt
            (le_max_left a (T - ε))
            hcL.1,
          hcL.2
        ⟩

    have hcNear :
        T - ε < c := by

      exact
        lt_of_le_of_lt
          (le_max_right a (T - ε))
          hcL.1

    obtain
      ⟨
        t,
        ht,
        x,
        hH,
        hF
      ⟩ :=
      hPair
        c hc
        (n : ℝ)

    exact
      ⟨
        t,
        x,
        ⟨
          lt_trans hc.1 ht.1,
          ht.2
        ⟩,
        ⟨
          lt_trans hcNear ht.1,
          ht.2
        ⟩,
        hH,
        hF
      ⟩

  choose τ x hτ using
    hChoice

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) :=
    tendsto_terminal_of_double_oriented_localization
      (fun n => (hτ n).2.1)

  have hHTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sH
              (H (τ n) (x n))
        )
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_double_oriented
      (fun n => (hτ n).2.2.1)

  have hFTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sF
              (F (τ n) (x n))
        )
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_double_oriented
      (fun n => (hτ n).2.2.2)

  exact
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hHTendsto,
      hFTendsto
    ⟩

/-! ## Fixed double-oriented pair under hypothetical nonextension -/

/--
Hypothetical nonextension forces one of the six structurally valid fixed
curl/constituent-gradient pairs, one fixed orientation for the curl, one fixed
orientation for the constituent gradient, and one common localized terminal
spacetime sequence on which both oriented quantities tend to `+∞`.
-/
theorem fixed_curl_constituentGradient_doubleOriented_samePoint_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      p : H3TerminalCurlGradientPair,
      ∃
        sCurl sGradient : H3TerminalOrientation,
        H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
          a T
          (h3TerminalCurlFieldForPair u p)
          (h3TerminalGradientFieldForPair u p)
          sCurl
          sGradient := by

  rcases
      fixed_curl_constituentGradient_samePoint_cofinallyUnbounded_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    with h1 | h2 | h3 | h4 | h5 | h6

  · have hPair := h1

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (
          fun t x =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              yAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component zAxis
              )
              x
        )
      at hPair

    obtain ⟨sCurl, hCurl⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    obtain ⟨sGradient, hBoth⟩ :=
      exists_second_orientation_of_oriented_absPair_cofinallyUnbounded
        hCurl

    refine
      ⟨
        H3TerminalCurlGradientPair.x_yz,
        sCurl,
        sGradient,
        ?_
      ⟩

    change
      H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
        a T
        (
          fun t x =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              yAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component zAxis
              )
              x
        )
        sCurl
        sGradient

    exact
      double_oriented_samePoint_blowupSequence_of_cofinallyUnbounded
        hClass.terminal_start.2
        hBoth

  · have hPair := h2

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (
          fun t x =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              zAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component yAxis
              )
              x
        )
      at hPair

    obtain ⟨sCurl, hCurl⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    obtain ⟨sGradient, hBoth⟩ :=
      exists_second_orientation_of_oriented_absPair_cofinallyUnbounded
        hCurl

    refine
      ⟨
        H3TerminalCurlGradientPair.x_zy,
        sCurl,
        sGradient,
        ?_
      ⟩

    change
      H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
        a T
        (
          fun t x =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              zAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component yAxis
              )
              x
        )
        sCurl
        sGradient

    exact
      double_oriented_samePoint_blowupSequence_of_cofinallyUnbounded
        hClass.terminal_start.2
        hBoth

  · have hPair := h3

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (
          fun t x =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              zAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component xAxis
              )
              x
        )
      at hPair

    obtain ⟨sCurl, hCurl⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    obtain ⟨sGradient, hBoth⟩ :=
      exists_second_orientation_of_oriented_absPair_cofinallyUnbounded
        hCurl

    refine
      ⟨
        H3TerminalCurlGradientPair.y_zx,
        sCurl,
        sGradient,
        ?_
      ⟩

    change
      H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
        a T
        (
          fun t x =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              zAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component xAxis
              )
              x
        )
        sCurl
        sGradient

    exact
      double_oriented_samePoint_blowupSequence_of_cofinallyUnbounded
        hClass.terminal_start.2
        hBoth

  · have hPair := h4

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (
          fun t x =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              xAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component zAxis
              )
              x
        )
      at hPair

    obtain ⟨sCurl, hCurl⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    obtain ⟨sGradient, hBoth⟩ :=
      exists_second_orientation_of_oriented_absPair_cofinallyUnbounded
        hCurl

    refine
      ⟨
        H3TerminalCurlGradientPair.y_xz,
        sCurl,
        sGradient,
        ?_
      ⟩

    change
      H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
        a T
        (
          fun t x =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              xAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component zAxis
              )
              x
        )
        sCurl
        sGradient

    exact
      double_oriented_samePoint_blowupSequence_of_cofinallyUnbounded
        hClass.terminal_start.2
        hBoth

  · have hPair := h5

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (
          fun t x =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              xAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component yAxis
              )
              x
        )
      at hPair

    obtain ⟨sCurl, hCurl⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    obtain ⟨sGradient, hBoth⟩ :=
      exists_second_orientation_of_oriented_absPair_cofinallyUnbounded
        hCurl

    refine
      ⟨
        H3TerminalCurlGradientPair.z_xy,
        sCurl,
        sGradient,
        ?_
      ⟩

    change
      H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
        a T
        (
          fun t x =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              xAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component yAxis
              )
              x
        )
        sCurl
        sGradient

    exact
      double_oriented_samePoint_blowupSequence_of_cofinallyUnbounded
        hClass.terminal_start.2
        hBoth

  · have hPair := h6

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (
          fun t x =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              yAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component xAxis
              )
              x
        )
      at hPair

    obtain ⟨sCurl, hCurl⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    obtain ⟨sGradient, hBoth⟩ :=
      exists_second_orientation_of_oriented_absPair_cofinallyUnbounded
        hCurl

    refine
      ⟨
        H3TerminalCurlGradientPair.z_yx,
        sCurl,
        sGradient,
        ?_
      ⟩

    change
      H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
        a T
        (
          fun t x =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        (
          fun t x =>
            spatial3.d
              yAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component xAxis
              )
              x
        )
        sCurl
        sGradient

    exact
      double_oriented_samePoint_blowupSequence_of_cofinallyUnbounded
        hClass.terminal_start.2
        hBoth

/-! ## Neutral package -/

/--
Neutral terminal formulation with one fixed structural pair and fixed
orientations for both the curl component and its constituent gradient entry.
-/
theorem smoothContinuationExtension_or_fixed_doubleOrientedCurlGradient_samePoint_blowupSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃
        p : H3TerminalCurlGradientPair,
        ∃
          sCurl sGradient : H3TerminalOrientation,
          H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
            a T
            (h3TerminalCurlFieldForPair u p)
            (h3TerminalGradientFieldForPair u p)
            sCurl
            sGradient
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          fixed_curl_constituentGradient_doubleOriented_samePoint_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
