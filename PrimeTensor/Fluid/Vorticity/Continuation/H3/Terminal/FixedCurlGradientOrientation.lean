import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedCurlGradientSamePoint

/-!
# Fixed orientation of the terminal curl / gradient pathology

The fixed same-point curl/gradient theorem still records the curl only through
its absolute value.  Thus the selected fixed curl component could, a priori,
alternate sign while its magnitude diverges.

There are only two orientations.  This file proves a generic terminal
finite-choice lemma: if `|H|` and `|F|` are jointly cofinally unbounded at the
same spacetime points, then one fixed orientation of `H` is jointly cofinally
unbounded with `|F|`.

The orientation is represented by a two-valued type:

* `positive`: oriented value `H`,
* `negative`: oriented value `-H`.

Consequently, under hypothetical nonextension, one fixed structurally valid
curl/constituent-gradient pair admits a fixed curl orientation and a localized
terminal sequence on which

    n < orientedCurl,
    n < |fixedGradient|,

with both quantities tending to `+∞`.

For the curl itself this means either the fixed component tends to `+∞` or it
tends to `-∞` along the selected sequence.  No sign claim is made for the
constituent gradient in this increment.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Orientation -/

inductive H3TerminalOrientation
  | positive
  | negative
  deriving DecidableEq

def h3TerminalOrientedValue :
    H3TerminalOrientation → ℝ → ℝ
  | .positive, z => z
  | .negative, z => -z

@[simp]
theorem h3TerminalOrientedValue_positive
    (z : ℝ) :
    h3TerminalOrientedValue
      H3TerminalOrientation.positive z = z := by
  rfl

@[simp]
theorem h3TerminalOrientedValue_negative
    (z : ℝ) :
    h3TerminalOrientedValue
      H3TerminalOrientation.negative z = -z := by
  rfl

/-! ## Generic oriented same-point predicates -/

def H3TerminalScalarOrientedPairSamePointCofinallyUnbounded
    (a T : ℝ)
    (H F : ℝ → Point3 → ℝ)
    (s : H3TerminalOrientation) : Prop :=
  ∀
    c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃
          t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ∃ x : Point3,
              M < abs (F t x)
                ∧
              M <
                h3TerminalOrientedValue
                  s
                  (H t x)

def H3TerminalScalarOrientedPairSamePointBlowupSequence
    (a T : ℝ)
    (H F : ℝ → Point3 → ℝ)
    (s : H3TerminalOrientation) : Prop :=
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
          (n : ℝ) < abs (F (τ n) (x n))
            ∧
          (n : ℝ) <
            h3TerminalOrientedValue
              s
              (H (τ n) (x n))
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ =>
          abs (F (τ n) (x n)))
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              s
              (H (τ n) (x n))
        )
        atTop
        atTop

/-! ## Absolute-value pair forces one fixed orientation -/

/--
If `|H|` and `|F|` are jointly cofinally unbounded at the same spacetime
points, then either `H` or `-H` is jointly cofinally unbounded with `|F|`.
-/
theorem exists_orientation_of_samePoint_absPair_cofinallyUnbounded
    {a T : ℝ}
    {H F : ℝ → Point3 → ℝ}
    (hPair :
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T H F) :
    ∃ s : H3TerminalOrientation,
      H3TerminalScalarOrientedPairSamePointCofinallyUnbounded
        a T H F s := by

  classical

  by_cases hPos :
      H3TerminalScalarOrientedPairSamePointCofinallyUnbounded
        a T H F H3TerminalOrientation.positive

  · exact
      ⟨
        H3TerminalOrientation.positive,
        hPos
      ⟩

  have hPosBound := hPos

  unfold H3TerminalScalarOrientedPairSamePointCofinallyUnbounded at hPosBound

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

  unfold H3TerminalScalarOrientedPairSamePointCofinallyUnbounded

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
      hAbsH,
      hAbsF
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

  have hM₀ltF :
      M₀ < abs (F t x) :=
    lt_of_le_of_lt
      hM₀leK
      hAbsF

  have hHle :
      H t x ≤ M₀ := by

    have hAt :=
      hFailPos
        t ht₀ x

    simpa only [
      h3TerminalOrientedValue_positive
    ] using
      hAt hM₀ltF

  have hHneg :
      H t x < 0 := by

    by_contra hNotNeg

    have hHnonneg :
        0 ≤ H t x :=
      le_of_not_gt
        hNotNeg

    have hAbsEq :
        abs (H t x) = H t x :=
      abs_of_nonneg hHnonneg

    have hAbsLe :
        abs (H t x) ≤ K := by

      rw [hAbsEq]

      exact
        le_trans
          hHle
          hM₀leK

    exact
      (not_lt_of_ge hAbsLe)
        hAbsH

  have hNegLarge :
      K < - H t x := by

    rw [abs_of_neg hHneg] at hAbsH

    exact
      hAbsH

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
        hAbsF

  · simpa only [
      h3TerminalOrientedValue_negative
    ] using
      (
        lt_of_le_of_lt
          hMleK
          hNegLarge
      )

/-! ## Oriented sequence extraction -/

private theorem tendsto_terminal_of_oriented_localization
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

private theorem tendsto_atTop_of_natCast_lt_oriented
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

private theorem oriented_samePoint_blowupSequence_of_cofinallyUnbounded
    {a T : ℝ}
    {H F : ℝ → Point3 → ℝ}
    {s : H3TerminalOrientation}
    (haT : a < T)
    (hPair :
      H3TerminalScalarOrientedPairSamePointCofinallyUnbounded
        a T H F s) :
    H3TerminalScalarOrientedPairSamePointBlowupSequence
      a T H F s := by

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
            (n : ℝ) < abs (F t x)
              ∧
            (n : ℝ) <
              h3TerminalOrientedValue
                s
                (H t x) := by

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
        hF,
        hH
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
        hF,
        hH
      ⟩

  choose τ x hτ using
    hChoice

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) :=
    tendsto_terminal_of_oriented_localization
      (fun n => (hτ n).2.1)

  have hFTendsto :
      Tendsto
        (
          fun n : ℕ =>
            abs (F (τ n) (x n))
        )
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_oriented
      (fun n => (hτ n).2.2.1)

  have hHTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              s
              (H (τ n) (x n))
        )
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_oriented
      (fun n => (hτ n).2.2.2)

  exact
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hFTendsto,
      hHTendsto
    ⟩

/-! ## Concrete fixed curl / constituent-gradient fields -/

private noncomputable def orientedVorticityXField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    realVorticityX
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x

private noncomputable def orientedVorticityYField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    realVorticityY
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x

private noncomputable def orientedVorticityZField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    realVorticityZ
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x

private noncomputable def orientedGradientField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i j : PrimeTensor.Axis Depth.three) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    spatial3.d
      i
      (
        fun y =>
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u t y
          ).component j
      )
      x

def H3TerminalOrientedVorticityXGradientYZBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (s : H3TerminalOrientation) : Prop :=
  H3TerminalScalarOrientedPairSamePointBlowupSequence
    a T
    (orientedVorticityXField u)
    (orientedGradientField u yAxis zAxis)
    s

def H3TerminalOrientedVorticityXGradientZYBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (s : H3TerminalOrientation) : Prop :=
  H3TerminalScalarOrientedPairSamePointBlowupSequence
    a T
    (orientedVorticityXField u)
    (orientedGradientField u zAxis yAxis)
    s

def H3TerminalOrientedVorticityYGradientZXBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (s : H3TerminalOrientation) : Prop :=
  H3TerminalScalarOrientedPairSamePointBlowupSequence
    a T
    (orientedVorticityYField u)
    (orientedGradientField u zAxis xAxis)
    s

def H3TerminalOrientedVorticityYGradientXZBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (s : H3TerminalOrientation) : Prop :=
  H3TerminalScalarOrientedPairSamePointBlowupSequence
    a T
    (orientedVorticityYField u)
    (orientedGradientField u xAxis zAxis)
    s

def H3TerminalOrientedVorticityZGradientXYBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (s : H3TerminalOrientation) : Prop :=
  H3TerminalScalarOrientedPairSamePointBlowupSequence
    a T
    (orientedVorticityZField u)
    (orientedGradientField u xAxis yAxis)
    s

def H3TerminalOrientedVorticityZGradientYXBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (s : H3TerminalOrientation) : Prop :=
  H3TerminalScalarOrientedPairSamePointBlowupSequence
    a T
    (orientedVorticityZField u)
    (orientedGradientField u yAxis xAxis)
    s

/-! ## Oriented fixed-pair terminal sequence -/

/--
Under hypothetical nonextension, one structurally valid fixed curl/gradient
pair admits a fixed curl orientation and a common terminal spacetime sequence
on which the oriented curl and the fixed gradient magnitude both tend to
`+∞`.
-/
theorem fixed_curl_constituentGradient_oriented_samePoint_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalOrientedVorticityXGradientYZBlowupSequence
          u a T s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalOrientedVorticityXGradientZYBlowupSequence
          u a T s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalOrientedVorticityYGradientZXBlowupSequence
          u a T s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalOrientedVorticityYGradientXZBlowupSequence
          u a T s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalOrientedVorticityZGradientXYBlowupSequence
          u a T s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalOrientedVorticityZGradientYXBlowupSequence
          u a T s
    ) := by

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
        (orientedVorticityXField u)
        (orientedGradientField u yAxis zAxis)
      at hPair

    obtain ⟨s, hs⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    exact
      Or.inl
        ⟨
          s,
          oriented_samePoint_blowupSequence_of_cofinallyUnbounded
            hClass.terminal_start.2
            hs
        ⟩

  · have hPair := h2

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (orientedVorticityXField u)
        (orientedGradientField u zAxis yAxis)
      at hPair

    obtain ⟨s, hs⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    exact
      Or.inr
        (
          Or.inl
            ⟨
              s,
              oriented_samePoint_blowupSequence_of_cofinallyUnbounded
                hClass.terminal_start.2
                hs
            ⟩
        )

  · have hPair := h3

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (orientedVorticityYField u)
        (orientedGradientField u zAxis xAxis)
      at hPair

    obtain ⟨s, hs⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    exact
      Or.inr
        (
          Or.inr
            (
              Or.inl
                ⟨
                  s,
                  oriented_samePoint_blowupSequence_of_cofinallyUnbounded
                    hClass.terminal_start.2
                    hs
                ⟩
            )
        )

  · have hPair := h4

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (orientedVorticityYField u)
        (orientedGradientField u xAxis zAxis)
      at hPair

    obtain ⟨s, hs⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  Or.inl
                    ⟨
                      s,
                      oriented_samePoint_blowupSequence_of_cofinallyUnbounded
                        hClass.terminal_start.2
                        hs
                    ⟩
                )
            )
        )

  · have hPair := h5

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (orientedVorticityZField u)
        (orientedGradientField u xAxis yAxis)
      at hPair

    obtain ⟨s, hs⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  Or.inr
                    (
                      Or.inl
                        ⟨
                          s,
                          oriented_samePoint_blowupSequence_of_cofinallyUnbounded
                            hClass.terminal_start.2
                            hs
                        ⟩
                    )
                )
            )
        )

  · have hPair := h6

    change
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T
        (orientedVorticityZField u)
        (orientedGradientField u yAxis xAxis)
      at hPair

    obtain ⟨s, hs⟩ :=
      exists_orientation_of_samePoint_absPair_cofinallyUnbounded
        hPair

    exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  Or.inr
                    (
                      Or.inr
                        ⟨
                          s,
                          oriented_samePoint_blowupSequence_of_cofinallyUnbounded
                            hClass.terminal_start.2
                            hs
                        ⟩
                    )
                )
            )
        )

/-! ## Neutral package -/

/--
Neutral formulation with a fixed structural pair and fixed curl orientation.
-/
theorem smoothContinuationExtension_or_fixed_orientedCurl_constituentGradient_samePoint_blowupSequence
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
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalOrientedVorticityXGradientYZBlowupSequence
            u a T s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalOrientedVorticityXGradientZYBlowupSequence
            u a T s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalOrientedVorticityYGradientZXBlowupSequence
            u a T s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalOrientedVorticityYGradientXZBlowupSequence
            u a T s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalOrientedVorticityZGradientXYBlowupSequence
            u a T s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalOrientedVorticityZGradientYXBlowupSequence
            u a T s
      )
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          fixed_curl_constituentGradient_oriented_samePoint_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
