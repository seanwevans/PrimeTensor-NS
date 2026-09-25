import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedCurlGradientPair

/-!
# Fixed curl / constituent-gradient divergence at the same spacetime points

The previous structural-pair theorem retains which fixed first derivative
belongs to the persistent fixed curl component, but its two cofinal
unboundedness statements may use different spacetime witnesses.

This file closes that gap.

For scalar fields `H = F - G`, if `H` is cofinally unbounded, then one of the
two fixed pairs `(H,F)` or `(H,G)` is jointly cofinally unbounded at the same
spacetime points.  Otherwise there are terminal tails and thresholds on which
neither constituent can be large together with `H`; choosing `H` larger than
both thresholds and their sum contradicts

    |H| = |F - G| ≤ |F| + |G|.

Applied to curl, hypothetical nonextension therefore forces one fixed
vorticity component and one fixed constituent first derivative to become
arbitrarily large together at the same spacetime points.

A second theorem extracts a standard terminal sequence `(τₙ,xₙ)` with

    T - 1/(n+1) < τₙ < T,

on which both fixed amplitudes exceed `n` and tend to `+∞`.

These remain necessary consequences conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Generic same-point pair predicates -/

def H3TerminalScalarPairSamePointCofinallyUnbounded
    (a T : ℝ)
    (H F : ℝ → Point3 → ℝ) : Prop :=
  ∀
    c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃
          t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ∃ x : Point3,
              M < abs (H t x)
                ∧
              M < abs (F t x)

def H3TerminalScalarPairSamePointBlowupSequence
    (a T : ℝ)
    (H F : ℝ → Point3 → ℝ) : Prop :=
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
          (n : ℝ) < abs (H (τ n) (x n))
            ∧
          (n : ℝ) < abs (F (τ n) (x n))
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ => abs (H (τ n) (x n)))
        atTop
        atTop
        ∧
      Tendsto
        (fun n : ℕ => abs (F (τ n) (x n)))
        atTop
        atTop

/-! ## Generic difference lemma -/

/--
If `H = F - G` is cofinally unbounded, then one fixed constituent is jointly
cofinally unbounded with `H` at the same spacetime points.
-/
theorem terminalScalarPairSamePoint_one_of_sub_pair_cofinallyUnbounded
    {a T : ℝ}
    {F G H : ℝ → Point3 → ℝ}
    (hH :
      H3TerminalScalarComponentCofinallyUnbounded
        a T H)
    (hEq :
      ∀ t : ℝ,
        ∀ x : Point3,
          H t x = F t x - G t x) :
    H3TerminalScalarPairSamePointCofinallyUnbounded
        a T H F
      ∨
    H3TerminalScalarPairSamePointCofinallyUnbounded
        a T H G := by

  classical

  by_cases hHF :
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T H F

  · exact Or.inl hHF

  by_cases hHG :
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T H G

  · exact Or.inr hHG

  exfalso

  have hHFBound := hHF
  have hHGBound := hHG

  unfold H3TerminalScalarPairSamePointCofinallyUnbounded at hHFBound
  unfold H3TerminalScalarPairSamePointCofinallyUnbounded at hHGBound

  push_neg at hHFBound
  push_neg at hHGBound

  obtain
    ⟨cF, hcF, MF, hFailF⟩ :=
    hHFBound

  obtain
    ⟨cG, hcG, MG, hFailG⟩ :=
    hHGBound

  let c : ℝ :=
    max cF cG

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hcF.1
          (le_max_left _ _)

    · dsimp only [c]

      exact
        max_lt
          hcF.2
          hcG.2

  let M : ℝ :=
    max
      (max MF MG)
      (MF + MG)

  obtain
    ⟨t, ht, x, hLargeH⟩ :=
    hH
      c hc M

  have htF :
      t ∈ Set.Ioo cF T := by

    exact
      ⟨
        lt_of_le_of_lt
          (by
            dsimp only [c]
            exact le_max_left cF cG)
          ht.1,
        ht.2
      ⟩

  have htG :
      t ∈ Set.Ioo cG T := by

    exact
      ⟨
        lt_of_le_of_lt
          (by
            dsimp only [c]
            exact le_max_right cF cG)
          ht.1,
        ht.2
      ⟩

  have hMF :
      MF ≤ M := by

    dsimp only [M]

    exact
      le_trans
        (le_max_left MF MG)
        (le_max_left _ _)

  have hMG :
      MG ≤ M := by

    dsimp only [M]

    exact
      le_trans
        (le_max_right MF MG)
        (le_max_left _ _)

  have hSum :
      MF + MG ≤ M := by

    dsimp only [M]

    exact
      le_max_right _ _

  have hFailFAt :=
    hFailF
      t htF x

  have hFailGAt :=
    hFailG
      t htG x

  have hMFlt :
      MF < abs (H t x) :=
    lt_of_le_of_lt
      hMF
      hLargeH

  have hMGlt :
      MG < abs (H t x) :=
    lt_of_le_of_lt
      hMG
      hLargeH

  have hFBound :
      abs (F t x) ≤ MF :=
    hFailFAt
      hMFlt

  have hGBound :
      abs (G t x) ≤ MG :=
    hFailGAt
      hMGlt

  have hUpper :
      abs (H t x) ≤ M := by

    rw [hEq t x]

    calc
      abs (F t x - G t x)
          ≤
        abs (F t x) + abs (G t x) :=
        abs_sub _ _

      _ ≤
        MF + MG :=
        add_le_add hFBound hGBound

      _ ≤ M :=
        hSum

  exact
    (not_lt_of_ge hUpper)
      hLargeH

/-! ## Sequence extraction from joint cofinal unboundedness -/

private theorem tendsto_terminal_of_localized_samePointPair
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

private theorem tendsto_atTop_of_natCast_lt_samePointPair
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

private theorem terminalScalarPairSamePoint_blowupSequence_of_cofinallyUnbounded
    {a T : ℝ}
    {H F : ℝ → Point3 → ℝ}
    (haT : a < T)
    (hPair :
      H3TerminalScalarPairSamePointCofinallyUnbounded
        a T H F) :
    H3TerminalScalarPairSamePointBlowupSequence
      a T H F := by

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
            (n : ℝ) < abs (H t x)
              ∧
            (n : ℝ) < abs (F t x) := by

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
      ⟨t, ht, x, hH, hF⟩ :=
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
        by
          exact
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
    tendsto_terminal_of_localized_samePointPair
      (fun n => (hτ n).2.1)

  have hHTendsto :
      Tendsto
        (fun n : ℕ => abs (H (τ n) (x n)))
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_samePointPair
      (fun n => (hτ n).2.2.1)

  have hFTendsto :
      Tendsto
        (fun n : ℕ => abs (F (τ n) (x n)))
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_samePointPair
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

/-! ## Six structurally valid fixed curl / gradient pairs -/

private noncomputable def h3TerminalVorticityXField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    realVorticityX
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x

private noncomputable def h3TerminalVorticityYField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    realVorticityY
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x

private noncomputable def h3TerminalVorticityZField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    realVorticityZ
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x

private noncomputable def h3TerminalGradientField
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

def H3TerminalVorticityXGradientYZSamePointCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointCofinallyUnbounded
    a T
    (h3TerminalVorticityXField u)
    (h3TerminalGradientField u yAxis zAxis)

def H3TerminalVorticityXGradientZYSamePointCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointCofinallyUnbounded
    a T
    (h3TerminalVorticityXField u)
    (h3TerminalGradientField u zAxis yAxis)

def H3TerminalVorticityYGradientZXSamePointCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointCofinallyUnbounded
    a T
    (h3TerminalVorticityYField u)
    (h3TerminalGradientField u zAxis xAxis)

def H3TerminalVorticityYGradientXZSamePointCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointCofinallyUnbounded
    a T
    (h3TerminalVorticityYField u)
    (h3TerminalGradientField u xAxis zAxis)

def H3TerminalVorticityZGradientXYSamePointCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointCofinallyUnbounded
    a T
    (h3TerminalVorticityZField u)
    (h3TerminalGradientField u xAxis yAxis)

def H3TerminalVorticityZGradientYXSamePointCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointCofinallyUnbounded
    a T
    (h3TerminalVorticityZField u)
    (h3TerminalGradientField u yAxis xAxis)

def H3TerminalVorticityXGradientYZSamePointBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointBlowupSequence
    a T
    (h3TerminalVorticityXField u)
    (h3TerminalGradientField u yAxis zAxis)

def H3TerminalVorticityXGradientZYSamePointBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointBlowupSequence
    a T
    (h3TerminalVorticityXField u)
    (h3TerminalGradientField u zAxis yAxis)

def H3TerminalVorticityYGradientZXSamePointBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointBlowupSequence
    a T
    (h3TerminalVorticityYField u)
    (h3TerminalGradientField u zAxis xAxis)

def H3TerminalVorticityYGradientXZSamePointBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointBlowupSequence
    a T
    (h3TerminalVorticityYField u)
    (h3TerminalGradientField u xAxis zAxis)

def H3TerminalVorticityZGradientXYSamePointBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointBlowupSequence
    a T
    (h3TerminalVorticityZField u)
    (h3TerminalGradientField u xAxis yAxis)

def H3TerminalVorticityZGradientYXSamePointBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarPairSamePointBlowupSequence
    a T
    (h3TerminalVorticityZField u)
    (h3TerminalGradientField u yAxis xAxis)

/-! ## Fixed same-point pair under hypothetical nonextension -/

/--
Hypothetical nonextension forces one structurally valid fixed curl/gradient
pair to be jointly cofinally unbounded at the same spacetime points.
-/
theorem fixed_curl_constituentGradient_samePoint_cofinallyUnbounded_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalVorticityXGradientYZSamePointCofinallyUnbounded u a T
      ∨
    H3TerminalVorticityXGradientZYSamePointCofinallyUnbounded u a T
      ∨
    H3TerminalVorticityYGradientZXSamePointCofinallyUnbounded u a T
      ∨
    H3TerminalVorticityYGradientXZSamePointCofinallyUnbounded u a T
      ∨
    H3TerminalVorticityZGradientXYSamePointCofinallyUnbounded u a T
      ∨
    H3TerminalVorticityZGradientYXSamePointCofinallyUnbounded u a T := by

  rcases
      fixed_vorticityComponent_cofinallyUnbounded_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    with hX | hY | hZ

  · have hHX :
        H3TerminalScalarComponentCofinallyUnbounded
          a T
          (h3TerminalVorticityXField u) := by

      simpa only [
        H3TerminalScalarComponentCofinallyUnbounded,
        H3TerminalVorticityXCofinallyUnbounded,
        h3TerminalVorticityXField
      ] using hX

    have hEq :
        ∀ t : ℝ,
          ∀ x : Point3,
            h3TerminalVorticityXField u t x
              =
            h3TerminalGradientField u yAxis zAxis t x
              -
            h3TerminalGradientField u zAxis yAxis t x := by

      intro t x

      rfl

    rcases
        terminalScalarPairSamePoint_one_of_sub_pair_cofinallyUnbounded
          hHX hEq
      with hYZ | hZY

    · exact
        Or.inl hYZ

    · exact
        Or.inr
          (Or.inl hZY)

  · have hHY :
        H3TerminalScalarComponentCofinallyUnbounded
          a T
          (h3TerminalVorticityYField u) := by

      simpa only [
        H3TerminalScalarComponentCofinallyUnbounded,
        H3TerminalVorticityYCofinallyUnbounded,
        h3TerminalVorticityYField
      ] using hY

    have hEq :
        ∀ t : ℝ,
          ∀ x : Point3,
            h3TerminalVorticityYField u t x
              =
            h3TerminalGradientField u zAxis xAxis t x
              -
            h3TerminalGradientField u xAxis zAxis t x := by

      intro t x

      rfl

    rcases
        terminalScalarPairSamePoint_one_of_sub_pair_cofinallyUnbounded
          hHY hEq
      with hZX | hXZ

    · exact
        Or.inr
          (
            Or.inr
              (Or.inl hZX)
          )

    · exact
        Or.inr
          (
            Or.inr
              (
                Or.inr
                  (Or.inl hXZ)
              )
          )

  · have hHZ :
        H3TerminalScalarComponentCofinallyUnbounded
          a T
          (h3TerminalVorticityZField u) := by

      simpa only [
        H3TerminalScalarComponentCofinallyUnbounded,
        H3TerminalVorticityZCofinallyUnbounded,
        h3TerminalVorticityZField
      ] using hZ

    have hEq :
        ∀ t : ℝ,
          ∀ x : Point3,
            h3TerminalVorticityZField u t x
              =
            h3TerminalGradientField u xAxis yAxis t x
              -
            h3TerminalGradientField u yAxis xAxis t x := by

      intro t x

      rfl

    rcases
        terminalScalarPairSamePoint_one_of_sub_pair_cofinallyUnbounded
          hHZ hEq
      with hXY | hYX

    · exact
        Or.inr
          (
            Or.inr
              (
                Or.inr
                  (
                    Or.inr
                      (Or.inl hXY)
                  )
              )
          )

    · exact
        Or.inr
          (
            Or.inr
              (
                Or.inr
                  (
                    Or.inr
                      (Or.inr hYX)
                  )
              )
          )

/--
Hypothetical nonextension admits a single localized terminal spacetime
sequence on which one fixed vorticity component and one fixed constituent
first derivative both exceed `n` and both tend to `+∞`.
-/
theorem fixed_curl_constituentGradient_samePoint_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalVorticityXGradientYZSamePointBlowupSequence u a T
      ∨
    H3TerminalVorticityXGradientZYSamePointBlowupSequence u a T
      ∨
    H3TerminalVorticityYGradientZXSamePointBlowupSequence u a T
      ∨
    H3TerminalVorticityYGradientXZSamePointBlowupSequence u a T
      ∨
    H3TerminalVorticityZGradientXYSamePointBlowupSequence u a T
      ∨
    H3TerminalVorticityZGradientYXSamePointBlowupSequence u a T := by

  rcases
      fixed_curl_constituentGradient_samePoint_cofinallyUnbounded_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    with h1 | h2 | h3 | h4 | h5 | h6

  · exact
      Or.inl
        (
          terminalScalarPairSamePoint_blowupSequence_of_cofinallyUnbounded
            hClass.terminal_start.2
            h1
        )

  · exact
      Or.inr
        (
          Or.inl
            (
              terminalScalarPairSamePoint_blowupSequence_of_cofinallyUnbounded
                hClass.terminal_start.2
                h2
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inl
                (
                  terminalScalarPairSamePoint_blowupSequence_of_cofinallyUnbounded
                    hClass.terminal_start.2
                    h3
                )
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  Or.inl
                    (
                      terminalScalarPairSamePoint_blowupSequence_of_cofinallyUnbounded
                        hClass.terminal_start.2
                        h4
                    )
                )
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  Or.inr
                    (
                      Or.inl
                        (
                          terminalScalarPairSamePoint_blowupSequence_of_cofinallyUnbounded
                            hClass.terminal_start.2
                            h5
                        )
                    )
                )
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  Or.inr
                    (
                      Or.inr
                        (
                          terminalScalarPairSamePoint_blowupSequence_of_cofinallyUnbounded
                            hClass.terminal_start.2
                            h6
                        )
                    )
                )
            )
        )

/-! ## Neutral package -/

/--
Neutral terminal formulation with one fixed structurally coupled curl/gradient
pair diverging at the same selected spacetime points.
-/
theorem smoothContinuationExtension_or_fixed_curl_constituentGradient_samePoint_blowupSequence
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
      H3TerminalVorticityXGradientYZSamePointBlowupSequence u a T
        ∨
      H3TerminalVorticityXGradientZYSamePointBlowupSequence u a T
        ∨
      H3TerminalVorticityYGradientZXSamePointBlowupSequence u a T
        ∨
      H3TerminalVorticityYGradientXZSamePointBlowupSequence u a T
        ∨
      H3TerminalVorticityZGradientXYSamePointBlowupSequence u a T
        ∨
      H3TerminalVorticityZGradientYXSamePointBlowupSequence u a T
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
          fixed_curl_constituentGradient_samePoint_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
