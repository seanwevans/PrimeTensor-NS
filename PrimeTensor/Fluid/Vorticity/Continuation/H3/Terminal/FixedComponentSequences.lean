import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedGradientComponent

/-!
# Fixed-component terminal blowup sequences

The terminal coordinate-persistence theorems prove that hypothetical
nonextension forces

* one fixed real vorticity component to be cofinally unbounded, and
* one fixed first velocity derivative entry to be cofinally unbounded.

This file converts those cofinal statements into standard terminal sequences.

For the fixed gradient entry there are fixed axes `i,j` and sequences
`σₙ → T`, `xₙ` such that

    n < |∂ᵢ uⱼ(σₙ,xₙ)|.

For vorticity, one fixed component among `ωₓ,ωᵧ,ω_z` admits a sequence
`τₙ → T`, `yₙ` such that

    n < |ω_fixed(τₙ,yₙ)|.

Each time sequence is additionally localized by

    T - 1/(n+1) < timeₙ < T.

The gradient and vorticity sequences are kept separate: fixed-coordinate
persistence does not by itself synchronize their selected times or points.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Generic fixed scalar-component sequence package -/

def H3TerminalScalarComponentBlowupSequence
    (a T : ℝ)
    (F : ℝ → Point3 → ℝ) : Prop :=
  ∃
    σ : ℕ → ℝ,
    ∃ x : ℕ → Point3,
      (
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T
            ∧
          σ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
            ∧
          (n : ℝ) < abs (F (σ n) (x n))
      )
        ∧
      Tendsto σ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ => abs (F (σ n) (x n)))
        atTop
        atTop

def H3TerminalVelocityGradientComponentBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (i j : PrimeTensor.Axis Depth.three) : Prop :=
  H3TerminalScalarComponentBlowupSequence
    a T
    (
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
    )

def H3TerminalVorticityXBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarComponentBlowupSequence
    a T
    (
      fun t x =>
        realVorticityX
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x
    )

def H3TerminalVorticityYBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarComponentBlowupSequence
    a T
    (
      fun t x =>
        realVorticityY
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x
    )

def H3TerminalVorticityZBlowupSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  H3TerminalScalarComponentBlowupSequence
    a T
    (
      fun t x =>
        realVorticityZ
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x
    )

/-! ## Sequence utilities -/

private theorem tendsto_terminal_of_one_div_natSucc_localization_fixed
    {T : ℝ}
    {σ : ℕ → ℝ}
    (hσ :
      ∀ n : ℕ,
        σ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T) :
    Tendsto σ atTop (𝓝 T) := by

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

  have hInvN :
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

    have hMulRaw :
        1 < ((N : ℝ) + 1) * ε :=
      (div_lt_iff₀ hε).1
        hNPlus

    exact
      (div_lt_iff₀ hDenN).2
        (by
          simpa only [mul_comm, one_mul] using hMulRaw)

  have hSmall :
      (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    lt_of_le_of_lt
      hInvN
      hSmallN

  have hLower :=
    (hσ n).1

  have hUpper :=
    (hσ n).2

  rw [Real.dist_eq]

  have hDiffNonpos :
      σ n - T ≤ 0 := by
    linarith

  rw [abs_of_nonpos hDiffNonpos]

  linarith

private theorem tendsto_atTop_of_natCast_lt_fixed
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

private theorem terminalScalarComponentBlowupSequence_of_cofinallyUnbounded
    {a T : ℝ}
    {F : ℝ → Point3 → ℝ}
    (haT : a < T)
    (hCofinal :
      ∀
        c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃
              t : ℝ,
                t ∈ Set.Ioo c T
                  ∧
                ∃ x : Point3,
                  M < abs (F t x)) :
    H3TerminalScalarComponentBlowupSequence
      a T F := by

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
      ⟨t, ht, x, hAmp⟩ :=
      hCofinal
        c hc
        (n : ℝ)

    have htClass :
        t ∈ Set.Ioo a T := by

      exact
        ⟨
          lt_trans hc.1 ht.1,
          ht.2
        ⟩

    have htNear :
        t ∈ Set.Ioo (T - ε) T := by

      exact
        ⟨
          lt_trans hcNear ht.1,
          ht.2
        ⟩

    exact
      ⟨
        t,
        x,
        htClass,
        by
          simpa only [ε] using htNear,
        hAmp
      ⟩

  choose σ x hσ using
    hChoice

  have hSigmaTendsto :
      Tendsto σ atTop (𝓝 T) :=
    tendsto_terminal_of_one_div_natSucc_localization_fixed
      (fun n => (hσ n).2.1)

  have hAmplitudeTendsto :
      Tendsto
        (fun n : ℕ => abs (F (σ n) (x n)))
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_fixed
      (fun n => (hσ n).2.2)

  exact
    ⟨
      σ,
      x,
      hσ,
      hSigmaTendsto,
      hAmplitudeTendsto
    ⟩

/-! ## Fixed gradient-entry sequence -/

/--
Under hypothetical nonextension, one fixed first velocity derivative entry
admits a terminal sequence with amplitude larger than `n` and therefore tending
to `+∞`.
-/
theorem exists_fixed_velocityGradientComponent_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      i j : PrimeTensor.Axis Depth.three,
        H3TerminalVelocityGradientComponentBlowupSequence
          u a T i j := by

  obtain
    ⟨i, j, hij⟩ :=
    exists_fixed_velocityGradientComponent_cofinallyUnbounded_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  refine
    ⟨
      i,
      j,
      ?_
    ⟩

  unfold H3TerminalVelocityGradientComponentBlowupSequence

  exact
    terminalScalarComponentBlowupSequence_of_cofinallyUnbounded
      hClass.terminal_start.2
      hij

/-! ## Fixed vorticity-component sequence -/

/--
Under hypothetical nonextension, one fixed vorticity component among
`ωₓ,ωᵧ,ω_z` admits a terminal sequence with amplitude larger than `n` and
therefore tending to `+∞`.
-/
theorem fixed_vorticityComponent_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalVorticityXBlowupSequence u a T
      ∨
    H3TerminalVorticityYBlowupSequence u a T
      ∨
    H3TerminalVorticityZBlowupSequence u a T := by

  rcases
      fixed_vorticityComponent_cofinallyUnbounded_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    with hX | hY | hZ

  · exact
      Or.inl
        (
          terminalScalarComponentBlowupSequence_of_cofinallyUnbounded
            hClass.terminal_start.2
            hX
        )

  · exact
      Or.inr
        (
          Or.inl
            (
              terminalScalarComponentBlowupSequence_of_cofinallyUnbounded
                hClass.terminal_start.2
                hY
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              terminalScalarComponentBlowupSequence_of_cofinallyUnbounded
                hClass.terminal_start.2
                hZ
            )
        )

/-! ## Neutral package -/

/--
Neutral fixed-coordinate terminal alternative.

Either the H³ path extends smoothly, or there is both

* one fixed velocity-gradient entry with a terminal blowup sequence, and
* one fixed vorticity component with a terminal blowup sequence.

No synchronization between these two sequences is asserted.
-/
theorem smoothContinuationExtension_or_fixed_gradientAndVorticity_blowupSequences
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
        ∃
          i j : PrimeTensor.Axis Depth.three,
            H3TerminalVelocityGradientComponentBlowupSequence
              u a T i j
      )
        ∧
      (
        H3TerminalVorticityXBlowupSequence u a T
          ∨
        H3TerminalVorticityYBlowupSequence u a T
          ∨
        H3TerminalVorticityZBlowupSequence u a T
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
        ⟨
          exists_fixed_velocityGradientComponent_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          fixed_vorticityComponent_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
