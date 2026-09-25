import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComponentAmplitude

/-!
# Terminal component blowup sequences

The component-amplitude theorem gives cofinal unboundedness of actual first
velocity derivatives and actual vorticity components under hypothetical
nonextension.

This file extracts standard terminal sequences.

For the velocity gradient there are sequences

    σₙ → T,  iₙ, jₙ, xₙ

with

    n < |∂_{iₙ} u_{jₙ}(σₙ,xₙ)|.

For vorticity there are sequences

    τₙ → T,  yₙ

such that the maximum magnitude of the three actual vorticity components at
`(τₙ,yₙ)` exceeds `n`.

The two time sequences are intentionally kept separate: the preceding cofinal
theorems do not imply that large gradient and large vorticity occur at the
same time.

All statements are conditional consequences of hypothetical failure of smooth
continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Two sequence utilities -/

private theorem tendsto_terminal_of_one_div_natSucc_localization
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

  have hCast :
      (N : ℝ) ≤ n := by
    exact_mod_cast hn

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
        (by linarith)

  have hSmallN :
      1 / ((N : ℝ) + 1) < ε := by

    have hεPos :
        0 < ε :=
      hε

    have hInvEps :
        1 / ε < (N : ℝ) :=
      hN

    have hNPlus :
        1 / ε < (N : ℝ) + 1 := by
      linarith

    have hMulRaw :
        1 < ((N : ℝ) + 1) * ε :=
      (div_lt_iff₀ hεPos).1
        hNPlus

    have hMul :
        1 < ε * ((N : ℝ) + 1) := by
      simpa only [mul_comm] using
        hMulRaw

    exact
      (div_lt_iff₀ hDenN).2
        (by
          simpa only [one_mul] using hMul)

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
    linarith [hUpper]

  rw [abs_of_nonpos hDiffNonpos]

  linarith

private theorem tendsto_atTop_of_natCast_lt
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

/-! ## Gradient-component sequence -/

/--
Hypothetical nonextension admits a terminal sequence of actual first velocity
derivative components whose magnitudes tend to `+∞`.
-/
theorem exists_velocityGradientComponent_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      σ : ℕ → ℝ,
      ∃
        i j : ℕ → PrimeTensor.Axis Depth.three,
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
              (n : ℝ)
                <
              abs
                (
                  spatial3.d
                    (i n)
                    (
                      fun y =>
                        (
                          PrimeTensor.Bridge.logSpaceTimeVectorField
                            u (σ n) y
                        ).component (j n)
                    )
                    (x n)
                )
          )
            ∧
          Tendsto σ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                abs
                  (
                    spatial3.d
                      (i n)
                      (
                        fun y =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u (σ n) y
                          ).component (j n)
                      )
                      (x n)
                  )
            )
            atTop
            atTop := by

  have hChoice :
      ∀ n : ℕ,
        ∃
          t : ℝ,
          ∃
            i j : PrimeTensor.Axis Depth.three,
            ∃ x : Point3,
              t ∈ Set.Ioo a T
                ∧
              t ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T
                ∧
              (n : ℝ)
                <
              abs
                (
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
                ) := by

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
          hClass.terminal_start.2
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
      ⟨t, ht, i, j, x, hAmp⟩ :=
      exists_velocityGradientComponent_gt_on_every_strictSubtail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        c
        hc
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
        i,
        j,
        x,
        htClass,
        by
          simpa only [ε] using htNear,
        hAmp
      ⟩

  choose σ i j x hσ using
    hChoice

  have hSigmaTendsto :
      Tendsto σ atTop (𝓝 T) :=
    tendsto_terminal_of_one_div_natSucc_localization
      (fun n => (hσ n).2.1)

  have hAmplitudeTendsto :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                spatial3.d
                  (i n)
                  (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (σ n) y
                      ).component (j n)
                  )
                  (x n)
              )
        )
        atTop
        atTop :=

    tendsto_atTop_of_natCast_lt
      (fun n => (hσ n).2.2)

  exact
    ⟨
      σ,
      i,
      j,
      x,
      hσ,
      hSigmaTendsto,
      hAmplitudeTendsto
    ⟩

/-! ## Vorticity-component sequence -/

/--
Hypothetical nonextension admits a terminal sequence of actual vorticity
component amplitudes tending to `+∞`.

At each selected point the scalar amplitude is the maximum of the magnitudes of
the three real vorticity components.
-/
theorem exists_vorticityComponentMax_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      τ : ℕ → ℝ,
      ∃ y : ℕ → Point3,
        (
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            (n : ℝ)
              <
            max
              (
                abs
                  (
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (τ n)
                      (y n)
                  )
              )
              (
                max
                  (
                    abs
                      (
                        realVorticityY
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (τ n)
                          (y n)
                      )
                  )
                  (
                    abs
                      (
                        realVorticityZ
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (τ n)
                          (y n)
                      )
                  )
              )
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              max
                (
                  abs
                    (
                      realVorticityX
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (τ n)
                        (y n)
                    )
                )
                (
                  max
                    (
                      abs
                        (
                          realVorticityY
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            (τ n)
                            (y n)
                        )
                    )
                    (
                      abs
                        (
                          realVorticityZ
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            (τ n)
                            (y n)
                        )
                    )
                )
          )
          atTop
          atTop := by

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
            (n : ℝ)
              <
            max
              (
                abs
                  (
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t x
                  )
              )
              (
                max
                  (
                    abs
                      (
                        realVorticityY
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          t x
                      )
                  )
                  (
                    abs
                      (
                        realVorticityZ
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          t x
                      )
                  )
              ) := by

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
          hClass.terminal_start.2
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
      exists_vorticityComponent_gt_on_every_strictSubtail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        c
        hc
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

    have hMax :
        (n : ℝ)
          <
        max
          (
            abs
              (
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
          )
          (
            max
              (
                abs
                  (
                    realVorticityY
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t x
                  )
              )
              (
                abs
                  (
                    realVorticityZ
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t x
                  )
              )
          ) := by

      rcases hAmp with hX | hY | hZ

      · exact
          lt_of_lt_of_le
            hX
            (le_max_left _ _)

      · exact
          lt_of_lt_of_le
            hY
            (
              le_trans
                (le_max_left _ _)
                (le_max_right _ _)
            )

      · exact
          lt_of_lt_of_le
            hZ
            (
              le_trans
                (le_max_right _ _)
                (le_max_right _ _)
            )

    exact
      ⟨
        t,
        x,
        htClass,
        by
          simpa only [ε] using htNear,
        hMax
      ⟩

  choose τ y hτ using
    hChoice

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) :=
    tendsto_terminal_of_one_div_natSucc_localization
      (fun n => (hτ n).2.1)

  have hAmplitudeTendsto :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                abs
                  (
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (τ n)
                      (y n)
                  )
              )
              (
                max
                  (
                    abs
                      (
                        realVorticityY
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (τ n)
                          (y n)
                      )
                  )
                  (
                    abs
                      (
                        realVorticityZ
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (τ n)
                          (y n)
                      )
                  )
              )
        )
        atTop
        atTop :=

    tendsto_atTop_of_natCast_lt
      (fun n => (hτ n).2.2)

  exact
    ⟨
      τ,
      y,
      hτ,
      hTauTendsto,
      hAmplitudeTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
