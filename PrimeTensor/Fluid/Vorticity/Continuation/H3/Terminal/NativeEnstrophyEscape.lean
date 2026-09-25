import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.EnstrophySequence

/-!
# Native terminal enstrophy escape

The preceding terminal enstrophy theorem gives a natural sequence of native
multiplicative enstrophy states

    Eₙ = mulEnstrophyDensity u (τₙ) (yₙ)

whose logarithmic coordinates tend to `+∞`.

`MulReal.logValue` is a faithful finite real coordinate on every completed
multiplicative state.  Therefore, for every fixed `q : MulReal`,

    logValue q < logValue Eₙ

eventually.

In particular the logarithmic coordinates of `Eₙ` cannot converge to the
logarithmic coordinate of any finite `MulReal` state.

No intrinsic linear order on `MulReal` is introduced or assumed.  The escape
statement is made entirely through the already-established faithful logarithmic
coordinate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## A real divergence utility -/

/--
A real sequence tending to `+∞` cannot converge to any finite real number.
-/
private theorem not_tendsto_nhds_of_tendsto_atTop
    {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop)
    (L : ℝ) :
    ¬ Tendsto f atTop (𝓝 L) := by

  intro hL

  have hAbove :
      ∀ᶠ n : ℕ in atTop,
        L + 2 < f n :=
    hf.eventually
      (eventually_gt_atTop (L + 2))

  obtain
    ⟨N₁, hN₁⟩ :=
    (eventually_atTop.1 hAbove)

  rw [Metric.tendsto_atTop] at hL

  obtain
    ⟨N₂, hN₂⟩ :=
    hL
      1
      (by norm_num)

  let N : ℕ :=
    max N₁ N₂

  have hOne :
      L + 2 < f N :=
    hN₁
      N
      (le_max_left _ _)

  have hNear :
      dist (f N) L < 1 :=
    hN₂
      N
      (le_max_right _ _)

  rw [Real.dist_eq] at hNear

  have hUpper :
      f N < L + 1 := by

    rw [abs_lt] at hNear

    linarith [hNear.2]

  linarith

/-! ## Terminal native enstrophy escape -/

/--
Under hypothetical nonextension, there is a terminal sequence of native
enstrophy states whose logarithmic coordinates eventually exceed the
logarithmic coordinate of every fixed `MulReal` state.

The same sequence retains the explicit `1/(n+1)` terminal localization and the
pointwise `n²` real-enstrophy lower bound.
-/
theorem exists_terminal_nativeEnstrophy_escapeEveryFiniteLogState_of_noH3PathExtension
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
            (n : ℝ) ^ 2
              <
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ n)
              (y n)
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              PrimeTensor.Bridge.MulReal.logValue
                (mulEnstrophyDensity u (τ n) (y n))
          )
          atTop
          atTop
          ∧
        (
          ∀ q : PrimeTensor.MulReal,
            ∀ᶠ n : ℕ in atTop,
              PrimeTensor.Bridge.MulReal.logValue q
                <
              PrimeTensor.Bridge.MulReal.logValue
                (mulEnstrophyDensity u (τ n) (y n))
        )
          ∧
        (
          ∀ q : PrimeTensor.MulReal,
            ¬ Tendsto
                (
                  fun n : ℕ =>
                    PrimeTensor.Bridge.MulReal.logValue
                      (mulEnstrophyDensity u (τ n) (y n))
                )
                atTop
                (
                  𝓝
                    (
                      PrimeTensor.Bridge.MulReal.logValue q
                    )
                )
        ) := by

  obtain
    ⟨
      τ,
      y,
      i,
      j,
      hτ,
      hTauTendsto,
      hEnstrophyTendsto,
      hNativeTendsto
    ⟩ :=
    exists_samePoint_enstrophy_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hEscape :
      ∀ q : PrimeTensor.MulReal,
        ∀ᶠ n : ℕ in atTop,
          PrimeTensor.Bridge.MulReal.logValue q
            <
          PrimeTensor.Bridge.MulReal.logValue
            (mulEnstrophyDensity u (τ n) (y n)) := by

    intro q

    exact
      hNativeTendsto.eventually
        (
          eventually_gt_atTop
            (
              PrimeTensor.Bridge.MulReal.logValue q
            )
        )

  have hNoFiniteLimit :
      ∀ q : PrimeTensor.MulReal,
        ¬ Tendsto
            (
              fun n : ℕ =>
                PrimeTensor.Bridge.MulReal.logValue
                  (mulEnstrophyDensity u (τ n) (y n))
            )
            atTop
            (
              𝓝
                (
                  PrimeTensor.Bridge.MulReal.logValue q
                )
            ) := by

    intro q

    exact
      not_tendsto_nhds_of_tendsto_atTop
        hNativeTendsto
        (
          PrimeTensor.Bridge.MulReal.logValue q
        )

  exact
    ⟨
      τ,
      y,
      (fun n =>
        ⟨
          (hτ n).1,
          (hτ n).2.1,
          (hτ n).2.2.2.2
        ⟩),
      hTauTendsto,
      hNativeTendsto,
      hEscape,
      hNoFiniteLimit
    ⟩

/-! ## Neutral package -/

/--
Neutral formulation: either the path extends smoothly, or one terminal native
enstrophy sequence escapes every fixed finite `MulReal` logarithmic state and
has no finite logarithmic limit.
-/
theorem smoothContinuationExtension_or_terminal_nativeEnstrophy_escapesEveryFiniteLogState
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
              (n : ℝ) ^ 2
                <
              realEnstrophyDensity
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n)
                (y n)
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                PrimeTensor.Bridge.MulReal.logValue
                  (mulEnstrophyDensity u (τ n) (y n))
            )
            atTop
            atTop
            ∧
          (
            ∀ q : PrimeTensor.MulReal,
              ∀ᶠ n : ℕ in atTop,
                PrimeTensor.Bridge.MulReal.logValue q
                  <
                PrimeTensor.Bridge.MulReal.logValue
                  (mulEnstrophyDensity u (τ n) (y n))
          )
            ∧
          (
            ∀ q : PrimeTensor.MulReal,
              ¬ Tendsto
                  (
                    fun n : ℕ =>
                      PrimeTensor.Bridge.MulReal.logValue
                        (mulEnstrophyDensity u (τ n) (y n))
                  )
                  atTop
                  (
                    𝓝
                      (
                        PrimeTensor.Bridge.MulReal.logValue q
                      )
                  )
          )
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
          exists_terminal_nativeEnstrophy_escapeEveryFiniteLogState_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
