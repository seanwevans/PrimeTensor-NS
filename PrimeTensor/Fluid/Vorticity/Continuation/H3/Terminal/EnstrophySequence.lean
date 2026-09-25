import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.VorticityGradientSamePointSequence

/-!
# Terminal pointwise enstrophy sequence

The same-point terminal vorticity/gradient sequence localizes a hypothetical
nonextension pathology to actual spacetime points `(τₙ,yₙ)`.

At each such point, let

    m = max(|ωₓ|, |ωᵧ|, |ω_z|).

The classical pointwise enstrophy density is

    e = ωₓ² + ωᵧ² + ω_z²,

so

    m² ≤ e.

Hence the already-proved bound `n < m` yields

    n² < e(τₙ,yₙ),

and the pointwise enstrophy density tends to `+∞` along the same terminal
spacetime sequence.

PrimeTensor already has the exact multiplicative bridge

    logValue (mulEnstrophyDensity u t x)
      =
    realEnstrophyDensity (logSpaceTimeVectorField u) t x.

Therefore the logarithm of the native multiplicative enstrophy state also tends
to `+∞` along that sequence.

This remains a necessary consequence conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise max-vorticity versus enstrophy -/

/--
The square of the largest real vorticity-component magnitude is bounded by the
pointwise real enstrophy density.
-/
theorem sq_vorticityComponentMax_le_realEnstrophyDensity
    (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3) :
    (
      max
        (abs (realVorticityX v t x))
        (
          max
            (abs (realVorticityY v t x))
            (abs (realVorticityZ v t x))
        )
    ) ^ 2
      ≤
    realEnstrophyDensity v t x := by

  unfold realEnstrophyDensity

  by_cases hX :
      max
          (abs (realVorticityY v t x))
          (abs (realVorticityZ v t x))
        ≤
      abs (realVorticityX v t x)

  · rw [max_eq_left hX]
    rw [sq_abs]

    nlinarith [
      sq_nonneg (realVorticityY v t x),
      sq_nonneg (realVorticityZ v t x)
    ]

  · have hX' :
        abs (realVorticityX v t x)
          ≤
        max
          (abs (realVorticityY v t x))
          (abs (realVorticityZ v t x)) := by
      exact
        le_of_not_ge
          hX

    rw [max_eq_right hX']

    by_cases hY :
        abs (realVorticityZ v t x)
          ≤
        abs (realVorticityY v t x)

    · rw [max_eq_left hY]
      rw [sq_abs]

      nlinarith [
        sq_nonneg (realVorticityX v t x),
        sq_nonneg (realVorticityZ v t x)
      ]

    · have hY' :
          abs (realVorticityY v t x)
            ≤
          abs (realVorticityZ v t x) := by
        exact
          le_of_not_ge
            hY

      rw [max_eq_right hY']
      rw [sq_abs]

      nlinarith [
        sq_nonneg (realVorticityX v t x),
        sq_nonneg (realVorticityY v t x)
      ]

/--
If the maximum vorticity-component magnitude is larger than a nonnegative
threshold `M`, then the pointwise enstrophy density is larger than `M²`.
-/
theorem sq_lt_realEnstrophyDensity_of_lt_vorticityComponentMax
    (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    {M : ℝ}
    (hM : 0 ≤ M)
    (hLarge :
      M
        <
      max
        (abs (realVorticityX v t x))
        (
          max
            (abs (realVorticityY v t x))
            (abs (realVorticityZ v t x))
        )) :
    M ^ 2
      <
    realEnstrophyDensity v t x := by

  let W : ℝ :=
    max
      (abs (realVorticityX v t x))
      (
        max
          (abs (realVorticityY v t x))
          (abs (realVorticityZ v t x))
      )

  have hW :
      0 ≤ W := by

    dsimp only [W]

    exact
      le_max_of_le_left
        (abs_nonneg _)

  have hSq :
      M ^ 2 < W ^ 2 :=
    (sq_lt_sq₀ hM hW).2
      (by
        simpa only [W] using hLarge)

  have hMaxSq :
      W ^ 2
        ≤
      realEnstrophyDensity v t x := by

    dsimp only [W]

    exact
      sq_vorticityComponentMax_le_realEnstrophyDensity
        v t x

  exact
    lt_of_lt_of_le
      hSq
      hMaxSq

/-! ## Terminal enstrophy sequence -/

/--
Under hypothetical nonextension, the same terminal spacetime sequence carrying
the actual vorticity/gradient pathology also carries pointwise real enstrophy
larger than `n²`.
-/
theorem exists_samePoint_enstrophy_blowupSequence_of_noH3PathExtension
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
      ∃
        y : ℕ → Point3,
        ∃
          i j : ℕ → PrimeTensor.Axis Depth.three,
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
                ∧
              (n : ℝ) / 2
                <
              abs
                (
                  spatial3.d
                    (i n)
                    (
                      fun x =>
                        (
                          PrimeTensor.Bridge.logSpaceTimeVectorField
                            u (τ n) x
                        ).component (j n)
                    )
                    (y n)
                )
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
                realEnstrophyDensity
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  (τ n)
                  (y n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                PrimeTensor.Bridge.MulReal.logValue
                  (mulEnstrophyDensity u (τ n) (y n))
            )
            atTop
            atTop := by

  obtain
    ⟨
      τ,
      y,
      i,
      j,
      hτ,
      hTauTendsto,
      hOmegaTendsto,
      hGradientTendsto
    ⟩ :=
    exists_samePoint_vorticityGradient_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hEnstrophy :
      ∀ n : ℕ,
        (n : ℝ) ^ 2
          <
        realEnstrophyDensity
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ n)
          (y n) := by

    intro n

    exact
      sq_lt_realEnstrophyDensity_of_lt_vorticityComponentMax
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        (τ n)
        (y n)
        (Nat.cast_nonneg n)
        (hτ n).2.2.1

  have hEnstrophyTendsto :
      Tendsto
        (
          fun n : ℕ =>
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ n)
              (y n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        (max M 1)

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    have hNLe :
        (N : ℝ) ≤ n := by
      exact_mod_cast hn

    have hMltN :
        M < (N : ℝ) := by
      exact
        lt_of_le_of_lt
          (le_max_left M 1)
          hN

    have hOneLtN :
        1 < (N : ℝ) := by
      exact
        lt_of_le_of_lt
          (le_max_right M 1)
          hN

    have hOneLeN :
        1 ≤ (n : ℝ) := by
      linarith

    have hNNonneg :
        0 ≤ (n : ℝ) :=
      Nat.cast_nonneg n

    have hNSq :
        (n : ℝ) ≤ (n : ℝ) ^ 2 := by

      nlinarith [
        mul_nonneg
          hNNonneg
          (sub_nonneg.mpr hOneLeN)
      ]

    exact
      le_of_lt
        (
          lt_trans
            (lt_of_lt_of_le hMltN hNLe)
            (
              lt_of_le_of_lt
                hNSq
                (hEnstrophy n)
            )
        )

  have hNativeTendsto :
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (mulEnstrophyDensity u (τ n) (y n))
        )
        atTop
        atTop := by

    have hEq :
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (mulEnstrophyDensity u (τ n) (y n))
        )
          =
        (
          fun n : ℕ =>
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ n)
              (y n)
        ) := by

      funext n

      exact
        logValue_mulEnstrophyDensity
          u
          (τ n)
          (y n)

    rw [hEq]

    exact
      hEnstrophyTendsto

  exact
    ⟨
      τ,
      y,
      i,
      j,
      (fun n =>
        ⟨
          (hτ n).1,
          (hτ n).2.1,
          (hτ n).2.2.1,
          (hτ n).2.2.2,
          hEnstrophy n
        ⟩),
      hTauTendsto,
      hEnstrophyTendsto,
      hNativeTendsto
    ⟩

/-! ## Neutral package -/

/--
Neutral terminal formulation including the native multiplicative enstrophy
bridge.
-/
theorem smoothContinuationExtension_or_terminal_nativeEnstrophyLog_blowupSequence
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
        ∃
          y : ℕ → Point3,
          ∃
            i j : ℕ → PrimeTensor.Axis Depth.three,
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
                  ∧
                (n : ℝ) / 2
                  <
                abs
                  (
                    spatial3.d
                      (i n)
                      (
                        fun x =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u (τ n) x
                          ).component (j n)
                      )
                      (y n)
                  )
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
                  realEnstrophyDensity
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    (τ n)
                    (y n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  PrimeTensor.Bridge.MulReal.logValue
                    (mulEnstrophyDensity u (τ n) (y n))
              )
              atTop
              atTop
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
          exists_samePoint_enstrophy_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
