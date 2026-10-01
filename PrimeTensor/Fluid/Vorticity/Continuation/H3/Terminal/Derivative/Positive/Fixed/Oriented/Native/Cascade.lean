import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Fixed.Structural.Curl.Gradient
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Curl.Gradient.Double.Escape
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fixed oriented structural pair on the positive-growth cascade

The fixed structural-pair theorem gives, under hypothetical nonextension, one
positive-growth terminal spacetime sequence carrying

* full H³ energy divergence;
* normalized dissipation divergence;
* normalized adverse-transport divergence;
* top characteristic-frequency divergence;
* divergence of the magnitude of one fixed curl component;
* divergence of the magnitude of one fixed constituent gradient.

This file freezes the sign of both real fields.

For any real number `z`, choose the orientation

    positive  if 0 ≤ z,
    negative  if z < 0.

Then the corresponding oriented value is exactly `|z|`.  Applying this choice
to the fixed curl and gradient along the sequence gives a sequence in the
finite four-element orientation-pair space.  One pair occurs frequently, and
a strictly increasing subsequence freezes both signs simultaneously.

All scalar/frequency limits and the standard terminal localization survive
that extraction.  Along the resulting common sequence,

    orientedCurl -> +∞,
    orientedGradient -> +∞.

Finally, the exact multiplicative bridges

    logValue(nativeCurl) = realCurl,
    logValue(nativeGradient) = realGradient

transport these to one-sided native logarithmic escape in the corresponding
fixed directions.

Thus the positive-growth cascade and the previously developed native
curl/gradient escape machinery are synchronized on one sequence.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Canonical orientation of one real value -/

private def h3PositiveGrowthOrientationOfReal
    (z : ℝ) :
    H3TerminalOrientation :=
  if 0 ≤ z then
    H3TerminalOrientation.positive
  else
    H3TerminalOrientation.negative

private theorem h3TerminalOrientedValue_positiveGrowthOrientation_eq_abs
    (z : ℝ) :
    h3TerminalOrientedValue
        (h3PositiveGrowthOrientationOfReal z)
        z
      =
    abs z := by

  by_cases hz :
      0 ≤ z

  · simp [
      h3PositiveGrowthOrientationOfReal,
      hz,
      abs_of_nonneg hz
    ]

  · have hzNeg :
        z < 0 :=
      lt_of_not_ge
        hz

    simp [
      h3PositiveGrowthOrientationOfReal,
      hz,
      abs_of_neg hzNeg
    ]

local instance h3TerminalOrientationFintypePositiveGrowth :
    Fintype H3TerminalOrientation where

  elems :=
    {
      H3TerminalOrientation.positive,
      H3TerminalOrientation.negative
    }

  complete s := by
    cases s <;> simp

/-! ## Positive-growth cascade with fixed real and native orientations -/

/--
Under hypothetical nonextension, there is one fixed structural curl/gradient
pair and fixed orientations for both members on a positive-growth terminal
subsequence carrying the complete scalar/frequency cascade.

The corresponding native multiplicative curl and gradient states have
one-sided logarithmic escape in exactly those fixed orientations.
-/
theorem exists_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradient_doubleOriented_nativeEscape_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
    ∃
      p₀ : H3TerminalCurlGradientPair,
      ∃
        sCurl sGradient : H3TerminalOrientation,
        ∃
          τ : ℕ → ℝ,
          ∃
            y : ℕ → Point3,
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
                deriv (velocityH3EnergyAt u) (τ n)
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3EnergyAt u (τ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3DissipationAt u (τ n)
                    /
                  velocityH3EnergyAt u (τ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  (
                    - velocityH3TransportDerivativeAt u (τ n)
                  )
                    /
                  velocityH3EnergyAt u (τ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TopCharacteristicFrequencyAt
                    u
                    (τ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalOrientedValue
                    sCurl
                    (
                      h3TerminalCurlFieldForPair
                        u p₀
                        (τ n)
                        (y n)
                    )
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalOrientedValue
                    sGradient
                    (
                      h3TerminalGradientFieldForPair
                        u p₀
                        (τ n)
                        (y n)
                    )
              )
              atTop
              atTop
              ∧
            H3TerminalNativeLogDirectionalEscape
              (
                fun n : ℕ =>
                  h3TerminalNativeCurlForPair
                    u p₀
                    (τ n)
                    (y n)
              )
              sCurl
              ∧
            H3TerminalNativeLogDirectionalEscape
              (
                fun n : ℕ =>
                  h3TerminalNativeGradientForPair
                    u p₀
                    (τ n)
                    (y n)
              )
              sGradient := by

  obtain
    ⟨
      p₀,
      σ,
      x,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto,
      hFrequencyTendsto,
      hCurlAbsTendsto,
      hGradientAbsTendsto
    ⟩ :=
    exists_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradientPair_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  let s :
      ℕ →
        (
          H3TerminalOrientation
            ×
          H3TerminalOrientation
        ) :=
    fun n =>
      (
        h3PositiveGrowthOrientationOfReal
          (
            h3TerminalCurlFieldForPair
              u p₀
              (σ n)
              (x n)
          ),
        h3PositiveGrowthOrientationOfReal
          (
            h3TerminalGradientFieldForPair
              u p₀
              (σ n)
              (x n)
          )
      )

  have hFrequentlySomeOrientationPair :
      ∃ᶠ n : ℕ in atTop,
        ∃
          q :
            (
              H3TerminalOrientation
                ×
              H3TerminalOrientation
            ),
          s n = q :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            s n,
            rfl
          ⟩
      )

  obtain
    ⟨
      q,
      hOrientationFrequently
    ⟩ :=
    (
      Filter.frequently_exists
    ).1
      hFrequentlySomeOrientationPair

  obtain
    ⟨
      φ,
      hPhiMono,
      hOrientationFixed
    ⟩ :=
    extraction_of_frequently_atTop
      hOrientationFrequently

  have hPhiTendsto :
      Tendsto φ atTop atTop :=
    hPhiMono.tendsto_atTop

  let τ : ℕ → ℝ :=
    fun n =>
      σ (φ n)

  let y : ℕ → Point3 :=
    fun n =>
      x (φ n)

  have hCurlOrientationFixed :
      ∀ n : ℕ,
        h3PositiveGrowthOrientationOfReal
            (
              h3TerminalCurlFieldForPair
                u p₀
                (σ (φ n))
                (x (φ n))
            )
          =
        q.1 := by

    intro n

    have h :=
      congrArg Prod.fst
        (hOrientationFixed n)

    simpa only [s] using
      h

  have hGradientOrientationFixed :
      ∀ n : ℕ,
        h3PositiveGrowthOrientationOfReal
            (
              h3TerminalGradientFieldForPair
                u p₀
                (σ (φ n))
                (x (φ n))
            )
          =
        q.2 := by

    intro n

    have h :=
      congrArg Prod.snd
        (hOrientationFixed n)

    simpa only [s] using
      h

  have hTauData :
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
        deriv (velocityH3EnergyAt u) (τ n) := by

    intro n

    have hOld :=
      hσ (φ n)

    have hIndexLeNat :
        n ≤ φ n :=
      hPhiMono.le_apply

    have hIndexLe :
        (n : ℝ) ≤ (φ n : ℝ) := by
      exact_mod_cast
        hIndexLeNat

    have hDenPos :
        0 < (n : ℝ) + 1 := by
      positivity

    have hDenLe :
        (n : ℝ) + 1
          ≤
        (φ n : ℝ) + 1 := by
      linarith

    have hInv :
        (1 : ℝ) / ((φ n : ℝ) + 1)
          ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le
        hDenPos
        hDenLe

    have hNear :
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T := by

      constructor

      · dsimp only [τ]

        have hOldLower :=
          hOld.2.1.1

        linarith

      · dsimp only [τ]

        exact
          hOld.2.1.2

    have hDerivative :
        (n : ℝ)
          <
        deriv (velocityH3EnergyAt u) (τ n) := by

      dsimp only [τ]

      exact
        lt_of_le_of_lt
          hIndexLe
          hOld.2.2

    exact
      ⟨
        by
          dsimp only [τ]
          exact hOld.1,
        hNear,
        hDerivative
      ⟩

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by

    dsimp only [τ]

    exact
      hSigmaTendsto.comp
        hPhiTendsto

  have hEnergySubsequence :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            velocityH3EnergyAt u (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hEnergyTendsto.comp
        hPhiTendsto

  have hDissSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (τ n)
              /
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
              /
            velocityH3EnergyAt u (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hDissRatioTendsto.comp
        hPhiTendsto

  have hTransportSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (τ n)
            )
              /
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
              /
            velocityH3EnergyAt u (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hTransportRatioTendsto.comp
        hPhiTendsto

  have hFrequencySubsequence :
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicFrequencyAt
              u
              (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            h3TopCharacteristicFrequencyAt
              u
              (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hFrequencyTendsto.comp
        hPhiTendsto

  have hCurlAbsSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                h3TerminalCurlFieldForPair
                  u p₀
                  (τ n)
                  (y n)
              )
        )
        atTop
        atTop := by

    dsimp only [τ, y]

    change
      Tendsto
        (
          (fun n : ℕ =>
            abs
              (
                h3TerminalCurlFieldForPair
                  u p₀
                  (σ n)
                  (x n)
              ))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hCurlAbsTendsto.comp
        hPhiTendsto

  have hGradientAbsSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                h3TerminalGradientFieldForPair
                  u p₀
                  (τ n)
                  (y n)
              )
        )
        atTop
        atTop := by

    dsimp only [τ, y]

    change
      Tendsto
        (
          (fun n : ℕ =>
            abs
              (
                h3TerminalGradientFieldForPair
                  u p₀
                  (σ n)
                  (x n)
              ))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hGradientAbsTendsto.comp
        hPhiTendsto

  have hCurlOrientedFunction :
      (
        fun n : ℕ =>
          h3TerminalOrientedValue
            q.1
            (
              h3TerminalCurlFieldForPair
                u p₀
                (τ n)
                (y n)
            )
      )
        =
      (
        fun n : ℕ =>
          abs
            (
              h3TerminalCurlFieldForPair
                u p₀
                (τ n)
                (y n)
            )
      ) := by

    funext n

    dsimp only [τ, y]

    rw [
      ← hCurlOrientationFixed n
    ]

    exact
      h3TerminalOrientedValue_positiveGrowthOrientation_eq_abs
        (
          h3TerminalCurlFieldForPair
            u p₀
            (σ (φ n))
            (x (φ n))
        )

  have hGradientOrientedFunction :
      (
        fun n : ℕ =>
          h3TerminalOrientedValue
            q.2
            (
              h3TerminalGradientFieldForPair
                u p₀
                (τ n)
                (y n)
            )
      )
        =
      (
        fun n : ℕ =>
          abs
            (
              h3TerminalGradientFieldForPair
                u p₀
                (τ n)
                (y n)
            )
      ) := by

    funext n

    dsimp only [τ, y]

    rw [
      ← hGradientOrientationFixed n
    ]

    exact
      h3TerminalOrientedValue_positiveGrowthOrientation_eq_abs
        (
          h3TerminalGradientFieldForPair
            u p₀
            (σ (φ n))
            (x (φ n))
        )

  have hCurlOrientedTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              q.1
              (
                h3TerminalCurlFieldForPair
                  u p₀
                  (τ n)
                  (y n)
              )
        )
        atTop
        atTop := by

    rw [
      hCurlOrientedFunction
    ]

    exact
      hCurlAbsSubsequence

  have hGradientOrientedTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              q.2
              (
                h3TerminalGradientFieldForPair
                  u p₀
                  (τ n)
                  (y n)
              )
        )
        atTop
        atTop := by

    rw [
      hGradientOrientedFunction
    ]

    exact
      hGradientAbsSubsequence

  have hNativeCurlEscape :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p₀
              (τ n)
              (y n)
        )
        q.1 := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p₀
              (τ n)
              (y n))
        (H :=
          fun n : ℕ =>
            h3TerminalCurlFieldForPair
              u p₀
              (τ n)
              (y n))
        (s := q.1)
        (fun n =>
          logValue_h3TerminalNativeCurlForPair
            u p₀
            (τ n)
            (y n))
        hCurlOrientedTendsto

  have hNativeGradientEscape :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p₀
              (τ n)
              (y n)
        )
        q.2 := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p₀
              (τ n)
              (y n))
        (H :=
          fun n : ℕ =>
            h3TerminalGradientFieldForPair
              u p₀
              (τ n)
              (y n))
        (s := q.2)
        (fun n =>
          logValue_h3TerminalNativeGradientForPair
            u p₀
            (τ n)
            (y n))
        hGradientOrientedTendsto

  exact
    ⟨
      p₀,
      q.1,
      q.2,
      τ,
      y,
      hTauData,
      hTauTendsto,
      hEnergySubsequence,
      hDissSubsequence,
      hTransportSubsequence,
      hFrequencySubsequence,
      hCurlOrientedTendsto,
      hGradientOrientedTendsto,
      hNativeCurlEscape,
      hNativeGradientEscape
    ⟩

/--
Neutral positive-growth/native synchronization formulation.
-/
theorem smoothContinuationExtension_or_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradient_doubleOriented_nativeEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T
    )
      ∨
    (
      ∃
        p₀ : H3TerminalCurlGradientPair,
        ∃
          sCurl sGradient : H3TerminalOrientation,
          ∃
            τ : ℕ → ℝ,
            ∃
              y : ℕ → Point3,
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
                  deriv (velocityH3EnergyAt u) (τ n)
              )
                ∧
              Tendsto τ atTop (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    velocityH3EnergyAt u (τ n)
                )
                atTop
                atTop
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    velocityH3DissipationAt u (τ n)
                      /
                    velocityH3EnergyAt u (τ n)
                )
                atTop
                atTop
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    (
                      - velocityH3TransportDerivativeAt u (τ n)
                    )
                      /
                    velocityH3EnergyAt u (τ n)
                )
                atTop
                atTop
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TopCharacteristicFrequencyAt
                      u
                      (τ n)
                )
                atTop
                atTop
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalOrientedValue
                      sCurl
                      (
                        h3TerminalCurlFieldForPair
                          u p₀
                          (τ n)
                          (y n)
                      )
                )
                atTop
                atTop
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalOrientedValue
                      sGradient
                      (
                        h3TerminalGradientFieldForPair
                          u p₀
                          (τ n)
                          (y n)
                      )
                )
                atTop
                atTop
                ∧
              H3TerminalNativeLogDirectionalEscape
                (
                  fun n : ℕ =>
                    h3TerminalNativeCurlForPair
                      u p₀
                      (τ n)
                      (y n)
                )
                sCurl
                ∧
              H3TerminalNativeLogDirectionalEscape
                (
                  fun n : ℕ =>
                    h3TerminalNativeGradientForPair
                      u p₀
                      (τ n)
                      (y n)
                )
                sGradient
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradient_doubleOriented_nativeEscape_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

end

end Euclidean
end Bridge
end PrimeTensor
