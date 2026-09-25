import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeCurlEnstrophyQuadratic

/-!
# Complementary-gradient terminal dichotomy

For each packaged curl / constituent-gradient pair, the fixed curl component
contains exactly two first velocity derivatives.  The preceding development
selects one of them and fixes one-sided terminal orientations for

* the curl component, and
* the selected constituent derivative.

This file tracks the other derivative in the same curl identity.

If the selected derivative occurs with positive curl sign, then

    complement = selected - curl.

If the selected derivative occurs with negative curl sign, then

    complement = selected + curl.

Equivalently, with `selectedCurlSign` encoded as an orientation,

    complement
      =
    selected - orientedValue selectedCurlSign curl.

This produces an exhaustive neutral dichotomy.

In the sign combinations where the two terms on the right reinforce, the
complementary derivative is forced to escape in the selected-gradient
orientation on the same spacetime sequence.  Quantitatively, the existing
bounds larger than `n` improve to

    2 n < orientedValue sGradient (logValue nativeComplement).

In the remaining sign combinations, the exact identity permits cancellation.
No divergence of the complementary derivative is asserted there.

All terminal statements remain necessary consequences conditional on
hypothetical failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Complementary derivative for each structural pair -/

def h3TerminalComplementDerivativeAxisForPair :
    H3TerminalCurlGradientPair →
      PrimeTensor.Axis Depth.three
  | .x_yz => zAxis
  | .x_zy => yAxis
  | .y_zx => xAxis
  | .y_xz => zAxis
  | .z_xy => yAxis
  | .z_yx => xAxis

def h3TerminalComplementComponentAxisForPair :
    H3TerminalCurlGradientPair →
      PrimeTensor.Axis Depth.three
  | .x_yz => yAxis
  | .x_zy => zAxis
  | .y_zx => zAxis
  | .y_xz => xAxis
  | .z_xy => xAxis
  | .z_yx => yAxis

noncomputable def h3TerminalComplementGradientFieldForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair) :
    ℝ → Point3 → ℝ :=
  fun t x =>
    spatial3.d
      (h3TerminalComplementDerivativeAxisForPair p)
      (
        fun y =>
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u t y
          ).component
            (h3TerminalComplementComponentAxisForPair p)
      )
      x

noncomputable def h3TerminalNativeComplementGradientForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair) :
    ℝ → Point3 → MulReal :=
  fun t x =>
    mulSpatial3.d
      (h3TerminalComplementDerivativeAxisForPair p)
      (
        fun y =>
          (u t y).component
            (h3TerminalComplementComponentAxisForPair p)
      )
      x

/--
Orientation encoding whether the already-selected constituent derivative
occurs with positive or negative sign in the curl identity.
-/
def h3TerminalSelectedCurlSignForPair :
    H3TerminalCurlGradientPair →
      H3TerminalOrientation
  | .x_yz => .positive
  | .x_zy => .negative
  | .y_zx => .positive
  | .y_xz => .negative
  | .z_xy => .positive
  | .z_yx => .negative

/-! ## Exact real and native identities -/

/--
Unified exact identity for the complementary derivative:

    complement = selected - oriented(selectedCurlSign, curl).
-/
theorem h3TerminalComplementGradientFieldForPair_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    h3TerminalComplementGradientFieldForPair
        u p t x
      =
    h3TerminalGradientFieldForPair
        u p t x
      -
    h3TerminalOrientedValue
      (h3TerminalSelectedCurlSignForPair p)
      (
        h3TerminalCurlFieldForPair
          u p t x
      ) := by

  cases p <;>
    simp [
      h3TerminalComplementGradientFieldForPair,
      h3TerminalComplementDerivativeAxisForPair,
      h3TerminalComplementComponentAxisForPair,
      h3TerminalGradientFieldForPair,
      h3TerminalGradientDerivativeAxisForPair,
      h3TerminalGradientComponentAxisForPair,
      h3TerminalSelectedCurlSignForPair,
      h3TerminalCurlFieldForPair,
      h3TerminalOrientedValue,
      realVorticityX,
      realVorticityY,
      realVorticityZ
    ] <;>
    ring

/--
Exact logarithmic bridge for the complementary native velocity derivative.
-/
theorem logValue_h3TerminalNativeComplementGradientForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeComplementGradientForPair
            u p t x
        )
      =
    h3TerminalComplementGradientFieldForPair
      u p t x := by

  unfold h3TerminalNativeComplementGradientForPair
  unfold h3TerminalComplementGradientFieldForPair

  have hLog :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      (h3TerminalComplementDerivativeAxisForPair p)
      (
        fun y =>
          (u t y).component
            (h3TerminalComplementComponentAxisForPair p)
      )
      x

  simpa [
    PrimeTensor.Bridge.logSpaceTimeVectorField,
    PrimeTensor.Bridge.logVectorField
  ] using hLog.symm

/-! ## Forced versus cancellation-compatible sign regimes -/

/--
The orientation combinations in which the complementary derivative is forced
to diverge.

For a positive-sign selected constituent (`curl = selected - complement`),
opposite curl/selected orientations reinforce in the complement.

For a negative-sign selected constituent (`curl = complement - selected`),
equal curl/selected orientations reinforce in the complement.
-/
def H3TerminalComplementForcedRegime
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
  match h3TerminalSelectedCurlSignForPair p with
  | .positive =>
      sCurl ≠ sGradient
  | .negative =>
      sCurl = sGradient

/--
The remaining orientation combinations are precisely the cases in which the
exact curl identity permits leading-order cancellation.
-/
def H3TerminalComplementCancellationRegime
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
  ¬ H3TerminalComplementForcedRegime
      p sCurl sGradient

/-! ## Quantitative reinforcement in the forced regime -/

/--
In a forced sign regime, the synchronized bounds

    n < oriented curl,
    n < oriented selected gradient

imply the sharper complementary bound

    2 n < oriented complementary gradient

at the same spacetime point.
-/
theorem two_mul_natCast_lt_oriented_complement_of_forcedRegime
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (hForced :
      H3TerminalComplementForcedRegime
        p sCurl sGradient)
    (n : ℕ)
    (t : ℝ)
    (x : Point3)
    (hCurl :
      (n : ℝ)
        <
      h3TerminalOrientedValue
        sCurl
        (
          PrimeTensor.Bridge.MulReal.logValue
            (
              h3TerminalNativeCurlForPair
                u p t x
            )
        ))
    (hGradient :
      (n : ℝ)
        <
      h3TerminalOrientedValue
        sGradient
        (
          PrimeTensor.Bridge.MulReal.logValue
            (
              h3TerminalNativeGradientForPair
                u p t x
            )
        )) :
    2 * (n : ℝ)
      <
    h3TerminalOrientedValue
      sGradient
      (
        PrimeTensor.Bridge.MulReal.logValue
          (
            h3TerminalNativeComplementGradientForPair
              u p t x
          )
      ) := by

  rw [
    logValue_h3TerminalNativeCurlForPair
  ] at hCurl

  rw [
    logValue_h3TerminalNativeGradientForPair
  ] at hGradient

  rw [
    logValue_h3TerminalNativeComplementGradientForPair,
    h3TerminalComplementGradientFieldForPair_eq
  ]

  cases p <;>
    cases sCurl <;>
    cases sGradient <;>
    simp [
      H3TerminalComplementForcedRegime,
      h3TerminalSelectedCurlSignForPair,
      h3TerminalOrientedValue
    ] at hForced hCurl hGradient ⊢ <;>
    linarith

/-! ## Forced complementary native escape on the same sequence -/

def H3TerminalNativeComplementGradientForcedCascade
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
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
          2 * (n : ℝ)
            <
          h3TerminalOrientedValue
            sGradient
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ n)
                    (x n)
                )
            )
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        )
        sCurl
        ∧
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n)
        )
        sGradient
        ∧
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ n)
              (x n)
        )
        sGradient

private theorem tendsto_atTop_of_two_natCast_lt
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        2 * (n : ℝ) < f n) :
    Tendsto f atTop atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt
      (M / 2)

  filter_upwards
    [eventually_ge_atTop N]
    with n hn

  have hNLe :
      (N : ℝ) ≤ n := by
    exact_mod_cast hn

  have hMlt :
      M < 2 * (n : ℝ) := by
    linarith

  exact
    le_of_lt
      (
        lt_trans
          hMlt
          (hf n)
      )

/--
In a forced sign regime, the complementary native derivative has one-sided
logarithmic escape in the same orientation as the selected gradient, on the
same terminal spacetime sequence.
-/
theorem nativeComplementGradientForcedCascade_of_doubleDirectionalEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hForced :
      H3TerminalComplementForcedRegime
        p sCurl sGradient)
    (hDirectional :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementGradientForcedCascade
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional
    ⟩ :=
    hDirectional

  have hComplementBound :
      ∀ n : ℕ,
        2 * (n : ℝ)
          <
        h3TerminalOrientedValue
          sGradient
          (
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ n)
                  (x n)
              )
          ) := by

    intro n

    exact
      two_mul_natCast_lt_oriented_complement_of_forcedRegime
        u p
        sCurl sGradient
        hForced
        n
        (τ n)
        (x n)
        (hτ n).2.2.1
        (hτ n).2.2.2

  have hComplementOrientedTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sGradient
              (
                PrimeTensor.Bridge.MulReal.logValue
                  (
                    h3TerminalNativeComplementGradientForPair
                      u p
                      (τ n)
                      (x n)
                  )
              )
        )
        atTop
        atTop :=
    tendsto_atTop_of_two_natCast_lt
      hComplementBound

  have hComplementDirectional :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ n)
              (x n)
        )
        sGradient := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ n)
              (x n))
        (H :=
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ n)
                  (x n)
              ))
        (s := sGradient)
        (fun n => rfl)
        hComplementOrientedTendsto

  refine
    ⟨
      τ,
      x,
      ?_,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional,
      hComplementDirectional
    ⟩

  intro n

  exact
    ⟨
      (hτ n).1,
      (hτ n).2.1,
      hComplementBound n
    ⟩

/-! ## Exhaustive neutral terminal dichotomy -/

/--
Under hypothetical nonextension, the fixed synchronized native curl/gradient
pair lies in exactly the regime supplied by its fixed orientations.

If the signs reinforce, the complementary native derivative is forced to
escape one-sidedly on the same sequence, with quantitative lower bound `2n`.

Otherwise the orientation combination is explicitly retained as a
cancellation-compatible regime; no complementary-gradient divergence is
claimed.
-/
theorem fixed_nativeComplementGradient_forced_or_cancellation_of_noH3PathExtension
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
        (
          (
            H3TerminalComplementForcedRegime
              p sCurl sGradient
              ∧
            H3TerminalNativeComplementGradientForcedCascade
              u a T p sCurl sGradient
          )
            ∨
          H3TerminalComplementCancellationRegime
            p sCurl sGradient
        ) := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hDirectional
    ⟩ :=
    fixed_nativeCurlGradient_doubleDirectionalEscape_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  by_cases hForced :
      H3TerminalComplementForcedRegime
        p sCurl sGradient

  · exact
      ⟨
        p,
        sCurl,
        sGradient,
        Or.inl
          ⟨
            hForced,
            nativeComplementGradientForcedCascade_of_doubleDirectionalEscape
              hForced
              hDirectional
          ⟩
      ⟩

  · exact
      ⟨
        p,
        sCurl,
        sGradient,
        Or.inr hForced
      ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative exposing the exact complementary-gradient
sign dichotomy.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_forced_or_cancellation
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
          (
            (
              H3TerminalComplementForcedRegime
                p sCurl sGradient
                ∧
              H3TerminalNativeComplementGradientForcedCascade
                u a T p sCurl sGradient
            )
              ∨
            H3TerminalComplementCancellationRegime
              p sCurl sGradient
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
          fixed_nativeComplementGradient_forced_or_cancellation_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
