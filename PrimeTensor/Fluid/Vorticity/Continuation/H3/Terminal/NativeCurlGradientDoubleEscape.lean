import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedCurlGradientDoubleOrientation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeVorticityOrientationEscape

/-!
# One-sided native escape for both members of the fixed curl / gradient pair

The fixed double-orientation theorem gives, under hypothetical nonextension,

* one fixed structurally valid curl / constituent-gradient pair,
* one fixed orientation for the curl,
* one fixed orientation for the constituent gradient, and
* one common localized terminal spacetime sequence

on which both oriented real quantities tend to `+∞`.

Both real quantities have exact native multiplicative representatives.

For the curl component this is the corresponding `mulVorticityX/Y/Z` ratio.
For the constituent gradient this is the native spatial derivative

    mulSpatial3.d i (fun y => (u t y).component j) x.

Their logarithms are exactly the real curl and real logged velocity-gradient
entries.  Hence both native states have fixed one-sided logarithmic escape on
the same terminal spacetime sequence.

No native order on `MulReal` is introduced.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Native representatives of the packaged structural pair -/

noncomputable def h3TerminalNativeCurlForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    H3TerminalCurlGradientPair → ℝ → Point3 → MulReal
  | .x_yz, t, x => mulVorticityX u t x
  | .x_zy, t, x => mulVorticityX u t x
  | .y_zx, t, x => mulVorticityY u t x
  | .y_xz, t, x => mulVorticityY u t x
  | .z_xy, t, x => mulVorticityZ u t x
  | .z_yx, t, x => mulVorticityZ u t x

noncomputable def h3TerminalNativeGradientForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair) :
    ℝ → Point3 → MulReal :=
  fun t x =>
    mulSpatial3.d
      (h3TerminalGradientDerivativeAxisForPair p)
      (
        fun y =>
          (u t y).component
            (h3TerminalGradientComponentAxisForPair p)
      )
      x

/-! ## Exact logarithmic bridges -/

theorem logValue_h3TerminalNativeCurlForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (h3TerminalNativeCurlForPair u p t x)
      =
    h3TerminalCurlFieldForPair u p t x := by

  cases p <;>
    simp only [
      h3TerminalNativeCurlForPair,
      h3TerminalCurlFieldForPair,
      logValue_mulVorticityX,
      logValue_mulVorticityY,
      logValue_mulVorticityZ
    ]

theorem logValue_h3TerminalNativeGradientForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (h3TerminalNativeGradientForPair u p t x)
      =
    h3TerminalGradientFieldForPair u p t x := by

  unfold h3TerminalNativeGradientForPair
  unfold h3TerminalGradientFieldForPair

  have hLog :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      (h3TerminalGradientDerivativeAxisForPair p)
      (
        fun y =>
          (u t y).component
            (h3TerminalGradientComponentAxisForPair p)
      )
      x

  simpa [
    PrimeTensor.Bridge.logSpaceTimeVectorField,
    PrimeTensor.Bridge.logVectorField
  ] using hLog.symm

/-! ## Native double-directional escape package -/

def H3TerminalNativeCurlGradientDoubleDirectionalEscape
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
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sCurl
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeCurlForPair
                    u p
                    (τ n)
                    (x n)
                )
            )
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sGradient
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeGradientForPair
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

/--
Transport one fixed double-oriented real curl/gradient sequence through the
exact native logarithmic bridges.
-/
theorem nativeCurlGradientDoubleDirectionalEscape_of_realSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hSeq :
      H3TerminalScalarDoubleOrientedPairSamePointBlowupSequence
        a T
        (h3TerminalCurlFieldForPair u p)
        (h3TerminalGradientFieldForPair u p)
        sCurl
        sGradient) :
    H3TerminalNativeCurlGradientDoubleDirectionalEscape
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hCurlTendsto,
      hGradientTendsto
    ⟩ :=
    hSeq

  have hNativeCurl :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        )
        sCurl := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n))
        (H :=
          fun n : ℕ =>
            h3TerminalCurlFieldForPair
              u p
              (τ n)
              (x n))
        (s := sCurl)
        (fun n =>
          logValue_h3TerminalNativeCurlForPair
            u p
            (τ n)
            (x n))
        hCurlTendsto

  have hNativeGradient :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n)
        )
        sGradient := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n))
        (H :=
          fun n : ℕ =>
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (x n))
        (s := sGradient)
        (fun n =>
          logValue_h3TerminalNativeGradientForPair
            u p
            (τ n)
            (x n))
        hGradientTendsto

  refine
    ⟨
      τ,
      x,
      ?_,
      hTauTendsto,
      hNativeCurl,
      hNativeGradient
    ⟩

  intro n

  refine
    ⟨
      (hτ n).1,
      (hτ n).2.1,
      ?_,
      ?_
    ⟩

  · rw [
      logValue_h3TerminalNativeCurlForPair
        u p
        (τ n)
        (x n)
    ]

    exact
      (hτ n).2.2.1

  · rw [
      logValue_h3TerminalNativeGradientForPair
        u p
        (τ n)
        (x n)
    ]

    exact
      (hτ n).2.2.2

/-! ## Native pair escape under hypothetical nonextension -/

/--
Under hypothetical nonextension, there is one fixed structurally valid native
curl/gradient pair and fixed orientations for both members such that, on one
common localized terminal spacetime sequence, both logarithmic coordinates
escape one-sidedly.

Each direction is independent: the curl and gradient may each escape toward
`+∞` or `-∞`, according to their respective fixed orientations.
-/
theorem fixed_nativeCurlGradient_doubleDirectionalEscape_of_noH3PathExtension
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
        H3TerminalNativeCurlGradientDoubleDirectionalEscape
          u a T p sCurl sGradient := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hSeq
    ⟩ :=
    fixed_curl_constituentGradient_doubleOriented_samePoint_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  exact
    ⟨
      p,
      sCurl,
      sGradient,
      nativeCurlGradientDoubleDirectionalEscape_of_realSequence
        hSeq
    ⟩

/-! ## Neutral package -/

/--
Neutral multiplicative terminal formulation.

Either the H³ path extends smoothly, or one fixed native curl/gradient
structural pair has fixed one-sided logarithmic escape directions for both
members on the same terminal spacetime sequence.
-/
theorem smoothContinuationExtension_or_fixed_nativeCurlGradient_doubleDirectionalEscape
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
          H3TerminalNativeCurlGradientDoubleDirectionalEscape
            u a T p sCurl sGradient
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
          fixed_nativeCurlGradient_doubleDirectionalEscape_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
