import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedCurlGradientOrientation

/-!
# One-sided native vorticity-ratio escape on the synchronized terminal sequence

The fixed-orientation theorem gives, under hypothetical nonextension, one fixed
real curl component and one fixed constituent velocity derivative which diverge
together at the same spacetime points, with the curl orientation fixed.

The multiplicative vorticity bridge is exact:

    logValue (mulVorticityX u t x) = realVorticityX (logSpaceTimeVectorField u) t x,
    logValue (mulVorticityY u t x) = realVorticityY (logSpaceTimeVectorField u) t x,
    logValue (mulVorticityZ u t x) = realVorticityZ (logSpaceTimeVectorField u) t x.

Therefore the corresponding fixed native vorticity ratio has a one-sided
logarithmic escape on the same terminal spacetime sequence:

* positive orientation: its logarithmic coordinate tends to `+∞`;
* negative orientation: its logarithmic coordinate tends to `-∞`.

No linear order on `MulReal` is introduced.  The statement is entirely in the
already-established faithful logarithmic coordinate.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Directional escape of a native logarithmic coordinate -/

def H3TerminalNativeLogDirectionalEscape
    (Ω : ℕ → PrimeTensor.MulReal)
    (s : H3TerminalOrientation) : Prop :=
  match s with
  | .positive =>
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (Ω n)
        )
        atTop
        atTop
  | .negative =>
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (Ω n)
        )
        atTop
        atBot

/--
If a native sequence has logarithmic coordinate `Hₙ`, and the fixed
orientation of `Hₙ` tends to `+∞`, then the native logarithmic coordinate
escapes in the corresponding one-sided direction.
-/
theorem nativeLogDirectionalEscape_of_oriented_log_bridge
    {Ω : ℕ → PrimeTensor.MulReal}
    {H : ℕ → ℝ}
    {s : H3TerminalOrientation}
    (hBridge :
      ∀ n : ℕ,
        PrimeTensor.Bridge.MulReal.logValue
            (Ω n)
          =
        H n)
    (hOriented :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              s
              (H n)
        )
        atTop
        atTop) :
    H3TerminalNativeLogDirectionalEscape
      Ω s := by

  cases s with

  | positive =>

      unfold H3TerminalNativeLogDirectionalEscape

      have hEq :
          (
            fun n : ℕ =>
              PrimeTensor.Bridge.MulReal.logValue
                (Ω n)
          )
            =
          H := by

        funext n

        exact
          hBridge n

      rw [hEq]

      simpa only [
        h3TerminalOrientedValue_positive
      ] using hOriented

  | negative =>

      unfold H3TerminalNativeLogDirectionalEscape

      have hNeg :
          Tendsto
            (fun n : ℕ => - H n)
            atTop
            atTop := by

        simpa only [
          h3TerminalOrientedValue_negative
        ] using hOriented

      have hH :
          Tendsto H atTop atBot := by

        refine
          tendsto_atBot.2
            ?_

        intro M

        have hEventually :
            ∀ᶠ n : ℕ in atTop,
              -M ≤ - H n :=
          hNeg.eventually
            (eventually_ge_atTop (-M))

        filter_upwards
          [hEventually]
          with n hn

        linarith

      have hEq :
          (
            fun n : ℕ =>
              PrimeTensor.Bridge.MulReal.logValue
                (Ω n)
          )
            =
          H := by

        funext n

        exact
          hBridge n

      rw [hEq]

      exact
        hH

/-! ## Native fixed curl / constituent-gradient escape package -/

def H3TerminalNativeCurlGradientOrientedEscape
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (Ω : ℝ → Point3 → PrimeTensor.MulReal)
    (i j : PrimeTensor.Axis Depth.three)
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
                        u (τ n) y
                    ).component j
                )
                (x n)
            )
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            s
            (
              PrimeTensor.Bridge.MulReal.logValue
                (Ω (τ n) (x n))
            )
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                spatial3.d
                  i
                  (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (τ n) y
                      ).component j
                  )
                  (x n)
              )
        )
        atTop
        atTop
        ∧
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            Ω (τ n) (x n)
        )
        s

private theorem nativeCurlGradientOrientedEscape_of_real_orientedSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {Ω : ℝ → Point3 → PrimeTensor.MulReal}
    {H : ℝ → Point3 → ℝ}
    {i j : PrimeTensor.Axis Depth.three}
    {s : H3TerminalOrientation}
    (hBridge :
      ∀ t : ℝ,
        ∀ x : Point3,
          PrimeTensor.Bridge.MulReal.logValue
              (Ω t x)
            =
          H t x)
    (hSeq :
      H3TerminalScalarOrientedPairSamePointBlowupSequence
        a T
        H
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
        s) :
    H3TerminalNativeCurlGradientOrientedEscape
      u a T Ω i j s := by

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hGradientTendsto,
      hOrientedTendsto
    ⟩ :=
    hSeq

  have hNativeDirectional :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            Ω (τ n) (x n)
        )
        s := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            Ω (τ n) (x n))
        (H :=
          fun n : ℕ =>
            H (τ n) (x n))
        (s := s)
        (fun n =>
          hBridge
            (τ n)
            (x n))
        hOrientedTendsto

  refine
    ⟨
      τ,
      x,
      ?_,
      hTauTendsto,
      hGradientTendsto,
      hNativeDirectional
    ⟩

  intro n

  refine
    ⟨
      (hτ n).1,
      (hτ n).2.1,
      (hτ n).2.2.1,
      ?_
    ⟩

  rw [
    hBridge
      (τ n)
      (x n)
  ]

  exact
    (hτ n).2.2.2

/-! ## Native one-sided escape under hypothetical nonextension -/

/--
Under hypothetical nonextension, one of the six structurally valid fixed
curl/constituent-gradient pairs admits a fixed curl orientation and one common
terminal spacetime sequence on which

* the fixed constituent velocity-gradient magnitude tends to `+∞`, and
* the corresponding native vorticity ratio logarithm tends to `+∞` or `-∞`
  according to that fixed orientation.
-/
theorem fixed_nativeVorticityRatio_constituentGradient_orientedEscape_of_noH3PathExtension
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
        H3TerminalNativeCurlGradientOrientedEscape
          u a T
          (mulVorticityX u)
          yAxis zAxis
          s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalNativeCurlGradientOrientedEscape
          u a T
          (mulVorticityX u)
          zAxis yAxis
          s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalNativeCurlGradientOrientedEscape
          u a T
          (mulVorticityY u)
          zAxis xAxis
          s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalNativeCurlGradientOrientedEscape
          u a T
          (mulVorticityY u)
          xAxis zAxis
          s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalNativeCurlGradientOrientedEscape
          u a T
          (mulVorticityZ u)
          xAxis yAxis
          s
    )
      ∨
    (
      ∃ s : H3TerminalOrientation,
        H3TerminalNativeCurlGradientOrientedEscape
          u a T
          (mulVorticityZ u)
          yAxis xAxis
          s
    ) := by

  rcases
      fixed_curl_constituentGradient_oriented_samePoint_blowupSequence_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    with h1 | h2 | h3 | h4 | h5 | h6

  · obtain ⟨s, hs⟩ := h1

    have hSeq := hs

    change
      H3TerminalScalarOrientedPairSamePointBlowupSequence
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
        s
      at hSeq

    exact
      Or.inl
        ⟨
          s,
          nativeCurlGradientOrientedEscape_of_real_orientedSequence
            (Ω := mulVorticityX u)
            (H :=
              fun t x =>
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x)
            (i := yAxis)
            (j := zAxis)
            (s := s)
            (fun t x =>
              logValue_mulVorticityX
                u t x)
            hSeq
        ⟩

  · obtain ⟨s, hs⟩ := h2

    have hSeq := hs

    change
      H3TerminalScalarOrientedPairSamePointBlowupSequence
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
        s
      at hSeq

    exact
      Or.inr
        (
          Or.inl
            ⟨
              s,
              nativeCurlGradientOrientedEscape_of_real_orientedSequence
                (Ω := mulVorticityX u)
                (H :=
                  fun t x =>
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t x)
                (i := zAxis)
                (j := yAxis)
                (s := s)
                (fun t x =>
                  logValue_mulVorticityX
                    u t x)
                hSeq
            ⟩
        )

  · obtain ⟨s, hs⟩ := h3

    have hSeq := hs

    change
      H3TerminalScalarOrientedPairSamePointBlowupSequence
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
        s
      at hSeq

    exact
      Or.inr
        (
          Or.inr
            (
              Or.inl
                ⟨
                  s,
                  nativeCurlGradientOrientedEscape_of_real_orientedSequence
                    (Ω := mulVorticityY u)
                    (H :=
                      fun t x =>
                        realVorticityY
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          t x)
                    (i := zAxis)
                    (j := xAxis)
                    (s := s)
                    (fun t x =>
                      logValue_mulVorticityY
                        u t x)
                    hSeq
                ⟩
            )
        )

  · obtain ⟨s, hs⟩ := h4

    have hSeq := hs

    change
      H3TerminalScalarOrientedPairSamePointBlowupSequence
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
        s
      at hSeq

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
                      nativeCurlGradientOrientedEscape_of_real_orientedSequence
                        (Ω := mulVorticityY u)
                        (H :=
                          fun t x =>
                            realVorticityY
                              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                              t x)
                        (i := xAxis)
                        (j := zAxis)
                        (s := s)
                        (fun t x =>
                          logValue_mulVorticityY
                            u t x)
                        hSeq
                    ⟩
                )
            )
        )

  · obtain ⟨s, hs⟩ := h5

    have hSeq := hs

    change
      H3TerminalScalarOrientedPairSamePointBlowupSequence
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
        s
      at hSeq

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
                          nativeCurlGradientOrientedEscape_of_real_orientedSequence
                            (Ω := mulVorticityZ u)
                            (H :=
                              fun t x =>
                                realVorticityZ
                                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                  t x)
                            (i := xAxis)
                            (j := yAxis)
                            (s := s)
                            (fun t x =>
                              logValue_mulVorticityZ
                                u t x)
                            hSeq
                        ⟩
                    )
                )
            )
        )

  · obtain ⟨s, hs⟩ := h6

    have hSeq := hs

    change
      H3TerminalScalarOrientedPairSamePointBlowupSequence
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
        s
      at hSeq

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
                          nativeCurlGradientOrientedEscape_of_real_orientedSequence
                            (Ω := mulVorticityZ u)
                            (H :=
                              fun t x =>
                                realVorticityZ
                                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                  t x)
                            (i := yAxis)
                            (j := xAxis)
                            (s := s)
                            (fun t x =>
                              logValue_mulVorticityZ
                                u t x)
                            hSeq
                        ⟩
                    )
                )
            )
        )

/-! ## Neutral package -/

/--
Neutral multiplicative terminal formulation.

Either the H³ path extends smoothly, or one fixed native vorticity ratio has a
one-sided logarithmic escape on a common terminal spacetime sequence where one
of its fixed constituent velocity derivatives also diverges in magnitude.
-/
theorem smoothContinuationExtension_or_fixed_nativeVorticityRatio_constituentGradient_orientedEscape
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
          H3TerminalNativeCurlGradientOrientedEscape
            u a T
            (mulVorticityX u)
            yAxis zAxis
            s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalNativeCurlGradientOrientedEscape
            u a T
            (mulVorticityX u)
            zAxis yAxis
            s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalNativeCurlGradientOrientedEscape
            u a T
            (mulVorticityY u)
            zAxis xAxis
            s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalNativeCurlGradientOrientedEscape
            u a T
            (mulVorticityY u)
            xAxis zAxis
            s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalNativeCurlGradientOrientedEscape
            u a T
            (mulVorticityZ u)
            xAxis yAxis
            s
      )
        ∨
      (
        ∃ s : H3TerminalOrientation,
          H3TerminalNativeCurlGradientOrientedEscape
            u a T
            (mulVorticityZ u)
            yAxis xAxis
            s
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
          fixed_nativeVorticityRatio_constituentGradient_orientedEscape_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
