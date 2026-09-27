import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FixedOrientedNativeCascade
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Quantitative native escape on the positive-growth cascade

The fixed oriented native cascade synchronizes the positive-growth H³ cascade
with one fixed structural curl/gradient pair and fixed one-sided native escape
directions.  The complementary-gradient machinery developed earlier uses a
slightly stronger quantitative sequence interface:

    n < oriented log(nativeCurl_n),
    n < oriented log(nativeGradient_n).

Since both oriented real fields already tend to `+∞`, these indexed lower
bounds can be imposed simultaneously by one further strictly increasing
subsequence.

The extraction preserves:

* the standard localization `T - 1/(n+1) < τ_n < T`;
* the indexed positive-growth bound `n < E'(τ_n)`;
* full H³ energy divergence;
* normalized dissipation divergence;
* normalized adverse-transport divergence;
* top characteristic-frequency divergence;
* the fixed structural pair;
* both fixed orientations;
* both native one-sided escape directions.

The resulting sequence is therefore simultaneously a positive-growth full
cascade and an `H3TerminalNativeCurlGradientDoubleDirectionalEscape`.  This is
the exact interface needed to run the complementary-gradient forced /
cancellation analysis on the positive-growth branch itself.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension, one fixed structural curl/gradient pair and
fixed orientations admit a positive-growth terminal sequence on which both
native logarithmic coordinates exceed the index `n`, while the complete
H³ scalar/frequency cascade is retained.
-/
theorem exists_terminal_positiveGrowth_fullCascade_quantitativeNativeDoubleEscape_of_noH3PathExtension
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
      p : H3TerminalCurlGradientPair,
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
                          (y n)
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
                          (y n)
                      )
                  )
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
            H3TerminalNativeLogDirectionalEscape
              (
                fun n : ℕ =>
                  h3TerminalNativeCurlForPair
                    u p
                    (τ n)
                    (y n)
              )
              sCurl
              ∧
            H3TerminalNativeLogDirectionalEscape
              (
                fun n : ℕ =>
                  h3TerminalNativeGradientForPair
                    u p
                    (τ n)
                    (y n)
              )
              sGradient
              ∧
            H3TerminalNativeCurlGradientDoubleDirectionalEscape
              u a T p sCurl sGradient := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      σ,
      x,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto,
      hFrequencyTendsto,
      hCurlOrientedTendsto,
      hGradientOrientedTendsto,
      _hNativeCurlOld,
      _hNativeGradientOld
    ⟩ :=
    exists_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradient_doubleOriented_nativeEscape_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  have hIndexedEventually :
      ∀ n : ℕ,
        ∀ᶠ k : ℕ in atTop,
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sCurl
            (
              h3TerminalCurlFieldForPair
                u p
                (σ k)
                (x k)
            )
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sGradient
            (
              h3TerminalGradientFieldForPair
                u p
                (σ k)
                (x k)
            ) := by

    intro n

    exact
      (
        hCurlOrientedTendsto.eventually
          (eventually_gt_atTop (n : ℝ))
      ).and
        (
          hGradientOrientedTendsto.eventually
            (eventually_gt_atTop (n : ℝ))
        )

  obtain
    ⟨
      φ,
      hPhiMono,
      hIndexed
    ⟩ :=
    extraction_forall_of_eventually
      hIndexedEventually

  have hPhiTendsto :
      Tendsto φ atTop atTop :=
    hPhiMono.tendsto_atTop

  let τ : ℕ → ℝ :=
    fun n =>
      σ (φ n)

  let y : ℕ → Point3 :=
    fun n =>
      x (φ n)

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

  have hNativeCurlIndexed :
      ∀ n : ℕ,
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
                  (y n)
              )
          ) := by

    intro n

    rw [
      logValue_h3TerminalNativeCurlForPair
    ]

    dsimp only [τ, y]

    exact
      (hIndexed n).1

  have hNativeGradientIndexed :
      ∀ n : ℕ,
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
                  (y n)
              )
          ) := by

    intro n

    rw [
      logValue_h3TerminalNativeGradientForPair
    ]

    dsimp only [τ, y]

    exact
      (hIndexed n).2

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

  have hCurlOrientedSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sCurl
              (
                h3TerminalCurlFieldForPair
                  u p
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
            h3TerminalOrientedValue
              sCurl
              (
                h3TerminalCurlFieldForPair
                  u p
                  (σ n)
                  (x n)
              ))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hCurlOrientedTendsto.comp
        hPhiTendsto

  have hGradientOrientedSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sGradient
              (
                h3TerminalGradientFieldForPair
                  u p
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
            h3TerminalOrientedValue
              sGradient
              (
                h3TerminalGradientFieldForPair
                  u p
                  (σ n)
                  (x n)
              ))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hGradientOrientedTendsto.comp
        hPhiTendsto

  have hNativeCurlEscape :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (y n)
        )
        sCurl := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (y n))
        (H :=
          fun n : ℕ =>
            h3TerminalCurlFieldForPair
              u p
              (τ n)
              (y n))
        (s := sCurl)
        (fun n =>
          logValue_h3TerminalNativeCurlForPair
            u p
            (τ n)
            (y n))
        hCurlOrientedSubsequence

  have hNativeGradientEscape :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (y n)
        )
        sGradient := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (y n))
        (H :=
          fun n : ℕ =>
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (y n))
        (s := sGradient)
        (fun n =>
          logValue_h3TerminalNativeGradientForPair
            u p
            (τ n)
            (y n))
        hGradientOrientedSubsequence

  have hDirectional :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u a T p sCurl sGradient := by

    refine
      ⟨
        τ,
        y,
        ?_,
        hTauTendsto,
        hNativeCurlEscape,
        hNativeGradientEscape
      ⟩

    intro n

    exact
      ⟨
        (hTauData n).1,
        (hTauData n).2.1,
        hNativeCurlIndexed n,
        hNativeGradientIndexed n
      ⟩

  exact
    ⟨
      p,
      sCurl,
      sGradient,
      τ,
      y,
      (
        fun n =>
          ⟨
            (hTauData n).1,
            (hTauData n).2.1,
            (hTauData n).2.2,
            hNativeCurlIndexed n,
            hNativeGradientIndexed n
          ⟩
      ),
      hTauTendsto,
      hEnergySubsequence,
      hDissSubsequence,
      hTransportSubsequence,
      hFrequencySubsequence,
      hNativeCurlEscape,
      hNativeGradientEscape,
      hDirectional
    ⟩

/--
Neutral quantitative positive-growth/native formulation.
-/
theorem smoothContinuationExtension_or_terminal_positiveGrowth_fullCascade_quantitativeNativeDoubleEscape
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
        p : H3TerminalCurlGradientPair,
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
                            (y n)
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
                            (y n)
                        )
                    )
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
              H3TerminalNativeLogDirectionalEscape
                (
                  fun n : ℕ =>
                    h3TerminalNativeCurlForPair
                      u p
                      (τ n)
                      (y n)
                )
                sCurl
                ∧
              H3TerminalNativeLogDirectionalEscape
                (
                  fun n : ℕ =>
                    h3TerminalNativeGradientForPair
                      u p
                      (τ n)
                      (y n)
                )
                sGradient
                ∧
              H3TerminalNativeCurlGradientDoubleDirectionalEscape
                u a T p sCurl sGradient
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
          exists_terminal_positiveGrowth_fullCascade_quantitativeNativeDoubleEscape_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

end

end Euclidean
end Bridge
end PrimeTensor
