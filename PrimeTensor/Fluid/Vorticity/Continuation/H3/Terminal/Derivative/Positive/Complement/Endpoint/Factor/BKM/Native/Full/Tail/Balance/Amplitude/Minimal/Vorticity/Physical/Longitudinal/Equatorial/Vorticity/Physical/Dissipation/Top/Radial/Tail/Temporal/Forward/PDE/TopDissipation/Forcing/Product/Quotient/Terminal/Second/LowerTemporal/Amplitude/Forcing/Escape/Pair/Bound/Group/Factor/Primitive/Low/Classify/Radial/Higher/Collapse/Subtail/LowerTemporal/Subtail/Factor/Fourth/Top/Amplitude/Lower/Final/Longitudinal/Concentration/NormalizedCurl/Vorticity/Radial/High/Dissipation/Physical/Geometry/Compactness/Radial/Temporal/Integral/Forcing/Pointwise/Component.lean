import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component

/-!
# Freeze the canonical cubic-forcing coordinate

The canonical pointwise forcing-rate witness gives

    δ / (2 Δt_n) < fullForcingCubicMassProfile (r_n),

with `Δt_n -> 0`.

The full cubic profile is exactly

    (2π)^6 * Σ_{j : Fin 3} ‖F'''_j(r_n)‖₂².

Therefore one coordinate carries at least one third of the normalized cubic
mass.  A finite pigeonhole extraction freezes that coordinate without leaving
the canonical witness lineage.

Along the extracted subsequence one fixed third-radial forcing coordinate
satisfies the explicit reciprocal-width estimate

    δ / (6 (2π)^6 Δt_n) < ‖F'''_{j₀}(r_n)‖₂²,

and hence its Fourier `L²` norm tends to `+∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationFixedThirdRadialForcingComponentCanonicalPointwiseRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              Tendsto
                  (fun n : ℕ => s (φ n))
                  atTop
                  (𝓝 T)
                ∧
              Tendsto
                  (fun n : ℕ => σ (m (q (φ n))))
                  atTop
                  (𝓝 T)
                ∧
              (
                ∀ n : ℕ,
                  s (φ n) < σ (m (q (φ n)))
              )
                ∧
              (
                ∀ n : ℕ,
                  r (φ n) ∈
                    Set.Icc
                      (s (φ n))
                      (σ (m (q (φ n))))
              )
                ∧
              Tendsto
                  (fun n : ℕ => r (φ n))
                  atTop
                  (𝓝 T)
                ∧
              (
                ∀ n : ℕ,
                  δ
                      /
                    (
                      6
                        *
                      (2 * Real.pi) ^ 6
                        *
                      (
                        σ (m (q (φ n)))
                          -
                        s (φ n)
                      )
                    )
                    <
                  (
                    ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                        hH3 hClass j₀ (r (φ n))‖ : ℝ
                  ) ^ 2
              )
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                        hH3 hClass j₀ (r (φ n))‖
                )
                atTop
                atTop

theorem fixedThirdRadialForcingComponentCanonicalPointwiseRateEscapeSubsequenceOf_of_fullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hPointwise :
      H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedThirdRadialForcingComponentCanonicalPointwiseRateEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      m,
      q,
      hmTop,
      hqTop,
      s,
      r,
      hs,
      hσ,
      hsTendsto,
      hSigmaMQ,
      hForward,
      hr,
      hrTendsto,
      hRate,
      _hProfileTop
    ⟩ :=
    hPointwise

  let C : ℝ :=
    (2 * Real.pi) ^ 6

  have hC :
      0 < C := by
    dsimp only [C]
    positivity

  have hrClass :
      ∀ n : ℕ,
        r n ∈ Set.Ioo a T := by

    intro n

    exact
      ⟨
        lt_of_lt_of_le
          (hs n).1
          (hr n).1,
        lt_of_le_of_lt
          (hr n).2
          (hσ (m (q n))).2
      ⟩

  have hCoordinate :
      ∀ n : ℕ,
        ∃ j : Fin 3,
          δ
              /
            (
              6
                *
              C
                *
              (
                σ (m (q n))
                  -
                s n
              )
            )
            <
          (
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j (r n)‖ : ℝ
          ) ^ 2 := by

    intro n

    have hGap :
        0 < σ (m (q n)) - s n :=
      sub_pos.mpr
        (hForward n)

    let A : ℝ :=
      δ
        /
      (
        6
          *
        C
          *
        (
          σ (m (q n))
            -
          s n
        )
      )

    by_contra hNo

    have hEach :
        ∀ j : Fin 3,
          (
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j (r n)‖ : ℝ
          ) ^ 2
            ≤
          A := by

      intro j

      exact
        le_of_not_gt
          (
            fun hj =>
              hNo
                ⟨
                  j,
                  by
                    simpa only [A] using hj
                ⟩
          )

    have hSumLe :
        (
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j (r n)‖ : ℝ
            ) ^ 2
        )
          ≤
        3 * A := by

      calc
        (
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j (r n)‖ : ℝ
            ) ^ 2
        )
            ≤
          ∑ _j : Fin 3, A := by

              exact
                Finset.sum_le_sum
                  (
                    fun j _hj =>
                      hEach j
                  )

        _ =
          3 * A := by
            simp

    have hProfileEq :=
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_sum_norm_sq_thirdRadialPath
        hH3
        hClass
        (hrClass n)

    have hProfileLe :
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass (r n)
          ≤
        δ
          /
        (
          2
            *
          (
            σ (m (q n))
              -
            s n
          )
        ) := by

      rw [hProfileEq]

      calc
        C
            *
          ∑ j : Fin 3,
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j (r n)‖ : ℝ
            ) ^ 2
            ≤
          C * (3 * A) :=
          mul_le_mul_of_nonneg_left
            hSumLe
            hC.le

        _ =
          δ
            /
          (
            2
              *
            (
              σ (m (q n))
                -
              s n
            )
          ) := by

          dsimp only [A]

          have hGapNe :
              σ (m (q n)) - s n ≠ 0 :=
            ne_of_gt
              hGap

          have hCNe :
              C ≠ 0 :=
            ne_of_gt
              hC

          field_simp [hGapNe, hCNe]
          norm_num

    exact
      (
        not_lt_of_ge
          hProfileLe
      )
        (hRate n)

  choose j hCoordinateRate using hCoordinate

  let p : ℕ → Fin 3 :=
    fun n =>
      j n

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ z : Fin 3,
          p n = z :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            p n,
            rfl
          ⟩
      )

  obtain
    ⟨
      j₀,
      hFrequently
    ⟩ :=
    (
      Filter.frequently_exists
    ).1
      hFrequentlySome

  obtain
    ⟨
      φ,
      hPhiMono,
      hFixed
    ⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hPhiTop :
      Tendsto φ atTop atTop :=
    hPhiMono.tendsto_atTop

  have hFixedCoordinate :
      ∀ n : ℕ,
        j (φ n) = j₀ := by

    intro n

    simpa only [p] using
      hFixed n

  have hsPhi :
      Tendsto
        (fun n : ℕ => s (φ n))
        atTop
        (𝓝 T) :=
    hsTendsto.comp
      hPhiTop

  have hSigmaPhi :
      Tendsto
        (fun n : ℕ => σ (m (q (φ n))))
        atTop
        (𝓝 T) :=
    hSigmaMQ.comp
      hPhiTop

  have hrPhi :
      Tendsto
        (fun n : ℕ => r (φ n))
        atTop
        (𝓝 T) :=
    hrTendsto.comp
      hPhiTop

  have hRateFixed :
      ∀ n : ℕ,
        δ
            /
          (
            6
              *
            (2 * Real.pi) ^ 6
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          )
          <
        (
          ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j₀ (r (φ n))‖ : ℝ
        ) ^ 2 := by

    intro n

    have hRaw :=
      hCoordinateRate
        (φ n)

    rw [
      hFixedCoordinate n
    ] at hRaw

    simpa only [C] using
      hRaw

  have hSqTop :
      Tendsto
        (
          fun n : ℕ =>
            (
              ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                  hH3 hClass j₀ (r (φ n))‖ : ℝ
            ) ^ 2
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    let K : ℝ :=
      max M 0 + 1

    have hK :
        0 < K := by

      dsimp only [K]

      have hMax :
          0 ≤ max M 0 :=
        le_max_right
          M
          0

      linarith

    let c : ℝ :=
      δ
        /
      (
        6
          *
        C
          *
        K
      )

    have hc :
        0 < c := by

      dsimp only [c]

      positivity

    have hsLate :
        ∀ᶠ n : ℕ in atTop,
          T - c < s (φ n) :=
      (tendsto_order.1 hsPhi).1
        (T - c)
        (by linarith)

    filter_upwards [hsLate] with n hsLateN

    have hGap :
        0 <
          σ (m (q (φ n)))
            -
          s (φ n) :=
      sub_pos.mpr
        (hForward (φ n))

    have hEndpointUpper :
        σ (m (q (φ n))) < T :=
      (hσ (m (q (φ n)))).2

    have hGapUpper :
        σ (m (q (φ n)))
            -
          s (φ n)
          <
        c := by

      linarith

    have hScalePos :
        0 < 6 * C * K := by
      positivity

    have hScaled :
        (
          σ (m (q (φ n)))
            -
          s (φ n)
        )
          *
        (6 * C * K)
          <
        δ := by

      exact
        (lt_div_iff₀ hScalePos).1
          (by
            simpa only [c] using
              hGapUpper)

    have hDenPos :
        0
          <
        6
          *
        C
          *
        (
          σ (m (q (φ n)))
            -
          s (φ n)
        ) := by

      positivity

    have hKThreshold :
        K
          <
        δ
          /
        (
          6
            *
          C
            *
          (
            σ (m (q (φ n)))
              -
            s (φ n)
          )
        ) := by

      apply
        (lt_div_iff₀ hDenPos).2

      nlinarith [hScaled]

    have hMK :
        M < K := by

      dsimp only [K]

      have hMMax :
          M ≤ max M 0 :=
        le_max_left
          M
          0

      linarith

    exact
      le_of_lt
        (
          lt_trans
            hMK
            (
              lt_trans
                hKThreshold
                (
                  by
                    simpa only [C] using
                      hRateFixed n
                )
            )
        )

  have hNormTop :
      Tendsto
        (
          fun n : ℕ =>
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j₀ (r (φ n))‖
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    let K : ℝ :=
      max M 0 + 1

    have hK :
        0 < K := by

      dsimp only [K]

      have hMax :
          0 ≤ max M 0 :=
        le_max_right
          M
          0

      linarith

    have hSqEventually :
        ∀ᶠ n : ℕ in atTop,
          K ^ 2
            ≤
          (
            ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
                hH3 hClass j₀ (r (φ n))‖ : ℝ
          ) ^ 2 :=
      hSqTop.eventually
        (eventually_ge_atTop (K ^ 2))

    filter_upwards [hSqEventually] with n hSqLower

    have hSqrtLe :=
      Real.sqrt_le_sqrt
        hSqLower

    have hKLeNorm :
        K
          ≤
        ‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass j₀ (r (φ n))‖ := by

      simpa only [
        Real.sqrt_sq_eq_abs,
        abs_of_nonneg hK.le,
        abs_of_nonneg (norm_nonneg _)
      ] using
        hSqrtLe

    have hMK :
        M < K := by

      dsimp only [K]

      have hMMax :
          M ≤ max M 0 :=
        le_max_left
          M
          0

      linarith

    exact
      le_of_lt
        (hMK.trans_le hKLeNorm)

  exact
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      hmTop,
      hqTop,
      hPhiMono,
      s,
      r,
      hs,
      hσ,
      hsPhi,
      hSigmaPhi,
      (fun n => hForward (φ n)),
      (fun n => hr (φ n)),
      hrPhi,
      hRateFixed,
      hNormTop
    ⟩

theorem exists_fixed_terminalSequence_with_canonicalFixedThirdRadialForcingComponentRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
        )
        atTop
        (𝓝 0)
        ∧
      ∃ σ : ℕ → ℝ,
        ∃ hσ :
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T,
          Tendsto σ atTop (𝓝 T)
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal (ε ^ 2 / 64)
                <
              16 *
                h3TerminalPhysicalDissipationBadConeHighRadialMass
                  hH3
                  i
                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                  1
                  (σ n)
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hσ n).1,
                    (hσ n).2
                  ⟩
          )
            ∧
          H3TerminalPhysicalTopDissipationFixedThirdRadialForcingComponentCanonicalPointwiseRateEscapeSubsequenceOf
            hH3 hClass σ := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hPointwise
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalFullForcingCubicPointwiseRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hFixed :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingComponentCanonicalPointwiseRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fixedThirdRadialForcingComponentCanonicalPointwiseRateEscapeSubsequenceOf_of_fullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hPointwise

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hFixed
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
