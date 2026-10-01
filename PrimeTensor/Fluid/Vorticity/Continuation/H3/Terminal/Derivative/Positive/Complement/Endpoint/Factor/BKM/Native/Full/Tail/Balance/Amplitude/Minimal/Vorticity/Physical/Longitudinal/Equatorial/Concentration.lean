import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Escape

/-!
# Scale-invariant shrinking equatorial concentration

The previous checkpoint produced a scaled bad-cone lower bound

    κ² ε² / 2
      <
    scaledBadConeDefect(κ).

Since the scaled defect is exactly `κ²` times the ordinary bad-cone L² mass,
the factor `κ²` can be canceled whenever `κ > 0`.  The resulting lower bound

    ε² / 2
      <
    badConeDefect(κ)

is uniform in the aperture.

This permits a diagonal choice

    κ_n = 1 / (n + 1)

together with two strict times `s_n,t_n -> T` such that the longitudinal
difference keeps at least `ε²/2` of L² mass in the shrinking equatorial cone

    |ξ_i| < κ_n |ξ|.

Thus, on the branch consisting of hypothetical nonextension plus one surviving
physical-vorticity strong-H³ endpoint, the longitudinal spectral defect
concentrates into arbitrarily thin angular neighborhoods of the equator.

This remains a conditional necessary mechanism and does not assert existence
of a nonextendible solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialConcentration
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Unscaled equatorial defect -/

/--
Unscaled longitudinal square defect restricted to the angular bad cone.
-/
noncomputable def h3TerminalLongitudinalBadConeSquareDefect
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
    ‖h3TerminalSpectralDifferenceAt G H i ξ‖ ^ 2

/--
The scaled bad-cone defect is exactly `κ²` times the unscaled bad-cone defect.
-/
theorem h3TerminalLongitudinalBadConeScaledSquareDefect_eq_sq_mul
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalLongitudinalBadConeScaledSquareDefect
        i κ G H
      =
    κ ^ 2 *
      h3TerminalLongitudinalBadConeSquareDefect
        i κ G H := by

  unfold
    h3TerminalLongitudinalBadConeScaledSquareDefect
    h3TerminalLongitudinalBadConeSquareDefect

  calc
    (∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
        (
          κ *
            ‖h3TerminalSpectralDifferenceAt G H i ξ‖
        ) ^ 2)
        =
      ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
        κ ^ 2 *
          ‖h3TerminalSpectralDifferenceAt G H i ξ‖ ^ 2 := by

          apply integral_congr_ae

          filter_upwards with ξ

          ring

    _ =
      κ ^ 2 *
        ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
          ‖h3TerminalSpectralDifferenceAt G H i ξ‖ ^ 2 := by

          rw [integral_const_mul]

/-! ## Cancel the aperture scaling -/

/--
The recurrent scaled lower bound yields a scale-invariant lower bound on the
ordinary bad-cone L² defect.
-/
theorem exists_arbitrarilyLate_longitudinalBadConeSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {κ ε : ℝ}
    (hκ : 0 < κ)
    (hε : 0 < ε) :
    ∀ η : ℝ,
      0 < η →
      ∃
        s : ℝ,
        ∃ hs : s ∈ Set.Ioo (0 : ℝ) T,
        ∃
          t : ℝ,
          ∃ ht : t ∈ Set.Ioo (0 : ℝ) T,
            dist s T < η
              ∧
            dist t T < η
              ∧
            ε ^ 2 / 2
              <
            h3TerminalLongitudinalBadConeSquareDefect
              i κ
              (h3TerminalVelocitySpectralStateAt hH3 s hs)
              (h3TerminalVelocitySpectralStateAt hH3 t ht) := by

  intro η hη

  obtain
    ⟨
      s,
      hs,
      t,
      ht,
      hsη,
      htη,
      hScaled
    ⟩ :=
    exists_arbitrarilyLate_longitudinalBadConeScaledSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hκ
      hε
      η
      hη

  rw [
    h3TerminalLongitudinalBadConeScaledSquareDefect_eq_sq_mul
  ] at hScaled

  have hκ2 :
      0 < κ ^ 2 :=
    pow_pos
      hκ
      2

  have hMul :
      κ ^ 2 * (ε ^ 2 / 2)
        <
      κ ^ 2 *
        h3TerminalLongitudinalBadConeSquareDefect
          i κ
          (h3TerminalVelocitySpectralStateAt hH3 s hs)
          (h3TerminalVelocitySpectralStateAt hH3 t ht) := by

    convert hScaled using 1 <;> ring

  have hUnscaled :
      ε ^ 2 / 2
        <
      h3TerminalLongitudinalBadConeSquareDefect
        i κ
        (h3TerminalVelocitySpectralStateAt hH3 s hs)
        (h3TerminalVelocitySpectralStateAt hH3 t ht) :=
    lt_of_mul_lt_mul_left
      hMul
      (le_of_lt hκ2)

  exact
    ⟨
      s,
      hs,
      t,
      ht,
      hsη,
      htη,
      hUnscaled
    ⟩

/-! ## Shrinking-aperture concentration sequence -/

/--
Under hypothetical nonextension and one surviving physical-vorticity
strong-H³ endpoint, every fixed separation scale `ε > 0` admits two strict
terminal sequences `s_n,t_n -> T` such that the ordinary longitudinal
bad-cone square defect stays above `ε²/2` while the aperture

    κ_n = 1/(n+1)

tends to zero.
-/
theorem exists_shrinkingEquatorialCone_longitudinalBadConeSquareDefect_sequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s t : ℕ → ℝ,
      ∃ hs :
        ∀ n : ℕ,
          s n ∈ Set.Ioo (0 : ℝ) T,
        ∃ ht :
          ∀ n : ℕ,
            t n ∈ Set.Ioo (0 : ℝ) T,
          (
            Tendsto s atTop (𝓝 T)
          )
            ∧
          (
            Tendsto t atTop (𝓝 T)
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                (1 : ℝ) / ((n : ℝ) + 1)
            )
            atTop
            (𝓝 0)
            ∧
          (
            ∀ n : ℕ,
              dist (s n) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              dist (t n) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              ε ^ 2 / 2
                <
              h3TerminalLongitudinalBadConeSquareDefect
                i
                ((1 : ℝ) / ((n : ℝ) + 1))
                (h3TerminalVelocitySpectralStateAt
                  hH3
                  (s n)
                  (hs n))
                (h3TerminalVelocitySpectralStateAt
                  hH3
                  (t n)
                  (ht n))
          ) := by

  have hChoice :
      ∀ n : ℕ,
        ∃
          s : ℝ,
          ∃ hs : s ∈ Set.Ioo (0 : ℝ) T,
            ∃
              t : ℝ,
              ∃ ht : t ∈ Set.Ioo (0 : ℝ) T,
                dist s T
                    <
                  (1 : ℝ) / ((n : ℝ) + 1)
                  ∧
                dist t T
                    <
                  (1 : ℝ) / ((n : ℝ) + 1)
                  ∧
                ε ^ 2 / 2
                    <
                  h3TerminalLongitudinalBadConeSquareDefect
                    i
                    ((1 : ℝ) / ((n : ℝ) + 1))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      s
                      hs)
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      t
                      ht) := by

    intro n

    have hκ :
        0
          <
        (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    exact
      exists_arbitrarilyLate_longitudinalBadConeSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hκ
        hε
        ((1 : ℝ) / ((n : ℝ) + 1))
        hκ

  choose s hs t ht hData using hChoice

  have hInv :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / ((n : ℝ) + 1)
        )
        atTop
        (𝓝 0) := by

    simpa only [
      Nat.cast_add,
      Nat.cast_one
    ] using
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hNearT :
      ∀
        f : ℕ → ℝ,
        (
          ∀ n : ℕ,
            dist (f n) T
              <
            (1 : ℝ) / ((n : ℝ) + 1)
        ) →
        Tendsto f atTop (𝓝 T) := by

    intro f hf

    rw [Metric.tendsto_atTop]

    intro δ hδ

    obtain
      ⟨
        N : ℕ,
        hN
      ⟩ :=
      exists_nat_gt
        (1 / δ)

    refine
      ⟨
        N,
        ?_
      ⟩

    intro n hn

    have hCast :
        (N : ℝ) ≤ (n : ℝ) := by
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
        1 / ((N : ℝ) + 1)
          <
        δ := by

      have hNPlus :
          1 / δ
            <
          (N : ℝ) + 1 := by
        linarith

      have hMulRaw :
          1
            <
          ((N : ℝ) + 1) * δ :=
        (div_lt_iff₀ hδ).1
          hNPlus

      have hMul :
          1
            <
          δ * ((N : ℝ) + 1) := by
        simpa only [mul_comm] using
          hMulRaw

      exact
        (div_lt_iff₀ hDenN).2
          (by
            simpa only [one_mul] using
              hMul)

    have hSmall :
        (1 : ℝ) / ((n : ℝ) + 1)
          <
        δ :=
      lt_of_le_of_lt
        hInvN
        hSmallN

    exact
      lt_trans
        (hf n)
        hSmall

  have hSTendsto :
      Tendsto s atTop (𝓝 T) :=
    hNearT
      s
      (fun n =>
        (hData n).1)

  have hTTendsto :
      Tendsto t atTop (𝓝 T) :=
    hNearT
      t
      (fun n =>
        (hData n).2.1)

  refine
    ⟨
      s,
      t,
      hs,
      ht,
      hSTendsto,
      hTTendsto,
      hInv,
      ?_
    ⟩

  intro n

  exact
    hData n

end

end Euclidean
end Bridge
end PrimeTensor
