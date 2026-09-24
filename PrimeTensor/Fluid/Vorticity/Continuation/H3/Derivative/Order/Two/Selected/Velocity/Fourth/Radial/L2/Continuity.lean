import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Fifth.Radial.L2.Compact.Bound

/-!
# Selected fourth-radial velocity Fourier L² continuity

The fourth-radial difference estimate has now been reduced to exactly the two
inputs available in the preceding files:

* strong continuity of the unweighted selected raw Fourier `L²` state;
* a uniform fifth-radial selected velocity norm-square bound on every positive
  compact restart slab.

On a compact slab `[a,b]`, the frequency split gives

    ‖F₄(s) - F₄(t)‖²
      ≤ 2 R⁸ ‖F₀(s) - F₀(t)‖²
        + 4 R⁻² (‖F₅(s)‖² + ‖F₅(t)‖²).

For a prescribed `ε`, first choose `R` large enough that the fifth-order tail
is below `ε/2`; with `R` fixed, raw `L²` continuity makes the low-frequency
term below `ε/2`.

The proof deliberately mirrors the already-closed selected-forcing radial
continuity theorem.  A local compact-slab result is proved first and then
promoted to the full strict restart interval by `Set.IccExtend`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityFourthRadialL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-! ## Compact-slab continuity -/

/-- The selected fourth-radial velocity state is strongly continuous on every
positive compact restart slab. -/
theorem continuous_h3PreterminalSelectedVelocityFourthRadialFourierL2OnCompact
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3) :
    Continuous
      (fun s : Set.Icc a b =>
        h3PreterminalSelectedVelocityFourthRadialFourierL2
          hNS ht₀ hE hTail
          ⟨(s : ℝ),
            lt_of_lt_of_le ha s.property.1,
            lt_of_le_of_lt s.property.2 hbR⟩
          j) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let toOpen :
      Set.Icc a b →
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    fun s =>
      ⟨(s : ℝ),
        lt_of_lt_of_le ha s.property.1,
        lt_of_le_of_lt s.property.2 hbR⟩

  let F0 :
      Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3SpectralScalarRawFourierL2
        (W (s : ℝ) j)

  let F4 :
      Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityFourthRadialFourierL2
        hNS ht₀ hE hTail (toOpen s) j

  let F5 :
      Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityFifthRadialFourierL2
        hNS ht₀ hE hTail (toOpen s) j

  have hF0 :
      Continuous F0 := by
    dsimp only [F0, W]
    exact
      (continuous_h3PreterminalSelectedVelocityRawFourierL2
        hNS ht₀ hE hTail j).comp
        continuous_subtype_val

  obtain ⟨B, hB0, hB⟩ :=
    exists_norm_sq_bound_h3PreterminalSelectedVelocityFifthRadialFourierL2OnCompact
      hNS ht₀ hE hTail ha hab hbR

  rw [continuous_iff_continuousAt]
  intro s₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hLowNormTend :
      Tendsto
        (fun s : Set.Icc a b =>
          ‖F0 s - F0 s₀‖)
        (𝓝 s₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hF0.continuousAt

  have hPow :
      Tendsto
        (fun x : ℝ => x ^ 2)
        (𝓝 0)
        (𝓝 ((0 : ℝ) ^ 2)) := by
    exact continuousAt_id.pow 2

  have hLowSqTend :
      Tendsto
        (fun s : Set.Icc a b =>
          ‖F0 s - F0 s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 0) := by
    have hComp := hPow.comp hLowNormTend
    change
      Tendsto
        (fun s : Set.Icc a b =>
          ‖F0 s - F0 s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 ((0 : ℝ) ^ 2))
      at hComp
    norm_num at hComp
    exact hComp

  have hSqTend :
      Tendsto
        (fun s : Set.Icc a b =>
          ‖F4 s - F4 s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 0) := by

    refine tendsto_order.2 ⟨?_, ?_⟩

    · intro c hc
      exact
        Filter.Eventually.of_forall
          (fun s =>
            lt_of_lt_of_le hc
              (sq_nonneg ‖F4 s - F4 s₀‖))

    · intro ε hε

      let R : ℝ :=
        1 + (16 * B) / ε

      have hFrac0 :
          0 ≤ (16 * B) / ε := by
        exact
          div_nonneg
            (mul_nonneg (by norm_num) hB0)
            hε.le

      have hR : 0 < R := by
        dsimp only [R]
        linarith

      have hRone : 1 ≤ R := by
        dsimp only [R]
        linarith

      have hRfrac :
          (16 * B) / ε < R := by
        dsimp only [R]
        linarith

      have hBR :
          16 * B < ε * R := by
        simpa only [mul_comm] using
          (div_lt_iff₀ hε).1 hRfrac

      have hInv0 :
          0 ≤ R⁻¹ :=
        inv_nonneg.mpr hR.le

      have hInvOne :
          R⁻¹ ≤ 1 :=
        (inv_le_one₀ hR).2 hRone

      have hInvSq :
          (R⁻¹) ^ 2 ≤ R⁻¹ := by
        nlinarith [sq_nonneg (R⁻¹)]

      have hSixteen :
          16 * B * R⁻¹ < ε := by
        have hDiv :
            (16 * B) / R < ε :=
          (div_lt_iff₀ hR).2 hBR
        simpa only [div_eq_mul_inv, mul_assoc] using hDiv

      have hTailBudget :
          8 * B * (R⁻¹) ^ 2 < ε / 2 := by
        have hStep :
            8 * B * (R⁻¹) ^ 2
              ≤
            8 * B * R⁻¹ :=
          mul_le_mul_of_nonneg_left
            hInvSq
            (mul_nonneg (by norm_num) hB0)
        have hHalf :
            8 * B * R⁻¹ < ε / 2 := by
          nlinarith
        exact hStep.trans_lt hHalf

      let C : ℝ :=
        2 * (R ^ 4) ^ 2

      have hC0 : 0 ≤ C := by
        dsimp only [C]
        positivity

      have hC1 : 0 < C + 1 := by
        linarith

      let η : ℝ :=
        ε / (2 * (C + 1))

      have hη : 0 < η := by
        dsimp only [η]
        positivity

      have hLowEventually :
          ∀ᶠ s in 𝓝 s₀,
            ‖F0 s - F0 s₀‖ ^ 2 < η :=
        (tendsto_order.1 hLowSqTend).2 η hη

      filter_upwards [hLowEventually] with s hsLow

      have hInterp :=
        norm_sq_h3PreterminalSelectedVelocityFourthRadialFourierL2_sub_le
          hNS ht₀ hE hTail hR j
          (toOpen s) (toOpen s₀)

      have hηEq :
          (C + 1) * η = ε / 2 := by
        dsimp only [η]
        field_simp [ne_of_gt hC1]

      have hLow :
          C * ‖F0 s - F0 s₀‖ ^ 2
            <
          ε / 2 := by
        have hCLe :
            C ≤ C + 1 := by
          linarith

        have hSq0 :
            0 ≤ ‖F0 s - F0 s₀‖ ^ 2 :=
          sq_nonneg _

        have hStep1 :
            C * ‖F0 s - F0 s₀‖ ^ 2
              ≤
            (C + 1) *
              ‖F0 s - F0 s₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            hCLe hSq0

        have hStep2 :
            (C + 1) *
                ‖F0 s - F0 s₀‖ ^ 2
              <
            (C + 1) * η :=
          mul_lt_mul_of_pos_left
            hsLow hC1

        exact
          lt_of_le_of_lt hStep1
            (hStep2.trans_eq hηEq)

      have hNext :
          ‖F5 s‖ ^ 2 + ‖F5 s₀‖ ^ 2
            ≤
          B + B := by
        exact
          add_le_add
            (by
              dsimp only [F5, toOpen]
              exact hB s j)
            (by
              dsimp only [F5, toOpen]
              exact hB s₀ j)

      have hTailSmall :
          4 * (R⁻¹) ^ 2 *
              (‖F5 s‖ ^ 2 + ‖F5 s₀‖ ^ 2)
            <
          ε / 2 := by
        calc
          4 * (R⁻¹) ^ 2 *
              (‖F5 s‖ ^ 2 + ‖F5 s₀‖ ^ 2)
              ≤
            4 * (R⁻¹) ^ 2 *
              (B + B) :=
            mul_le_mul_of_nonneg_left
              hNext
              (mul_nonneg
                (by norm_num)
                (sq_nonneg _))
          _ =
            8 * B * (R⁻¹) ^ 2 := by
            ring
          _ < ε / 2 :=
            hTailBudget

      have hSqLt :
          ‖F4 s - F4 s₀‖ ^ 2 < ε := by

        have hInterp' :
            ‖F4 s - F4 s₀‖ ^ 2
              ≤
            2 * (R ^ 4) ^ 2 *
                ‖F0 s - F0 s₀‖ ^ 2
              +
            4 * (R⁻¹) ^ 2 *
              (‖F5 s‖ ^ 2 +
               ‖F5 s₀‖ ^ 2) := by
          dsimp only [F4, F5, F0, toOpen, W, U₀, hA, hU₀]
          exact hInterp

        calc
          ‖F4 s - F4 s₀‖ ^ 2
              ≤
            2 * (R ^ 4) ^ 2 *
                ‖F0 s - F0 s₀‖ ^ 2
              +
            4 * (R⁻¹) ^ 2 *
              (‖F5 s‖ ^ 2 +
               ‖F5 s₀‖ ^ 2) :=
            hInterp'
          _ < ε / 2 + ε / 2 := by
            exact add_lt_add hLow hTailSmall
          _ = ε := by
            ring

      exact hSqLt

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp
      hSqTend

  change
    Tendsto
      (fun s : Set.Icc a b =>
        Real.sqrt (‖F4 s - F4 s₀‖ ^ 2))
      (𝓝 s₀)
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

/-! ## Promotion to the whole open restart interval -/

/-- Every interior restart time lies strictly inside a positive compact slab
whose upper endpoint is still below the restart radius. -/
private theorem exists_h3SelectedVelocityFourthRadialLocalCompactSlab
    {R q : ℝ}
    (hq0 : 0 < q)
    (hqR : q < R) :
    ∃ a b : ℝ,
      0 < a ∧
      a ≤ b ∧
      b < R ∧
      a < q ∧
      q < b := by

  let a : ℝ := q / 2
  let b : ℝ := (q + R) / 2

  have ha : 0 < a := by
    dsimp only [a]
    positivity

  have haq : a < q := by
    dsimp only [a]
    linarith

  have hqb : q < b := by
    dsimp only [b]
    linarith

  have hbR : b < R := by
    dsimp only [b]
    linarith

  have hab : a ≤ b := by
    exact (haq.trans hqb).le

  exact ⟨a, b, ha, hab, hbR, haq, hqb⟩

/-- Fourth-radial selected velocity Fourier `L²` is strongly continuous on the
entire strict restart interval. -/
theorem continuous_h3PreterminalSelectedVelocityFourthRadialFourierL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFourthRadialFourierL2
          hNS ht₀ hE hTail q j) := by

  rw [continuous_iff_continuousAt]
  intro q₀

  obtain ⟨a, b, ha, hab, hbR, haq₀, hq₀b⟩ :=
    exists_h3SelectedVelocityFourthRadialLocalCompactSlab
      q₀.property.1 q₀.property.2

  let Fslab :
      Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityFourthRadialFourierL2
        hNS ht₀ hE hTail
        ⟨(s : ℝ),
          lt_of_lt_of_le ha s.property.1,
          lt_of_le_of_lt s.property.2 hbR⟩
        j

  have hFslab :
      Continuous Fslab := by
    dsimp only [Fslab]
    exact
      continuous_h3PreterminalSelectedVelocityFourthRadialFourierL2OnCompact
        hNS ht₀ hE hTail
        ha hab hbR j

  let Y : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hab Fslab

  have hY : Continuous Y := by
    dsimp only [Y]
    exact hFslab.Icc_extend'

  let G :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3FourierComplexL2 :=
    fun q => Y (q : ℝ)

  have hG : Continuous G := by
    dsimp only [G]
    exact hY.comp continuous_subtype_val

  have hNearReal :
      Set.Ioo a b ∈ 𝓝 (q₀ : ℝ) :=
    Ioo_mem_nhds haq₀ hq₀b

  have hNear :
      ∀ᶠ q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E)
        in 𝓝 q₀,
        (q : ℝ) ∈ Set.Ioo a b :=
    continuous_subtype_val.continuousAt
      hNearReal

  have hEq :
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedVelocityFourthRadialFourierL2
          hNS ht₀ hE hTail q j)
        =ᶠ[𝓝 q₀]
      G := by

    filter_upwards [hNear] with q hq

    have hqClosed :
        (q : ℝ) ∈ Set.Icc a b :=
      ⟨hq.1.le, hq.2.le⟩

    let qs : Set.Icc a b :=
      ⟨(q : ℝ), hqClosed⟩

    have hOpenEq :
        (⟨(qs : ℝ),
            lt_of_lt_of_le ha qs.property.1,
            lt_of_le_of_lt qs.property.2 hbR⟩ :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E))
          =
        q := by
      apply Subtype.ext
      rfl

    dsimp only [G, Y]
    rw [Set.IccExtend_of_mem hab Fslab hqClosed]

  exact
    hG.continuousAt.congr_of_eventuallyEq
      hEq

end

end Euclidean
end Bridge
end PrimeTensor
