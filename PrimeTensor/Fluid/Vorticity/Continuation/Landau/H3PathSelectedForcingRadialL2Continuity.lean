import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingRadialL2Difference

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingRadialL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/--
The unweighted selected nonlinear forcing is strongly continuous in Fourier
`L²` on all real source times.  Keeping this helper independent of the
terminal-slab parameters prevents the weighted continuity theorem from having
to elaborate the full forcing composition inside a highly dependent context.
-/
theorem continuous_h3SelectedRestartUnheatedForcingFourierL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    Continuous
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceFourierL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s)
          i) := by

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D :
      ℝ →
        H3SpectralFinVectorState × H3SpectralFinVectorState :=
    fun s => (W s, W s)

  let F :
      H3SpectralFinVectorState × H3SpectralFinVectorState →
        H3FourierComplexL2 :=
    fun p =>
      h3RawFinLerayOuterProductDivergenceFourierL2
        p.1 p.2 i

  have hW : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hD : Continuous D := by
    dsimp only [D]
    exact Continuous.prodMk hW hW

  have hF : Continuous F := by
    dsimp only [F]
    exact
      continuous_h3RawFinLerayOuterProductDivergenceFourierL2 i

  have hComp :
      Continuous (F ∘ D) :=
    hF.comp hD

  have hEq :
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceFourierL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s)
          i)
        =
      F ∘ D := by
    funext s
    rfl

  rw [hEq]
  exact hComp

/--
At every finite radial order, the quotient-safe selected forcing state is
strongly continuous on the complete positive terminal half.
-/
theorem continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
    {ν A q : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Continuous
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        m hν U₀ hA hU₀ hq hqR i) := by

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F0 :
      Set.Icc (q / 2) q →
        H3FourierComplexL2 :=
    fun s =>
      h3RawFinLerayOuterProductDivergenceFourierL2
        (W (s : ℝ)) (W (s : ℝ)) i

  let Fm :
      Set.Icc (q / 2) q →
        H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m hν U₀ hA hU₀ hq hqR i

  have hW : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hF0Real :
      Continuous
        (fun s : ℝ =>
          h3RawFinLerayOuterProductDivergenceFourierL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)
            i) :=
    continuous_h3SelectedRestartUnheatedForcingFourierL2
      hν U₀ hA hU₀ i

  have hF0Explicit :
      Continuous
        (fun s : Set.Icc (q / 2) q =>
          h3RawFinLerayOuterProductDivergenceFourierL2
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ (s : ℝ))
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ (s : ℝ))
            i) :=
    hF0Real.comp continuous_subtype_val

  have hF0 : Continuous F0 := by
    simpa only [F0, W] using hF0Explicit

  obtain ⟨B, hB0, hB⟩ :=
    exists_norm_sq_bound_h3SelectedRestartForcingRadialFourierL2OnSlab
      (m + 1) (by omega)
      hν U₀ hA hU₀ hq hqR

  rw [continuous_iff_continuousAt]
  intro s₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hLowNormTend :
      Tendsto
        (fun s : Set.Icc (q / 2) q =>
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
        (fun s : Set.Icc (q / 2) q =>
          ‖F0 s - F0 s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 0) := by
    have hComp := hPow.comp hLowNormTend
    change
      Tendsto
        (fun s : Set.Icc (q / 2) q =>
          ‖F0 s - F0 s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 ((0 : ℝ) ^ 2))
      at hComp
    norm_num at hComp
    exact hComp

  have hSqTend :
      Tendsto
        (fun s : Set.Icc (q / 2) q =>
          ‖Fm s - Fm s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 0) := by

    refine tendsto_order.2 ⟨?_, ?_⟩

    · intro c hc
      exact
        Filter.Eventually.of_forall
          (fun s =>
            lt_of_lt_of_le hc
              (sq_nonneg ‖Fm s - Fm s₀‖))

    · intro ε hε

      let R : ℝ := 1 + (16 * B) / ε

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
        2 * (R ^ m) ^ 2

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
        norm_sq_h3SelectedRestartForcingRadialFourierL2OnSlab_sub_le
          m hR hν U₀ hA hU₀ hq hqR i s s₀

      have hηEq :
          (C + 1) * η = ε / 2 := by
        dsimp only [η]
        field_simp [ne_of_gt hC1] <;> ring

      have hLow :
          C * ‖F0 s - F0 s₀‖ ^ 2 < ε / 2 := by
        have hCLe : C ≤ C + 1 := by
          linarith

        have hSq0 :
            0 ≤ ‖F0 s - F0 s₀‖ ^ 2 :=
          sq_nonneg _

        have hStep1 :
            C * ‖F0 s - F0 s₀‖ ^ 2
              ≤
            (C + 1) * ‖F0 s - F0 s₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hCLe hSq0

        have hStep2 :
            (C + 1) * ‖F0 s - F0 s₀‖ ^ 2
              <
            (C + 1) * η :=
          mul_lt_mul_of_pos_left hsLow hC1

        exact
          lt_of_le_of_lt hStep1
            (hStep2.trans_eq hηEq)

      have hNext :
          ‖h3SelectedRestartForcingRadialFourierL2OnSlab
              (m + 1) hν U₀ hA hU₀ hq hqR i s‖ ^ 2
            +
          ‖h3SelectedRestartForcingRadialFourierL2OnSlab
              (m + 1) hν U₀ hA hU₀ hq hqR i s₀‖ ^ 2
            ≤
          B + B :=
        add_le_add
          (hB i s)
          (hB i s₀)

      have hTail :
          4 * (R⁻¹) ^ 2 *
              (‖h3SelectedRestartForcingRadialFourierL2OnSlab
                    (m + 1) hν U₀ hA hU₀ hq hqR i s‖ ^ 2
                +
               ‖h3SelectedRestartForcingRadialFourierL2OnSlab
                    (m + 1) hν U₀ hA hU₀ hq hqR i s₀‖ ^ 2)
            <
          ε / 2 := by
        calc
          4 * (R⁻¹) ^ 2 *
              (‖h3SelectedRestartForcingRadialFourierL2OnSlab
                    (m + 1) hν U₀ hA hU₀ hq hqR i s‖ ^ 2
                +
               ‖h3SelectedRestartForcingRadialFourierL2OnSlab
                    (m + 1) hν U₀ hA hU₀ hq hqR i s₀‖ ^ 2)
              ≤
            4 * (R⁻¹) ^ 2 * (B + B) :=
            mul_le_mul_of_nonneg_left
              hNext
              (mul_nonneg
                (by norm_num)
                (sq_nonneg _))
          _ = 8 * B * (R⁻¹) ^ 2 := by
            ring
          _ < ε / 2 :=
            hTailBudget

      have hSqLt :
          ‖Fm s - Fm s₀‖ ^ 2 < ε := by
        dsimp only [Fm, F0, W] at hInterp ⊢
        calc
          ‖h3SelectedRestartForcingRadialFourierL2OnSlab
                m hν U₀ hA hU₀ hq hqR i s
              -
            h3SelectedRestartForcingRadialFourierL2OnSlab
                m hν U₀ hA hU₀ hq hqR i s₀‖ ^ 2
              ≤
            2 * (R ^ m) ^ 2 *
                ‖h3RawFinLerayOuterProductDivergenceFourierL2
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ (s : ℝ))
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ (s : ℝ))
                    i
                  -
                  h3RawFinLerayOuterProductDivergenceFourierL2
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ (s₀ : ℝ))
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ (s₀ : ℝ))
                    i‖ ^ 2
              +
            4 * (R⁻¹) ^ 2 *
              (‖h3SelectedRestartForcingRadialFourierL2OnSlab
                    (m + 1) hν U₀ hA hU₀ hq hqR i s‖ ^ 2
                +
               ‖h3SelectedRestartForcingRadialFourierL2OnSlab
                    (m + 1) hν U₀ hA hU₀ hq hqR i s₀‖ ^ 2) :=
            hInterp
          _ < ε / 2 + ε / 2 := by
            exact add_lt_add hLow hTail
          _ = ε := by
            ring

      exact hSqLt

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp hSqTend

  change
    Tendsto
      (fun s : Set.Icc (q / 2) q =>
        Real.sqrt (‖Fm s - Fm s₀‖ ^ 2))
      (𝓝 s₀)
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

/-- Fourth-order selected forcing radial Fourier `L²` continuity. -/
theorem continuous_h3SelectedRestartForcingFourthRadialFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Continuous
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        4 hν U₀ hA hU₀ hq hqR i) :=
  continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
    4 hν U₀ hA hU₀ hq hqR i

/-- Fifth-order selected forcing radial Fourier `L²` continuity. -/
theorem continuous_h3SelectedRestartForcingFifthRadialFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Continuous
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        5 hν U₀ hA hU₀ hq hqR i) :=
  continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
    5 hν U₀ hA hU₀ hq hqR i

end

end Euclidean
end Bridge
end PrimeTensor
