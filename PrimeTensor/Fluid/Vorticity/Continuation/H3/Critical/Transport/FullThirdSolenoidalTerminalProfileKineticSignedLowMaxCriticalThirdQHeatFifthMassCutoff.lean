import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalFourthQTemporalViscousAlternative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalForcingTwoMoment244
import Mathlib.Tactic

/-!
# Physical third-Q heat: a genuine fifth-moment low band plus explicit sixth tail

The fourth-Q physical PDE balance produces the *actual* third-Q velocity
heat state, q³ u-hat. Its squared L² density is q⁶ |u-hat|², one frequency
square above the actual fifth-velocity dissipation q⁵ |u-hat|².

On the sharp band sqrt(q) < rho, the missing derivative is paid by rho²:

    ||P_rho (q³ u-hat)||² <= rho² ∫ q⁵ |u-hat|².

This theorem is unconditional on each strict physical H³ slice. The
complementary sixth-order heat mass is retained EXACTLY rather than
being silently estimated by the fifth-order dissipation. At the existing
critical dyadic net-growth witness, this supplies a physically native
low-fifth/high-sixth/temporal alternative for all postselected cutoffs.

No endpoint-uniform sixth moment, eighth velocity Fourier moment, or
continuation theorem is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeCriticalThirdQFifth244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalThirdQFifth244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- One additional square-gradient power is paid by the *radius squared*
inside a sharp Fourier ball. This is the exact fifth-to-sixth moment loss. -/
theorem thirdFullKinetic_fifthSixthLowBand_density_le244
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ξ : H3FourierPoint3)
    (hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ)
    (z : ℂ) :
    h3FourierGradientSquare ξ ^ 6 * ‖z‖ ^ 2 ≤
      ρ ^ 2 * (h3FourierGradientSquare ξ ^ 5 * ‖z‖ ^ 2) := by
  have hRadial : h3FourierGradientMagnitude ξ ≤ ρ := by
    exact (show h3FourierGradientMagnitude ξ < ρ from hξ).le
  have hqBound : h3FourierGradientSquare ξ ≤ ρ ^ 2 := by
    have hSquare : h3FourierGradientSquare ξ =
        h3FourierGradientMagnitude ξ ^ 2 := by
      dsimp only [h3FourierGradientSquare, h3FourierGradientMagnitude]
      ring
    rw [hSquare]
    have hMag : 0 ≤ h3FourierGradientMagnitude ξ := by
      unfold h3FourierGradientMagnitude
      positivity
    exact pow_le_pow_left₀ hMag hRadial 2
  have hFactor : 0 ≤ h3FourierGradientSquare ξ ^ 5 * ‖z‖ ^ 2 := by
    exact mul_nonneg
      (pow_nonneg (h3FourierGradientSquare_nonneg ξ) 5)
      (sq_nonneg _)
  calc
    h3FourierGradientSquare ξ ^ 6 * ‖z‖ ^ 2 =
        h3FourierGradientSquare ξ *
          (h3FourierGradientSquare ξ ^ 5 * ‖z‖ ^ 2) := by ring
    _ ≤ ρ ^ 2 * (h3FourierGradientSquare ξ ^ 5 * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hqBound hFactor

/-- On the genuine physical strict-time velocity state, the *low-pass*
third-Q heat mass is bounded by the actual fifth-order velocity moment
of that coordinate. No sixth-order norm is assumed beyond the already
constructed physical third-Q Hilbert state at that strict time. -/
theorem thirdFullPhysical_thirdQHeatLowSquare_le_fifthCoordinate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ‖h3CriticalFourierSharpLowCutoffCLM ρ
      (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j t)‖ ^ 2 ≤
      ρ ^ 2 * (∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 5 *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let V3 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j t
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  let g : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 6 *
      ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
  let f : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 5 *
      ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
  have hV3AE :
      (V3 : H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
            h3SpectralScalarRawFourierL2 (U j) ξ) := by
    dsimp only [V3]
    rw [h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
      hH3 hClass ht j]
    simpa only [U, htAbs] using
      (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At_ae
        hH3 hClass ht j)
  have hGInt : Integrable g (volume : Measure H3FourierPoint3) := by
    have hLpInt : Integrable
        (fun ξ : H3FourierPoint3 => ‖(V3 : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
      (MeasureTheory.Lp.memLp V3).norm.integrable_sq
    refine hLpInt.congr ?_
    filter_upwards [hV3AE] with ξ hξ
    rw [hξ]
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (h3FourierGradientSquare_nonneg ξ) 3), mul_pow]
    ring
  have hFInt : Integrable f (volume : Measure H3FourierPoint3) := by
    change Integrable (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3)
    simpa only [U, htAbs] using
      (integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
        hH3 hClass ht j)
  have hLowSquare :
      ‖h3CriticalFourierSharpLowCutoffCLM ρ V3‖ ^ 2 =
        ∫ ξ : H3FourierPoint3, S.indicator g ξ ∂volume := by
    change ‖h3CriticalFourierSharpLowCutoffApply ρ V3‖ ^ 2 = _
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [h3Critical_fourierSharpLowCutoffApply_ae ρ V3, hV3AE]
      with ξ hCut hVel
    rw [hCut]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, hVel]
      dsimp only [g]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (h3FourierGradientSquare_nonneg ξ) 3), mul_pow]
      ring
    · change ‖(S.indicator (V3 : H3FourierPoint3 → ℂ)) ξ‖ ^ 2 =
          (S.indicator g) ξ
      simp only [Set.indicator_of_notMem hξ, norm_zero] <;> norm_num
  have hPointwise : ∀ ξ : H3FourierPoint3,
      S.indicator g ξ ≤ ρ ^ 2 * f ξ := by
    intro ξ
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      exact thirdFullKinetic_fifthSixthLowBand_density_le244
        ρ hρ ξ hξ (h3SpectralScalarRawFourierL2 (U j) ξ)
    · rw [Set.indicator_of_notMem hξ]
      dsimp only [f]
      exact mul_nonneg (sq_nonneg ρ)
        (mul_nonneg
          (pow_nonneg (h3FourierGradientSquare_nonneg ξ) 5)
          (sq_nonneg _))
  have hIndicatorInt : Integrable (S.indicator g)
      (volume : Measure H3FourierPoint3) :=
    hGInt.indicator (measurableSet_h3TerminalRadialFrequencyBelow ρ)
  change ‖h3CriticalFourierSharpLowCutoffCLM ρ V3‖ ^ 2 ≤
      ρ ^ 2 * (∫ ξ : H3FourierPoint3, f ξ ∂volume)
  calc
    _ = ∫ ξ : H3FourierPoint3, S.indicator g ξ ∂volume := hLowSquare
    _ ≤ ∫ ξ : H3FourierPoint3, ρ ^ 2 * f ξ ∂volume :=
      integral_mono hIndicatorInt (hFInt.const_mul _) hPointwise
    _ = ρ ^ 2 * (∫ ξ : H3FourierPoint3, f ξ ∂volume) := by
      rw [integral_const_mul]

/-- The actual entire three-coordinate low third-Q heat mass costs at most
rho squared times the exact physical fifth-order velocity dissipation. -/
theorem thirdFullPhysical_thirdQHeatLowSquare_le_fifthMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∑ j : Fin 3,
      ‖h3CriticalFourierSharpLowCutoffCLM ρ
        (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t)‖ ^ 2) ≤
      ρ ^ 2 * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let f (j : Fin 3) : ℝ :=
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume
  have hEach (j : Fin 3) :
      ‖h3CriticalFourierSharpLowCutoffCLM ρ
        (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t)‖ ^ 2 ≤ ρ ^ 2 * f j := by
    simpa only [f, U, htAbs] using
      (thirdFullPhysical_thirdQHeatLowSquare_le_fifthCoordinate244
        hH3 hClass ht ρ hρ j)
  have hFifth :
      h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht =
        ∑ j : Fin 3, f j := by
    unfold h3PathTopFourierGlobalFifthMass244
    rfl
  calc
    (∑ j : Fin 3,
      ‖h3CriticalFourierSharpLowCutoffCLM ρ
        (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t)‖ ^ 2) ≤
        ∑ j : Fin 3, ρ ^ 2 * f j := by
          apply Finset.sum_le_sum
          intro j _
          exact hEach j
    _ = ρ ^ 2 * (∑ j : Fin 3, f j) := by rw [Finset.mul_sum]
    _ = ρ ^ 2 * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht := by
      rw [hFifth]

/-- The unabsorbed highpass is EXACTLY the sixth velocity Fourier density
outside the chosen cutoff; it is not claimed to be small or time-integrable. -/
noncomputable def thirdFullPhysicalCriticalThirdQHeatHighpass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ρ : ℝ) (j : Fin 3) (t : ℝ) : H3FourierComplexL2 :=
  h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j t -
    h3CriticalFourierSharpLowCutoffCLM ρ
      (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j t)

/-- Exact sharp Fourier splitting of the actual third-Q physical heat state:
low band paid by the genuine fifth-order velocity dissipation, full high
sixth-order complement retained without any additional bound. -/
theorem thirdFullPhysical_thirdQHeatSquare_le_fifthPlusHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∑ j : Fin 3,
      ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j t‖ ^ 2) ≤
      ρ ^ 2 * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
            hH3 hClass ρ j t‖ ^ 2) := by
  let V (j : Fin 3) : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j t
  let P := h3CriticalFourierSharpLowCutoffCLM ρ
  have hExact : (∑ j : Fin 3, ‖V j‖ ^ 2) =
      (∑ j : Fin 3, ‖P (V j)‖ ^ 2) +
        (∑ j : Fin 3, ‖V j - P (V j)‖ ^ 2) := by
    calc
      _ = ∑ j : Fin 3,
          (‖P (V j)‖ ^ 2 + ‖V j - P (V j)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        exact thirdFullKinetic_sharpFourierLowHigh_square_identity244 ρ (V j)
      _ = (∑ j : Fin 3, ‖P (V j)‖ ^ 2) +
          (∑ j : Fin 3, ‖V j - P (V j)‖ ^ 2) :=
        Finset.sum_add_distrib
  have hLow : (∑ j : Fin 3, ‖P (V j)‖ ^ 2) ≤
      ρ ^ 2 * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht :=
    thirdFullPhysical_thirdQHeatLowSquare_le_fifthMass244
      hH3 hClass ht ρ hρ
  change (∑ j : Fin 3, ‖V j‖ ^ 2) ≤
    ρ ^ 2 * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
      (∑ j : Fin 3, ‖V j - P (V j)‖ ^ 2)
  rw [hExact]
  exact add_le_add_left hLow _

/-- One actual dyadic net-growth witness and every postselected positive
frequency radius: the third-Q heat term is now split into a piece funded
by the genuine fifth velocity moment, plus the explicit high sixth-order
velocity Fourier tail and the genuine fourth-radial temporal derivative.
The fifth expenditure is expressed as its canonical normalized path times
positive D3, so the theorem's statement has NO proof-dependent time input. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_fifthTemporalHighSixth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      K < h3PathPhysicalTopSignedLogRate244 hClass r ∧
      ∀ ρ : ℝ, 0 < ρ →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b)) +
          2 * (ρ ^ 2)⁻¹ * (
            (∑ j : Fin 3,
              ‖deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j) r‖ ^ 2) +
            ρ ^ 2 * (h3PathPhysicalTopFifthActionRate244 hH3 hClass r *
              h3TerminalPhysicalTopDissipation3Path hClass r) +
            (∑ j : Fin 3,
              ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
                hH3 hClass ρ j r‖ ^ 2)) := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_fourthQTemporalThirdQBudget244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hs.1 hr.1), lt_trans hr.2 ht.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD r ⟨hr.1.le, hr.2.le⟩
  have hFifth :
      h3PathTopFourierGlobalFifthMass244 hH3 hClass r hrClass =
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r *
          h3TerminalPhysicalTopDissipation3Path hClass r := by
    unfold h3PathPhysicalTopFifthActionRate244
    simp only [dif_pos hrClass]
    exact (div_mul_cancel₀ _ hDr.ne').symm
  intro ρ hρ
  let A : ℝ :=
    (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
      h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6 *
    (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
      ρ (velocityH3Energy0At u b))
  let F5 : ℝ := h3PathTopFourierGlobalFifthMass244 hH3 hClass r hrClass
  let D4 : ℝ := ∑ j : Fin 3,
    ‖deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j) r‖ ^ 2
  let Q3 : ℝ := ∑ j : Fin 3,
    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j r‖ ^ 2
  let H6 : ℝ := ∑ j : Fin 3,
    ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
      hH3 hClass ρ j r‖ ^ 2
  have hInput : A < C + 2 * (ρ ^ 2)⁻¹ * (D4 + Q3) := by
    simpa only [A, C, D4, Q3] using hAll ρ hρ
  have hLowHigh : Q3 ≤ ρ ^ 2 * F5 + H6 := by
    simpa only [Q3, F5, H6] using
      (thirdFullPhysical_thirdQHeatSquare_le_fifthPlusHigh244
        hH3 hClass hrClass ρ hρ.le)
  have hCoeff : 0 ≤ 2 * (ρ ^ 2)⁻¹ := by positivity
  have hResult : A < C + 2 * (ρ ^ 2)⁻¹ *
      (D4 + ρ ^ 2 * F5 + H6) := by
    calc
      A < C + 2 * (ρ ^ 2)⁻¹ * (D4 + Q3) := hInput
      _ ≤ C + 2 * (ρ ^ 2)⁻¹ * (D4 + (ρ ^ 2 * F5 + H6)) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left
            (add_le_add_right hLowHigh D4) hCoeff) C
      _ = C + 2 * (ρ ^ 2)⁻¹ * (D4 + ρ ^ 2 * F5 + H6) := by ring
  simpa only [A, C, D4, F5, H6, hFifth] using hResult

end
end PrimeTensor.FirstMonomialTriad
