import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicPhysicalSourcePeak
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticLowBandSourceLipschitz
import Mathlib.Tactic

/-!
# H3-native dyadic source peak: kinetic low band or actual Leray highpass

The prior order-four velocity-product convolution gate required order-eight
raw Fourier moments of the velocity.  This module removes that regularity
hypothesis from the dyadic physical source-peak transfer itself.

For the actual physical order-three Leray forcing F3_j(t) in Fourier L2,
cut at a real radial frequency rho >= 0, with the exact measurable indicator
Q_rho.  The genuine kinetic-energy estimate bounds the low component:

  ||Q_rho F3_j(t)||^2 <= rho^6 * measure(S_rho) * (18*rho*E0(b))^2.

All high components are retained exactly as F3_j - Q_rho F3_j.
Thus a sufficiently large physical source peak must be funded by either
this explicit, fixed-frequency kinetic ceiling or by the actual highpass
third-radial Leray forcing.  The new theorem does not assume order-eight
moments, a full-source ceiling, highpass smallness, or terminal compactness.

This does not yet bound the highpass source from Navier--Stokes dynamics.
That is the remaining mathematical obstruction.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

-- The canonical product-volume structure for three-dimensional Fourier space.
noncomputable local instance axisFintypeCriticalDyadicKineticHighpass244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalDyadicKineticHighpass244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The explicit kinetic-only bound for one order-three Leray forcing
coordinate below Fourier-gradient radius rho. -/
noncomputable def thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    (ρ E : ℝ) : ℝ :=
  ρ ^ 6 *
    (volume : Measure H3FourierPoint3).real
      (h3TerminalRadialFrequencyBelow ρ) *
    (18 * (ρ * E)) ^ 2

/-- The highpass is the genuine difference of the canonical third-radial
Fourier forcing state and its bounded sharp-cutoff projection. -/
noncomputable def thirdFullPhysicalCriticalThirdForcingHighpass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ρ : ℝ) (j : Fin 3) (t : ℝ) : H3FourierComplexL2 :=
  h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j t -
    h3CriticalFourierSharpLowCutoffCLM ρ
      (h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j t)

/-- The highpass remainder is exactly the complementary measurable
Fourier-region square mass of the actual third-radial Leray forcing. -/
theorem thirdFullPhysical_criticalThirdForcingHighpass_norm_sq_eq_integral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ρ : ℝ) (j : Fin 3) (t : ℝ) :
    ‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j t‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        ‖(h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume := by
  unfold thirdFullPhysicalCriticalThirdForcingHighpass244
  exact h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ _

/-- Kinetic-energy-only finite-band estimate for the ACTUAL physical
order-three Fourier Leray source.  No eighth velocity moments are used.
The factor rho^6 accounts for precisely three radial derivatives in L2. -/
theorem thirdFullPhysical_criticalThirdForcingLowSquare_le_kinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (j : Fin 3) :
    ‖h3CriticalFourierSharpLowCutoffCLM ρ
      (h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j t)‖ ^ 2 ≤
      thirdFullPhysicalCriticalThirdForcingKineticLowBudget244 ρ
        (velocityH3Energy0At u b) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let F : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j t
  let G : H3FourierComplexL2 :=
    h3CriticalLowRadialLerayFourierL2 ρ U j
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 htClass.1, htClass.2⟩
  have hFRep :
      (F : H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence U U j ξ) := by
    dsimp only [F]
    rw [h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
      hH3 hClass htClass j]
    have hRep :=
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At_ae
        hH3 hClass htClass j
    simpa only [U,
      h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
      using hRep
  have hTwoPi : (1 : ℝ) ≤ 2 * Real.pi := by
    have hp := Real.pi_gt_three
    linarith only [hp]
  have hCutoffNorm :
      ‖h3CriticalFourierSharpLowCutoffCLM ρ F‖ ≤ ρ ^ 3 * ‖G‖ := by
    change ‖h3CriticalFourierSharpLowCutoffApply ρ F‖ ≤ ρ ^ 3 * ‖G‖
    apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [
      h3Critical_fourierSharpLowCutoffApply_ae ρ F,
      h3Critical_lowRadialLerayFourierL2_ae ρ U j,
      hFRep
    ] with ξ hLow hRaw hF
    rw [hLow, hRaw]
    by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, hF,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)]
      have hRadial : (2 * Real.pi) * ‖ξ‖ < ρ := by
        change h3FourierGradientMagnitude ξ < ρ at hξ
        exact hξ
      have hXiBound : ‖ξ‖ ≤ ρ := by
        calc
          ‖ξ‖ = 1 * ‖ξ‖ := by ring
          _ ≤ (2 * Real.pi) * ‖ξ‖ :=
            mul_le_mul_of_nonneg_right hTwoPi (norm_nonneg ξ)
          _ ≤ ρ := hRadial.le
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg ξ) hXiBound 3)
        (norm_nonneg _)
    · simp only [Set.indicator_of_notMem hξ, norm_zero, mul_zero, le_refl]
  have hKineticSq :
      ‖G‖ ^ 2 ≤
      (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ρ) *
      (18 * (ρ * velocityH3Energy0At u b)) ^ 2 := by
    have hMass :=
      h3Critical_actual_lowRadial_lerayFourierSquareMass_le_kineticAnchor
        hH3 hClass b hb ρ hρ t ht j
    rw [h3Critical_lowRadialLerayFourierL2_norm_sq ρ U j]
    simpa only [U] using hMass
  have hCutoffSq :
      ‖h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 ≤
        (ρ ^ 3 * ‖G‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hCutoffNorm 2
  change ‖h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 ≤ _
  unfold thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
  calc
    ‖h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 ≤
        (ρ ^ 3 * ‖G‖) ^ 2 := hCutoffSq
    _ = ρ ^ 6 * ‖G‖ ^ 2 := by ring
    _ ≤ ρ ^ 6 *
        ((volume : Measure H3FourierPoint3).real
          (h3TerminalRadialFrequencyBelow ρ) *
        (18 * (ρ * velocityH3Energy0At u b)) ^ 2) :=
      mul_le_mul_of_nonneg_left hKineticSq (pow_nonneg hρ 6)
    _ = ρ ^ 6 *
        (volume : Measure H3FourierPoint3).real
          (h3TerminalRadialFrequencyBelow ρ) *
        (18 * (ρ * velocityH3Energy0At u b)) ^ 2 := by ring

/-- The exact low/high Fourier Pythagoras-free inequality, valid even for
an arbitrary projection.  It loses only a factor two; no cutoff orthogonality
is assumed. -/
theorem thirdFullKinetic_scalar_threeFourierLowHighSquare244
    (F : Fin 3 → H3FourierComplexL2)
    (P : H3FourierComplexL2 →L[ℂ] H3FourierComplexL2) :
    (∑ j : Fin 3, ‖F j‖ ^ 2) ≤
      2 * ((∑ j : Fin 3, ‖P (F j)‖ ^ 2) +
        (∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2)) := by
  have hEach (j : Fin 3) :
      ‖F j‖ ^ 2 ≤
        2 * (‖P (F j)‖ ^ 2 + ‖F j - P (F j)‖ ^ 2) := by
    have hTri : ‖F j‖ ≤ ‖P (F j)‖ + ‖F j - P (F j)‖ := by
      calc
        ‖F j‖ = ‖P (F j) + (F j - P (F j))‖ := by
          congr 1
          abel
        _ ≤ ‖P (F j)‖ + ‖F j - P (F j)‖ := norm_add_le _ _
    have hSq : ‖F j‖ ^ 2 ≤
        (‖P (F j)‖ + ‖F j - P (F j)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hTri 2
    nlinarith only [hSq,
      sq_nonneg (‖P (F j)‖ - ‖F j - P (F j)‖)]
  calc
    (∑ j : Fin 3, ‖F j‖ ^ 2) ≤
        ∑ j : Fin 3,
          2 * (‖P (F j)‖ ^ 2 + ‖F j - P (F j)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact hEach j
    _ = 2 * ((∑ j : Fin 3, ‖P (F j)‖ ^ 2) +
        (∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] <;> ring

/-- The physical cubic forcing mass splits into a *kinetic-only* low-band
budget and the exact highpass third-radial Leray mass.  No order-eight
velocity Fourier moment is present in the hypotheses. -/
theorem thirdFullPhysical_criticalThirdForcingMass_kineticLowHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    (2 * Real.pi) ^ 6 *
      (∑ j : Fin 3,
        (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t‖ : ℝ) ^ 2) ≤
    2 * (2 * Real.pi) ^ 6 *
      (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
        ρ (velocityH3Energy0At u b) +
        ∑ j : Fin 3,
          (‖thirdFullPhysicalCriticalThirdForcingHighpass244
            hH3 hClass ρ j t‖ : ℝ) ^ 2) := by
  let F : Fin 3 → H3FourierComplexL2 := fun j =>
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j t
  let P := h3CriticalFourierSharpLowCutoffCLM ρ
  let L := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  have hLow (j : Fin 3) : ‖P (F j)‖ ^ 2 ≤ L := by
    exact thirdFullPhysical_criticalThirdForcingLowSquare_le_kinetic244
      hH3 hClass b hb ρ hρ t ht j
  have hLowSum : (∑ j : Fin 3, ‖P (F j)‖ ^ 2) ≤ 3 * L := by
    calc
      (∑ j : Fin 3, ‖P (F j)‖ ^ 2) ≤ ∑ _j : Fin 3, L := by
        apply Finset.sum_le_sum
        intro j _
        exact hLow j
      _ = 3 * L := by simp <;> ring
  have hSplit := thirdFullKinetic_scalar_threeFourierLowHighSquare244 F P
  have hSum :
      (∑ j : Fin 3, ‖F j‖ ^ 2) ≤
      2 * (3 * L + ∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2) := by
    calc
      (∑ j : Fin 3, ‖F j‖ ^ 2) ≤
          2 * ((∑ j : Fin 3, ‖P (F j)‖ ^ 2) +
            (∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2)) := hSplit
      _ ≤ 2 * (3 * L + ∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add_left hLowSum _) (by norm_num)
  have hC : 0 ≤ (2 * Real.pi) ^ 6 := by positivity
  have hProduct := mul_le_mul_of_nonneg_left hSum hC
  change (2 * Real.pi) ^ 6 *
    (∑ j : Fin 3, ‖F j‖ ^ 2) ≤
    2 * (2 * Real.pi) ^ 6 *
      (3 * L + ∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2)
  calc
    _ ≤ (2 * Real.pi) ^ 6 *
        (2 * (3 * L +
          ∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2)) := hProduct
    _ = _ := by ring

/-- An actual near-critical dyadic H3 source peak is necessarily funded
by either the kinetic low-frequency budget or by the TRUE high-frequency
order-three Leray forcing.  This theorem assumes neither eighth moments
nor a regularity bound on the highpass remainder. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_kineticLowOrForcingHigh244
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
        8 * Real.log 2 - 3 * K * (t - s))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      (K * h3TerminalPhysicalTopDissipation3Path hClass r <
        12 * (2 * Real.pi) ^ 6 *
          thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
            ρ (velocityH3Energy0At u b) ∨
       K * h3TerminalPhysicalTopDissipation3Path hClass r <
        4 * (2 * Real.pi) ^ 6 *
          ∑ j : Fin 3,
            (‖thirdFullPhysicalCriticalThirdForcingHighpass244
              hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  obtain ⟨r, hr, hPeak⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_thirdRadialLerayPeak244
      hH3 hClass hsClass htClass hst hD hDouble B hB hRate K hNear
  have hrTail : r ∈ Set.Ioo b T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hMass := thirdFullPhysical_criticalThirdForcingMass_kineticLowHigh244
    hH3 hClass b hb ρ hρ r hrTail
  let X : ℝ := K * h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6
  let L : ℝ := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  let H : ℝ := ∑ j : Fin 3,
    (‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ : ℝ) ^ 2
  have hLarge : X < 2 * C * (3 * L + H) := by
    dsimp only [X, C, L, H]
    exact lt_of_lt_of_le hPeak hMass
  have hSplit : X < 12 * C * L ∨ X < 4 * C * H := by
    by_cases hSmallLow : X < 12 * C * L
    · exact Or.inl hSmallLow
    · right
      have hLowLarge : 12 * C * L ≤ X := le_of_not_gt hSmallLow
      nlinarith only [hLarge, hLowLarge]
  refine ⟨r, hr, ?_⟩
  simpa only [X, C, L, H] using hSplit

end
end PrimeTensor.FirstMonomialTriad
