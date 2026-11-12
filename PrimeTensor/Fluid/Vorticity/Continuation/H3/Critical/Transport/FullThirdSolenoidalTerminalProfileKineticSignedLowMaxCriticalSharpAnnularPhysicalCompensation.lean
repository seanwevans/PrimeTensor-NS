import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterTailLedger
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalSharpPhysicalKineticCompensation
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-!
# Physical sharp-highpass mismatch from Plancherel; annulus and outer-tail cost

The accepted three-axis Fourier annulus ledger is now identified with the
NATIVE PHYSICAL real-L² sharp-highpass mismatch. Both the velocity and the
projected momentum source are the actual strict-time Navier--Stokes fields.

For a kinetic anchor b<t<T, put Uhi=(1-P_rho)U, Rhi=(1-P_rho)R,
rate=(rho²+sigma²)/2, and K=sqrt(E0(b))*3*Ckin(rho,E0(b)). Then

  rate*||Uhi||² - K <= ||Uhi|| * ||Rhi-rate*Uhi||.

If the left side is nonnegative, its square must be funded by the exact
annular Young gap, the width penalty, and the OUTER TAIL:

  rho⁶*(rate*||Uhi||²-K)² <= ||Uhi||² * [2*Gap_ann + Width_ann + rho⁶*Tail].

There is no terminal-uniform assertion. In particular no estimate on the
moving outer tail or on the annulus width is inserted by assumption.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeSharpAnnularPhysical244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSharpAnnularPhysical244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Sharp highpass of a constant-rate complex Fourier mismatch: its squared
norm is exactly the L² residual over the complementary radial ball. -/
theorem thirdFullKinetic_sharpFourierRateMismatch_normSquare244
    (rho rate : ℝ) (R Z : H3FourierComplexL2) :
    ‖(R - (rate : ℂ) • Z) -
      h3CriticalFourierSharpLowCutoffCLM rho (R - (rate : ℂ) • Z)‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow rho)ᶜ,
        ‖(R : H3FourierPoint3 → ℂ) ξ -
          (rate : ℂ) * (Z : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume := by
  let E : H3FourierComplexL2 := R - (rate : ℂ) • Z
  have hAE : (E : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ => (R : H3FourierPoint3 → ℂ) ξ -
        (rate : ℂ) * (Z : H3FourierPoint3 → ℂ) ξ) := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub R ((rate : ℂ) • Z),
      MeasureTheory.Lp.coeFn_smul (rate : ℂ) Z] with ξ hSub hSmul
    rw [hSub]
    simp only [Pi.sub_apply]
    rw [hSmul]
    simp only [Pi.smul_apply, smul_eq_mul]
  change ‖E - h3CriticalFourierSharpLowCutoffCLM rho E‖ ^ 2 = _
  calc
    ‖E - h3CriticalFourierSharpLowCutoffCLM rho E‖ ^ 2 =
        ∫ ξ in (h3TerminalRadialFrequencyBelow rho)ᶜ,
          ‖(E : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume :=
      h3Critical_fourierSharpHighpass_norm_sq_eq_integral rho E
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (s := (h3TerminalRadialFrequencyBelow rho)ᶜ) hAE] with ξ hξ
      rw [hξ]

/-- A scalar physical rate mismatch and its actual Fourier transform have
exactly the same SHARP HIGH-PASS mass. Real scalar multiplication is
transported through the real Plancherel isometry before applying the
complex-linear Fourier projector. -/
theorem thirdFullKinetic_sharpPhysicalRateMismatch_normSquare244
    (rho rate : ℝ) (f g : H3ScalarL2) :
    ‖(f - h3CriticalPhysicalSharpLowCutoffApply rho f) -
      rate • (g - h3CriticalPhysicalSharpLowCutoffApply rho g)‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow rho)ᶜ,
        ‖(h3ScalarFourierL2 f : H3FourierPoint3 → ℂ) ξ -
          (rate : ℂ) *
            (h3ScalarFourierL2 g : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume := by
  let X : H3ScalarL2 :=
    (f - h3CriticalPhysicalSharpLowCutoffApply rho f) -
      rate • (g - h3CriticalPhysicalSharpLowCutoffApply rho g)
  let F : H3FourierComplexL2 :=
    h3ScalarFourierL2 f - (rate : ℂ) • h3ScalarFourierL2 g
  have hFourier : h3ScalarFourierL2 X =
      F - h3CriticalFourierSharpLowCutoffCLM rho F := by
    dsimp only [X, F]
    rw [h3ScalarFourierL2_sub, h3ScalarFourierL2_smul_real,
      h3Critical_scalarFourier_physicalHighpass_eq,
      h3Critical_scalarFourier_physicalHighpass_eq]
    rw [map_sub, map_smul]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) rate
      (h3ScalarFourierL2 g -
        h3CriticalFourierSharpLowCutoffCLM rho (h3ScalarFourierL2 g))]
    simp only [smul_sub]
    abel
  change ‖X‖ ^ 2 = _
  calc
    ‖X‖ ^ 2 = ‖h3ScalarFourierL2 X‖ ^ 2 := by
      rw [norm_h3ScalarFourierL2]
    _ = ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 := by
      rw [hFourier]
    _ = _ := thirdFullKinetic_sharpFourierRateMismatch_normSquare244
      rho rate (h3ScalarFourierL2 f) (h3ScalarFourierL2 g)

/-- The physical three-component highpass mismatch is IDENTICAL to the
three-axis Fourier error appearing in the accepted annular ledger. In
particular the physical source, not an invented Fourier state, is used. -/
theorem thirdFullPhysical_sharpActualRateMismatch_normSquare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rho rate : ℝ) :
    let U : H3PhysicalRealFinVectorL2Hilbert :=
      h3AuditInitialOldPhysicalHilbertTotal hH3 t
    let R : H3PhysicalRealFinVectorL2Hilbert :=
      h3PathActualProjectedMomentumSource244 hH3 t
    ‖(R - thirdFullPhysicalSharpLowCutoffHilbert244 rho R) -
      rate • (U - thirdFullPhysicalSharpLowCutoffHilbert244 rho U)‖ ^ 2 =
      ∑ j : Fin 3,
        ∫ ξ in (h3TerminalRadialFrequencyBelow rho)ᶜ,
          ‖(h3CriticalActualProjectedFourierSource hH3 j t :
            H3FourierPoint3 → ℂ) ξ -
            (rate : ℂ) *
              h3SpectralScalarRawFourierL2
                ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2
          ∂volume := by
  dsimp only
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    (R - thirdFullPhysicalSharpLowCutoffHilbert244 rho R) -
      rate • (U - thirdFullPhysicalSharpLowCutoffHilbert244 rho U)
  have hVelocity (j : Fin 3) :
      h3ScalarFourierL2 (U.ofLp j) =
        h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) := by
    symm
    change h3SpectralScalarRawFourierL2
      (h3AuditActualSpectralVelocityTotal hH3 t j) = _
    rw [h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2 hH3 j t ht]
    simp only [U, h3AuditInitialOldPhysicalHilbertTotal, PiLp.toLp_apply]
  have hSource (j : Fin 3) :
      h3ScalarFourierL2 (R.ofLp j) =
        h3CriticalActualProjectedFourierSource hH3 j t := rfl
  change ‖V‖ ^ 2 = _
  calc
    ‖V‖ ^ 2 = ∑ j : Fin 3, ‖V.ofLp j‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => H3ScalarL2) V
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hScalar :=
        thirdFullKinetic_sharpPhysicalRateMismatch_normSquare244
          rho rate (R.ofLp j) (U.ofLp j)
      rw [hSource j, hVelocity j] at hScalar
      change ‖(R.ofLp j -
          h3CriticalPhysicalSharpLowCutoffApply rho (R.ofLp j)) -
          rate • (U.ofLp j -
            h3CriticalPhysicalSharpLowCutoffApply rho (U.ofLp j))‖ ^ 2 = _
      exact hScalar

/-- The full physical annular ledger: the Fourier three-axis mismatch on
the left is replaced by the actual real-Hilbert sharp highpass source error.
The outer tail remains explicit as part of the cost functional. -/
noncomputable def thirdFullPhysicalActualAnnularLedgerCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho sigma : ℝ) : ℝ :=
  let ann : Set H3FourierPoint3 :=
    ((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
      h3TerminalRadialFrequencyBelow sigma
  let rate : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  2 * (∑ j : Fin 3, ∫ ξ in ann,
    h3FourierGradientSquare ξ ^ 3 *
      ‖h3RawFinLerayOuterProductDivergence U U j ξ +
        2 * ((h3FourierGradientSquare ξ : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) +
  (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
    (∑ j : Fin 3, ∫ ξ in ann,
      ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) +
  (rho ^ 2) ^ 3 *
    (∑ j : Fin 3, ∫ ξ in (h3TerminalRadialFrequencyBelow sigma)ᶜ,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
        H3FourierPoint3 → ℂ) ξ -
        (rate : ℂ) * h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume)

/-- Plancherel turns the accepted annulus+outer-tail Fourier ledger into
an inequality for the ACTUAL physical highpass momentum mismatch. -/
theorem thirdFullPhysical_actualHighpassMismatch_le_annularLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) :
    let rate : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let U : H3PhysicalRealFinVectorL2Hilbert :=
      h3AuditInitialOldPhysicalHilbertTotal hH3 t
    let R : H3PhysicalRealFinVectorL2Hilbert :=
      h3PathActualProjectedMomentumSource244 hH3 t
    (rho ^ 2) ^ 3 *
      ‖(R - thirdFullPhysicalSharpLowCutoffHilbert244 rho R) -
        rate • (U - thirdFullPhysicalSharpLowCutoffHilbert244 rho U)‖ ^ 2 ≤
      thirdFullPhysicalActualAnnularLedgerCost244 hH3 t rho sigma := by
  dsimp only
  have hFourier := thirdFullPhysical_sharpActualRateMismatch_normSquare244
    hH3 t ht rho ((rho ^ 2 + sigma ^ 2) / 2)
  have hLedger :=
    thirdFullPhysical_actualThreeAxisHighpass_YoungGap_outerTailLedger244
      hH3 t ht rho sigma hRho hOrder
  dsimp only at hFourier hLedger
  rw [hFourier]
  simpa only [thirdFullPhysicalActualAnnularLedgerCost244] using hLedger

/-- QUANTITATIVE physical rigidity on a moving finite annulus. If its
anti-heat carrier exceeds the genuine kinetic low-band budget, the positive
excess must be paid by the accepted annular Young gap, width error AND outer
frequency tail. No division by highpass mass is used, even when it vanishes.

The rate and the budget are fully specified actual physical quantities.
-/
theorem thirdFullPhysical_kineticExcess_forces_annularYoungGapTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 rho
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2) :
    (rho ^ 2) ^ 3 *
      (((rho ^ 2 + sigma ^ 2) / 2) *
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 rho
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2 -
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b))) ^ 2 ≤
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2 *
        thirdFullPhysicalActualAnnularLedgerCost244 hH3 t rho sigma := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let Ulo := thirdFullPhysicalSharpLowCutoffHilbert244 rho U
  let Rlo := thirdFullPhysicalSharpLowCutoffHilbert244 rho R
  let Uhi := U - Ulo
  let Rhi := R - Rlo
  let Ehi := Rhi - ((rho ^ 2 + sigma ^ 2) / 2) • Uhi
  let rate : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let K : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  have hU : U = Ulo + Uhi := by
    dsimp only [Uhi]
    abel
  have hR : R = Rlo + Rhi := by
    dsimp only [Rhi]
    abel
  have hPair : inner ℝ (Ulo + Uhi) (Rlo + Rhi) =
      -velocityH3Dissipation0At u t := by
    rw [← hU, ← hR]
    exact h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244
      hH3 t htAbs
  have hCrossLo : inner ℝ Ulo Rhi = 0 :=
    thirdFullPhysical_sharpVectorLowHigh_crossInner_zero244 rho U R
  have hCrossHi : inner ℝ Uhi Rlo = 0 :=
    thirdFullPhysical_sharpVectorHighLow_crossInner_zero244 rho U R
  have hBase := thirdFullKinetic_twoChannel_antiHeatCompensation244
    Ulo Uhi Rlo Rhi (velocityH3Dissipation0At u t) rate
    hPair hCrossLo hCrossHi
  have hUlo : ‖Ulo‖ ≤ Real.sqrt (velocityH3Energy0At u b) :=
    thirdFullPhysical_sharpActualVelocity_kineticAnchor244
      hH3 hClass b hb rho t ht
  have hRlo : ‖Rlo‖ ≤
      3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b) :=
    thirdFullPhysical_sharpActualSource_kineticAnchor244
      hH3 hClass b hb rho hRho t ht
  have hLow : ‖Ulo‖ * ‖Rlo‖ ≤ K := by
    calc
      ‖Ulo‖ * ‖Rlo‖ ≤
          Real.sqrt (velocityH3Energy0At u b) * ‖Rlo‖ :=
        mul_le_mul_of_nonneg_right hUlo (norm_nonneg _)
      _ ≤ K :=
        mul_le_mul_of_nonneg_left hRlo (Real.sqrt_nonneg _)
  have hD : 0 ≤ velocityH3Dissipation0At u t :=
    velocityH3Dissipation0At_nonneg u t
  have hGap : rate * ‖Uhi‖ ^ 2 - K ≤ ‖Uhi‖ * ‖Ehi‖ := by
    dsimp only [Ehi]
    linarith only [hBase, hD, hLow]
  have hLedger : (rho ^ 2) ^ 3 * ‖Ehi‖ ^ 2 ≤
      thirdFullPhysicalActualAnnularLedgerCost244 hH3 t rho sigma := by
    change (rho ^ 2) ^ 3 *
      ‖(R - thirdFullPhysicalSharpLowCutoffHilbert244 rho R) -
        rate • (U - thirdFullPhysicalSharpLowCutoffHilbert244 rho U)‖ ^ 2 ≤ _
    exact thirdFullPhysical_actualHighpassMismatch_le_annularLedger244
      hH3 t htAbs rho sigma hRho hOrder
  have hExcess' : 0 ≤ rate * ‖Uhi‖ ^ 2 - K := by
    apply sub_nonneg.mpr
    exact hExcess
  have hSq : (rate * ‖Uhi‖ ^ 2 - K) ^ 2 ≤
      (‖Uhi‖ * ‖Ehi‖) ^ 2 :=
    (sq_le_sq₀ hExcess'
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hGap
  have hWeight : 0 ≤ (rho ^ 2) ^ 3 :=
    pow_nonneg (sq_nonneg rho) 3
  change (rho ^ 2) ^ 3 * (rate * ‖Uhi‖ ^ 2 - K) ^ 2 ≤
    ‖Uhi‖ ^ 2 * thirdFullPhysicalActualAnnularLedgerCost244
      hH3 t rho sigma
  calc
    (rho ^ 2) ^ 3 * (rate * ‖Uhi‖ ^ 2 - K) ^ 2 ≤
        (rho ^ 2) ^ 3 * (‖Uhi‖ * ‖Ehi‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hSq hWeight
    _ = ‖Uhi‖ ^ 2 * ((rho ^ 2) ^ 3 * ‖Ehi‖ ^ 2) := by ring
    _ ≤ ‖Uhi‖ ^ 2 *
        thirdFullPhysicalActualAnnularLedgerCost244 hH3 t rho sigma :=
      mul_le_mul_of_nonneg_left hLedger (sq_nonneg _)

end
end PrimeTensor.FirstMonomialTriad
