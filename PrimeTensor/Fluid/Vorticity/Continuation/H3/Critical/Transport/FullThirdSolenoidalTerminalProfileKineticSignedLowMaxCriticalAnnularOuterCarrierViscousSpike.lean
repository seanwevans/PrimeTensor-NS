import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularFixedInnerTerminalBandlimit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialDissipationCost244
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-!
# Actual selected outer kinetic carrier forces an eighth-order viscous Fourier cost

The preceding proof identified a genuine mass ledger and the 119/128 outer
retention fraction of every wide-annulus positive-deficit witness. This module
connects the ORIGINAL physical sharp highpass (not an abstract replacement)
to the accepted weighted H³ spectral highpass. The original ordered-third
Sobolev multiplier has weight-square `1 + q + q² + q³`, with
`q = (2π |ξ|)²`. Consequently, on frequencies above sigma,

   sigma^6 * ||(1-P_sigma) FourierRaw(G)||²
     <= ||(1-P_sigma) G||².

The existing physical dissipative radial theorem pays another sigma².
Thus sigma^8 times the actual physical highpass kinetic mass is bounded by
the genuine H³ dissipation at the SAME strict time.

A positive physical selected excess with margin m, a nonnegative actual
annular deficit, and sigma >= 2 rho therefore force

    119 * m * sigma^6 <= 80 * velocityH3DissipationAt u t.

A uniform positive margin and unbounded selected outer radius force
instantaneous H³ dissipation spikes. This does NOT imply a divergent time
integral: persistent positive-width windows or time lower bounds are still
needed for a continuation contradiction.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeOuterCarrierSpike244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceOuterCarrierSpike244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The *raw* Fourier highpass of a weighted H³ scalar state inherits the
exact sixth-power radius coercivity from the original Fourier weight. -/
theorem thirdFullKinetic_rawSharpHighpass_sixthMoment_le_weighted244
    (rho : ℝ) (hRho : 0 ≤ rho) (G : H3SpectralScalarState) :
    rho ^ 6 *
        ‖h3SpectralScalarRawFourierL2 G -
          h3CriticalFourierSharpLowCutoffCLM rho
            (h3SpectralScalarRawFourierL2 G)‖ ^ 2 ≤
      ‖G - h3CriticalFourierSharpLowCutoffCLM rho G‖ ^ 2 := by
  let F : H3FourierComplexL2 := h3SpectralScalarRawFourierL2 G
  let S : Set H3FourierPoint3 := (h3TerminalRadialFrequencyBelow rho)ᶜ
  have hS : MeasurableSet S :=
    (measurableSet_h3TerminalRadialFrequencyBelow rho).compl
  have hFInt : Integrable (fun ξ : H3FourierPoint3 => ‖F ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F).integrable_norm_pow (by norm_num)
  have hGInt : Integrable (fun ξ : H3FourierPoint3 => ‖G ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp G).integrable_norm_pow (by norm_num)
  have hRawAE : ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      (h3SobolevFrequencyWeight ξ : ℂ) * F ξ = G ξ := by
    filter_upwards [h3SpectralScalarRawFourierL2_ae G,
      h3SpectralScalarRawFourier_reweight_ae G] with ξ hF hWeight
    change (h3SobolevFrequencyWeight ξ : ℂ) * F ξ = G ξ
    rw [hF]
    exact hWeight
  have hAE : ∀ᵐ ξ ∂((volume : Measure H3FourierPoint3).restrict S),
      rho ^ 6 * ‖F ξ‖ ^ 2 ≤ ‖G ξ‖ ^ 2 := by
    rw [ae_restrict_iff' hS]
    filter_upwards [hRawAE] with ξ hWeight hTail
    have hFreq : rho ≤ h3FourierGradientMagnitude ξ := by
      apply le_of_not_gt
      change ¬ h3FourierGradientMagnitude ξ < rho at hTail
      exact hTail
    have hQ : 0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ
    have hQeq : h3FourierGradientSquare ξ =
        h3FourierGradientMagnitude ξ ^ 2 := by
      dsimp only [h3FourierGradientSquare, h3FourierGradientMagnitude]
      ring
    have hQlower : rho ^ 2 ≤ h3FourierGradientSquare ξ := by
      rw [hQeq]
      exact pow_le_pow_left₀ hRho hFreq 2
    have hQcube : rho ^ 6 ≤ h3FourierGradientSquare ξ ^ 3 := by
      calc
        rho ^ 6 = (rho ^ 2) ^ 3 := by ring
        _ ≤ h3FourierGradientSquare ξ ^ 3 :=
          pow_le_pow_left₀ (sq_nonneg rho) hQlower 3
    have hWeightLower : rho ^ 6 ≤ h3SobolevFrequencyWeight ξ ^ 2 := by
      rw [h3SobolevFrequencyWeight_sq]
      change rho ^ 6 ≤ 1 + h3FourierGradientSquare ξ +
        h3FourierGradientSquare ξ ^ 2 + h3FourierGradientSquare ξ ^ 3
      nlinarith only [hQcube, hQ, sq_nonneg (h3FourierGradientSquare ξ)]
    have hExact : ‖G ξ‖ ^ 2 =
        h3SobolevFrequencyWeight ξ ^ 2 * ‖F ξ‖ ^ 2 := by
      rw [← hWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (h3SobolevFrequencyWeight_pos ξ).le, mul_pow]
    rw [hExact]
    exact mul_le_mul_of_nonneg_right hWeightLower (sq_nonneg _)
  change rho ^ 6 * ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 ≤
    ‖G - h3CriticalFourierSharpLowCutoffCLM rho G‖ ^ 2
  rw [h3Critical_fourierSharpHighpass_norm_sq_eq_integral,
    h3Critical_fourierSharpHighpass_norm_sq_eq_integral]
  change rho ^ 6 * (∫ ξ in S, ‖F ξ‖ ^ 2 ∂volume) ≤
    ∫ ξ in S, ‖G ξ‖ ^ 2 ∂volume
  rw [← integral_const_mul]
  exact integral_mono_ae
    ((hFInt.const_mul _).mono_measure Measure.restrict_le_self)
    (hGInt.mono_measure Measure.restrict_le_self) hAE

/-- For an arbitrary real radius, the accepted weighted radial remainder is
exactly the sum of the three weighted sharp highpass L² squares. -/
theorem thirdFullKinetic_weightedSharpVectorHighpass_exact244
    (rho : ℝ) (G : H3SpectralVelocityState) :
    h3PathActualSpectralHighRadialRemainder244 rho G =
      ∑ j : Fin 3,
        ‖G j - h3CriticalFourierSharpLowCutoffCLM rho (G j)‖ ^ 2 := by
  let S : Set H3FourierPoint3 := (h3TerminalRadialFrequencyBelow rho)ᶜ
  have h0 : Integrable (fun ξ : H3FourierPoint3 => ‖G 0 ξ‖ ^ 2)
      ((volume : Measure H3FourierPoint3).restrict S) :=
    ((MeasureTheory.Lp.memLp (G 0)).norm.integrable_sq).mono_measure
      Measure.restrict_le_self
  have h1 : Integrable (fun ξ : H3FourierPoint3 => ‖G 1 ξ‖ ^ 2)
      ((volume : Measure H3FourierPoint3).restrict S) :=
    ((MeasureTheory.Lp.memLp (G 1)).norm.integrable_sq).mono_measure
      Measure.restrict_le_self
  have h2 : Integrable (fun ξ : H3FourierPoint3 => ‖G 2 ξ‖ ^ 2)
      ((volume : Measure H3FourierPoint3).restrict S) :=
    ((MeasureTheory.Lp.memLp (G 2)).norm.integrable_sq).mono_measure
      Measure.restrict_le_self
  calc
    h3PathActualSpectralHighRadialRemainder244 rho G =
        ∫ ξ in S, h3TerminalSpectralStateSquareAmplitude G ξ ∂volume := by
          simpa only [S] using
            h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244 rho G
    _ = (∫ ξ in S, ‖G 0 ξ‖ ^ 2 ∂volume) +
          (∫ ξ in S, ‖G 1 ξ‖ ^ 2 ∂volume) +
            (∫ ξ in S, ‖G 2 ξ‖ ^ 2 ∂volume) := by
          unfold h3TerminalSpectralStateSquareAmplitude
          have h012 := integral_add (h0.add h1) h2
          have h01 := integral_add h0 h1
          simp only [Pi.add_apply] at h012 h01
          rw [h012, h01]
    _ = ∑ j : Fin 3,
        ‖G j - h3CriticalFourierSharpLowCutoffCLM rho (G j)‖ ^ 2 := by
          simp only [Fin.sum_univ_three]
          rw [h3Critical_fourierSharpHighpass_norm_sq_eq_integral,
            h3Critical_fourierSharpHighpass_norm_sq_eq_integral,
            h3Critical_fourierSharpHighpass_norm_sq_eq_integral]

/-- The ORIGINAL physical three-component sharp kinetic highpass is paid
by the *native* weighted H³ high-radial remainder with a sixth-power radius.
The physical Plancherel and raw decoder are exact, with no surrogate state. -/
theorem thirdFullPhysical_actualSharpHighMass_sixthMoment_le_weighted244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rho : ℝ) (hRho : 0 ≤ rho) :
    rho ^ 6 * thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho ≤
      h3PathActualSpectralHighRadialRemainder244 rho
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let G : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  have hFourier (j : Fin 3) :
      h3ScalarFourierL2 (V.ofLp j) = h3SpectralScalarRawFourierL2 (G j) := by
    symm
    change h3SpectralScalarRawFourierL2
      (h3AuditActualSpectralVelocityTotal hH3 t j) = _
    rw [h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2 hH3 j t ht]
    simp only [V, h3AuditInitialOldPhysicalHilbertTotal, PiLp.toLp_apply]
  have hPhysical :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho =
        ∑ j : Fin 3,
          ‖h3SpectralScalarRawFourierL2 (G j) -
            h3CriticalFourierSharpLowCutoffCLM rho
              (h3SpectralScalarRawFourierL2 (G j))‖ ^ 2 := by
    unfold thirdFullPhysicalActualSharpKineticHighMass244
    change ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 = _
    calc
      ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 =
        ∑ j : Fin 3,
          ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V).ofLp j‖ ^ 2 :=
            PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => H3ScalarL2) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        change ‖V.ofLp j - h3CriticalPhysicalSharpLowCutoffApply rho
          (V.ofLp j)‖ ^ 2 = _
        calc
          ‖V.ofLp j - h3CriticalPhysicalSharpLowCutoffApply rho
              (V.ofLp j)‖ ^ 2 =
              ‖h3ScalarFourierL2
                (V.ofLp j - h3CriticalPhysicalSharpLowCutoffApply rho
                  (V.ofLp j))‖ ^ 2 := by
                rw [norm_h3ScalarFourierL2]
          _ = ‖h3ScalarFourierL2 (V.ofLp j) -
              h3CriticalFourierSharpLowCutoffCLM rho
                (h3ScalarFourierL2 (V.ofLp j))‖ ^ 2 := by
                rw [h3Critical_scalarFourier_physicalHighpass_eq]
          _ = _ := by rw [hFourier j]
  have hWeighted := thirdFullKinetic_weightedSharpVectorHighpass_exact244 rho G
  calc
    rho ^ 6 * thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho =
        ∑ j : Fin 3,
          rho ^ 6 * ‖h3SpectralScalarRawFourierL2 (G j) -
            h3CriticalFourierSharpLowCutoffCLM rho
              (h3SpectralScalarRawFourierL2 (G j))‖ ^ 2 := by
              rw [hPhysical, Finset.mul_sum]
    _ ≤ ∑ j : Fin 3,
          ‖G j - h3CriticalFourierSharpLowCutoffCLM rho (G j)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          exact thirdFullKinetic_rawSharpHighpass_sixthMoment_le_weighted244
            rho hRho (G j)
    _ = h3PathActualSpectralHighRadialRemainder244 rho G := hWeighted.symm

/-- True physical H³ dissipation pays the physical sharp kinetic highpass
at the *eighth* power of the Fourier gradient radius. Six powers come
from the exact H³ multiplier, and two from the extra viscous derivative. -/
theorem thirdFullPhysical_actualSharpHighMass_eighthViscousCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (rho : ℝ) (hRho : 0 ≤ rho) :
    (rho ^ 2) ^ 4 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho ≤
      velocityH3DissipationAt u t := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hMass := thirdFullPhysical_actualSharpHighMass_sixthMoment_le_weighted244
    hH3 t htAbs rho hRho
  have hDiss := h3Path_highRadialMass_le_fullDissipationAt244
    hH3 hClass t ht rho hRho
  calc
    (rho ^ 2) ^ 4 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho =
      rho ^ 2 * (rho ^ 6 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho) := by ring
    _ ≤ rho ^ 2 * h3PathActualSpectralHighRadialRemainder244 rho
        (h3AuditActualSpectralVelocityTotal hH3 t) :=
      mul_le_mul_of_nonneg_left hMass (sq_nonneg rho)
    _ ≤ velocityH3DissipationAt u t := hDiss

/-- Pure real algebra: the exact 119/128 outer carrier and the eighth-order
moment yield sixth-order viscosity payment for the TRUE margin m. -/
theorem thirdFullKinetic_wideOuterMargin_sixthViscous_scalar244
    (rho sigma margin Mhi Mout D : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMhi : 0 ≤ Mhi)
    (hMargin : margin ≤ ((rho ^ 2 + sigma ^ 2) / 2) * Mhi)
    (hCarrier : 119 * Mhi ≤ 128 * Mout)
    (hVisc : (sigma ^ 2) ^ 4 * Mout ≤ D) :
    119 * margin * sigma ^ 6 ≤ 80 * D := by
  have hSigma : 0 ≤ sigma := by linarith only [hRho, hAspect]
  have hSq : (2 * rho) ^ 2 ≤ sigma ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ 2 * rho) hAspect 2
  have hRadius : (rho ^ 2 + sigma ^ 2) / 2 ≤
      (5 / 8 : ℝ) * sigma ^ 2 := by
    nlinarith only [hSq]
  have hMcap : margin ≤ (5 / 8 : ℝ) * sigma ^ 2 * Mhi :=
    hMargin.trans (mul_le_mul_of_nonneg_right hRadius hMhi)
  have hMcap8 : 8 * margin ≤ 5 * sigma ^ 2 * Mhi := by
    nlinarith only [hMcap]
  have hScaled : 8 * (119 * margin * sigma ^ 6) ≤ 8 * (80 * D) := by
    calc
      8 * (119 * margin * sigma ^ 6) =
          (119 * sigma ^ 6) * (8 * margin) := by ring
      _ ≤ (119 * sigma ^ 6) * (5 * sigma ^ 2 * Mhi) :=
        mul_le_mul_of_nonneg_left hMcap8 (by positivity)
      _ = (5 * (sigma ^ 2) ^ 4) * (119 * Mhi) := by ring
      _ ≤ (5 * (sigma ^ 2) ^ 4) * (128 * Mout) :=
        mul_le_mul_of_nonneg_left hCarrier (by positivity)
      _ = (5 * 128) * ((sigma ^ 2) ^ 4 * Mout) := by ring
      _ ≤ (5 * 128) * D :=
        mul_le_mul_of_nonneg_left hVisc (by norm_num)
      _ = 8 * (80 * D) := by ring
  exact (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 8)).mp hScaled

/-- Actual physical selected excess and a nonnegative exact annular deficit
at sigma >= 2 rho compel sixth-power instantaneous full-H³ viscosity. -/
theorem thirdFullPhysical_selectedWideOuterMargin_forces_viscousSpike244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (rho sigma margin : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hDeficit : 0 ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    119 * margin * sigma ^ 6 ≤ 80 * velocityH3DissipationAt u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 htClass.1, htClass.2⟩
  have hOrder : rho ≤ sigma := by linarith only [hRho, hAspect]
  have hB : 0 ≤ Real.sqrt (velocityH3Energy0At u b) *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b)) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num)
      (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 _ _))
  have hMarginBound : margin ≤ ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho := by
    linarith only [hExcess, hB]
  have hMhi : 0 ≤ thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho :=
    sq_nonneg _
  have hCarrier := thirdFullPhysical_doubleAperture_outerCarrier119of128244
    hH3 t htAbs b rho sigma margin hRho hOrder hAspect hMargin hExcess hDeficit
  have hVisc := thirdFullPhysical_actualSharpHighMass_eighthViscousCharge244
    hH3 hClass t htClass sigma (by linarith only [hRho, hAspect])
  exact thirdFullKinetic_wideOuterMargin_sixthViscous_scalar244
    rho sigma margin
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 t sigma)
    (velocityH3DissipationAt u t) hRho hAspect hMhi
    hMarginBound hCarrier hVisc

/-- An actual finite viscosity cap limits the sixth power of the outer
radius whenever the selected strict-excess margin remains positive. -/
theorem thirdFullPhysical_selectedWideOuterMargin_viscousCapRadius244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (rho sigma margin H : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hDeficit : 0 ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma)
    (hCap : velocityH3DissipationAt u t ≤ H) :
    119 * margin * sigma ^ 6 ≤ 80 * H :=
  (thirdFullPhysical_selectedWideOuterMargin_forces_viscousSpike244
    hH3 hClass b hb t ht rho sigma margin hRho hAspect hMargin
      hExcess hDeficit).trans
    (mul_le_mul_of_nonneg_left hCap (by norm_num))


/-- If actual selected outer radii escape to infinity while positive
strict-excess margins remain bounded below, the genuine instantaneous
physical H³ dissipation diverges along the SAME snapshots. No disjoint
interval or integrability contradiction is asserted. -/
theorem thirdFullPhysical_selectedWideOuterMargins_force_viscousSpikes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x sigma margin : ℕ → ℝ) (rho c : ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hRho : 0 < rho) (hc : 0 < c)
    (hSigma : Tendsto sigma atTop atTop)
    (hMargin : ∀ k : ℕ, c ≤ margin k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin k ≤
      ((rho ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho)
    (hDeficit : ∀ k : ℕ,
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) rho (sigma k)) :
    Tendsto (fun k : ℕ => velocityH3DissipationAt u (x k))
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let R : ℝ := max (2 * rho) (max 1 (80 * max M 0 / (119 * c)))
  have hLate : ∀ᶠ k : ℕ in atTop, R ≤ sigma k :=
    hSigma.eventually (eventually_ge_atTop R)
  filter_upwards [hLate] with k hk
  have hAspect : 2 * rho ≤ sigma k :=
    (le_max_left _ _).trans hk
  have hOne : 1 ≤ sigma k :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hSix : sigma k ≤ sigma k ^ 6 := by
    have hPow := pow_le_pow_right₀ hOne (by norm_num : (1 : ℕ) ≤ 6)
    simpa only [pow_one] using hPow
  have hMargPos : 0 < margin k := lt_of_lt_of_le hc (hMargin k)
  have hCharge := thirdFullPhysical_selectedWideOuterMargin_forces_viscousSpike244
    hH3 hClass b hb (x k) (hx k) rho (sigma k) (margin k)
      hRho hAspect hMargPos (hExcess k) (hDeficit k)
  have hCPos : 0 < 119 * c := mul_pos (by norm_num) hc
  have hRLower : 80 * max M 0 / (119 * c) ≤ sigma k :=
    (le_max_right (1 : ℝ) _).trans ((le_max_right _ _).trans hk)
  have hFloor : 80 * max M 0 ≤ (119 * c) * sigma k := by
    have hScaled := (div_le_iff₀ hCPos).mp hRLower
    simpa only [mul_comm] using hScaled
  have hSigmaNonneg : 0 ≤ sigma k := le_trans (by norm_num) hOne
  have hPay : (119 * c) * sigma k ≤
      119 * margin k * sigma k ^ 6 := by
    calc
      (119 * c) * sigma k ≤ (119 * c) * sigma k ^ 6 :=
        mul_le_mul_of_nonneg_left hSix (by positivity)
      _ ≤ (119 * margin k) * sigma k ^ 6 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hMargin k) (by norm_num))
          (pow_nonneg hSigmaNonneg 6)
      _ = 119 * margin k * sigma k ^ 6 := by ring
  have hScaled : 80 * M ≤ 80 * velocityH3DissipationAt u (x k) := by
    calc
      80 * M ≤ 80 * max M 0 :=
        mul_le_mul_of_nonneg_left (le_max_left M 0) (by norm_num)
      _ ≤ (119 * c) * sigma k := hFloor
      _ ≤ 119 * margin k * sigma k ^ 6 := hPay
      _ ≤ 80 * velocityH3DissipationAt u (x k) := hCharge
  exact (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 80)).mp hScaled

end
end PrimeTensor.FirstMonomialTriad
