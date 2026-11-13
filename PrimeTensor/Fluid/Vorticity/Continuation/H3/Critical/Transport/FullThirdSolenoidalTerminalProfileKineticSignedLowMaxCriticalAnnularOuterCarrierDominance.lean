import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularWideApertureBandEvacuation
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-!
# Exact sharp highpass splitting and selected outer-carrier dominance

A genuine highpass above rho is the disjoint union of the selected annulus
[rho,sigma) and the highpass beyond sigma. We prove that this partition
remains an EXACT square-mass identity for the actual physical three-component
Navier--Stokes velocity. No abstract Fourier replacement is introduced.

Under positive strict selected kinetic excess and nonnegative genuine
annular deficit, the preceding Young-width theorem gives
  2 K^6 * N[rho,sigma] <= 9 * M[rho,infinity]
when sigma >= K*rho with K >= 2. The exact split then forces
  (2 K^6 - 9) * M[rho,infinity] <= 2 K^6 * M[sigma,infinity].

In particular sigma >= 2 rho retains at least 119/128 of the original
highpass mass beyond sigma. In the cofinal finite-dissipation setting,
aspect escape makes this true for every fixed K. These are conditional
constraints on genuine positive-deficit witnesses; existence of those
witnesses and regularity beyond the endpoint are not claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeOuterCarrier244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceOuterCarrier244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact raw Fourier L2 highpass partition. This is the square-mass
version of the disjoint measurable sharp annulus / outer tail split. -/
theorem thirdFullKinetic_sharpHighpass_annulusOuter_normSquare244
    (rho sigma : ℝ) (hOrder : rho ≤ sigma)
    (F : H3FourierComplexL2) :
    ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 =
      ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
        h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 +
      ‖F - h3CriticalFourierSharpLowCutoffCLM sigma F‖ ^ 2 := by
  let ann : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow rho)ᶜ ∩
      h3TerminalRadialFrequencyBelow sigma
  let tail : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow sigma)ᶜ
  let high : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow rho)ᶜ
  let f : H3FourierPoint3 → ℝ := fun ξ => ‖F ξ‖ ^ 2
  have hf : Integrable f (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F).integrable_norm_pow (by norm_num)
  have hDisj : Disjoint ann tail :=
    thirdFullKinetic_sharpRadialAnnulus_outer_disjoint244 rho sigma
  have hTailMeas : MeasurableSet tail :=
    (measurableSet_h3TerminalRadialFrequencyBelow sigma).compl
  have hUnion : high = ann ∪ tail :=
    thirdFullKinetic_sharpRadialHighpass_annulusOuter_partition244
      rho sigma hOrder
  have hIntegral : (∫ ξ in high, f ξ ∂volume) =
      (∫ ξ in ann, f ξ ∂volume) +
        (∫ ξ in tail, f ξ ∂volume) := by
    rw [hUnion]
    exact setIntegral_union (s := ann) (t := tail)
      hDisj hTailMeas hf.integrableOn hf.integrableOn
  have hHigh : ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 =
      ∫ ξ in high, f ξ ∂volume :=
    h3Critical_fourierSharpHighpass_norm_sq_eq_integral rho F
  have hBand :
      ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
        h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 =
      ∫ ξ in ann, f ξ ∂volume :=
    thirdFullKinetic_sharpFourierAnnulusCutoff_norm_sq_eq_integral244
      rho sigma hOrder F
  have hOuter : ‖F - h3CriticalFourierSharpLowCutoffCLM sigma F‖ ^ 2 =
      ∫ ξ in tail, f ξ ∂volume :=
    h3Critical_fourierSharpHighpass_norm_sq_eq_integral sigma F
  calc
    ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 =
        ∫ ξ in high, f ξ ∂volume := hHigh
    _ = (∫ ξ in ann, f ξ ∂volume) +
          (∫ ξ in tail, f ξ ∂volume) := hIntegral
    _ = ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
          h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 +
        ‖F - h3CriticalFourierSharpLowCutoffCLM sigma F‖ ^ 2 := by
          rw [hBand, hOuter]

/-- At an actual strictly positive physical time, the genuine physical
sharp kinetic highpass splits EXACTLY into the actual raw annular mass and
the farther physical sharp outer highpass. -/
theorem thirdFullPhysical_actualSharpHighMass_annulusOuter_exact244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rho sigma : ℝ) (hOrder : rho ≤ sigma) :
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho =
      thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma +
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t sigma := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have hFourier (j : Fin 3) :
      h3ScalarFourierL2 (V.ofLp j) =
        h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) := by
    symm
    change h3SpectralScalarRawFourierL2
      (h3AuditActualSpectralVelocityTotal hH3 t j) = _
    rw [h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2
      hH3 j t ht]
    simp only [V, h3AuditInitialOldPhysicalHilbertTotal, PiLp.toLp_apply]
  have hComponent (j : Fin 3) :
      ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V).ofLp j‖ ^ 2 =
        ‖h3CriticalFourierSharpLowCutoffCLM sigma
            (h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
          h3CriticalFourierSharpLowCutoffCLM rho
            (h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2 +
        ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V).ofLp j‖ ^ 2 := by
    let f : H3ScalarL2 := V.ofLp j
    let F : H3FourierComplexL2 := h3ScalarFourierL2 f
    have hRho :
        ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V).ofLp j‖ ^ 2 =
          ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 := by
      change ‖f - h3CriticalPhysicalSharpLowCutoffApply rho f‖ ^ 2 = _
      calc
        ‖f - h3CriticalPhysicalSharpLowCutoffApply rho f‖ ^ 2 =
            ‖h3ScalarFourierL2
              (f - h3CriticalPhysicalSharpLowCutoffApply rho f)‖ ^ 2 := by
                rw [norm_h3ScalarFourierL2]
        _ = ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 := by
          rw [h3Critical_scalarFourier_physicalHighpass_eq]
    have hSigma :
        ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V).ofLp j‖ ^ 2 =
          ‖F - h3CriticalFourierSharpLowCutoffCLM sigma F‖ ^ 2 := by
      change ‖f - h3CriticalPhysicalSharpLowCutoffApply sigma f‖ ^ 2 = _
      calc
        ‖f - h3CriticalPhysicalSharpLowCutoffApply sigma f‖ ^ 2 =
            ‖h3ScalarFourierL2
              (f - h3CriticalPhysicalSharpLowCutoffApply sigma f)‖ ^ 2 := by
                rw [norm_h3ScalarFourierL2]
        _ = ‖F - h3CriticalFourierSharpLowCutoffCLM sigma F‖ ^ 2 := by
          rw [h3Critical_scalarFourier_physicalHighpass_eq]
    calc
      ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V).ofLp j‖ ^ 2 =
          ‖F - h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 := hRho
      _ = ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
            h3CriticalFourierSharpLowCutoffCLM rho F‖ ^ 2 +
          ‖F - h3CriticalFourierSharpLowCutoffCLM sigma F‖ ^ 2 :=
            thirdFullKinetic_sharpHighpass_annulusOuter_normSquare244
              rho sigma hOrder F
      _ = ‖h3CriticalFourierSharpLowCutoffCLM sigma
            (h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
          h3CriticalFourierSharpLowCutoffCLM rho
            (h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2 +
          ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V).ofLp j‖ ^ 2 := by
              rw [← hSigma]
              exact congrArg
                (fun q : ℝ =>
                  q + ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V).ofLp j‖ ^ 2)
                (congrArg
                  (fun G : H3FourierComplexL2 =>
                    ‖h3CriticalFourierSharpLowCutoffCLM sigma G -
                      h3CriticalFourierSharpLowCutoffCLM rho G‖ ^ 2)
                  (hFourier j))
  change ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 =
    (∑ j : Fin 3,
      ‖h3CriticalFourierSharpLowCutoffCLM sigma
          (h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
        h3CriticalFourierSharpLowCutoffCLM rho
          (h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2) +
      ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V‖ ^ 2
  calc
    ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 =
        ∑ j : Fin 3,
          ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V).ofLp j‖ ^ 2 :=
            PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => H3ScalarL2) _
    _ = ∑ j : Fin 3,
          (‖h3CriticalFourierSharpLowCutoffCLM sigma
              (h3SpectralScalarRawFourierL2
                ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
            h3CriticalFourierSharpLowCutoffCLM rho
              (h3SpectralScalarRawFourierL2
                ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2 +
            ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V).ofLp j‖ ^ 2) := by
              exact Finset.sum_congr rfl (fun j _ => hComponent j)
    _ = (∑ j : Fin 3,
          ‖h3CriticalFourierSharpLowCutoffCLM sigma
              (h3SpectralScalarRawFourierL2
                ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
            h3CriticalFourierSharpLowCutoffCLM rho
              (h3SpectralScalarRawFourierL2
                ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2) +
          (∑ j : Fin 3,
            ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V).ofLp j‖ ^ 2) :=
              Finset.sum_add_distrib
    _ = (∑ j : Fin 3,
          ‖h3CriticalFourierSharpLowCutoffCLM sigma
              (h3SpectralScalarRawFourierL2
                ((h3AuditActualSpectralVelocityTotal hH3 t) j)) -
            h3CriticalFourierSharpLowCutoffCLM rho
              (h3SpectralScalarRawFourierL2
                ((h3AuditActualSpectralVelocityTotal hH3 t) j))‖ ^ 2) +
          ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V‖ ^ 2 := by
            rw [PiLp.norm_sq_eq_of_L2
              (fun _ : Fin 3 => H3ScalarL2)
              (V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V)]

/-- When the annular budget is small, exact partition transfers the missing
highpass kinetic mass to the far outer tail. No hypothesis about PDE needed. -/
theorem thirdFullKinetic_outerCarrier_from_annularBudget244
    (q M N O : ℝ)
    (hSplit : M = N + O)
    (hBand : q * N ≤ 9 * M) :
    (q - 9) * M ≤ q * O := by
  calc
    (q - 9) * M = q * M - 9 * M := by ring
    _ ≤ q * M - q * N := sub_le_sub_left hBand _
    _ = q * O := by rw [hSplit]; ring

/-- The full exact physical positive-deficit estimate retains at least
(1 - 9/(2*K^6)) of all selected highpass mass beyond the outer cutoff.
No division by the vanishing highpass mass is needed. -/
theorem thirdFullPhysical_wideAnnularPositiveDeficit_outerCarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (b rho sigma K margin : ℝ)
    (hRho : 0 < rho) (hOrder : rho ≤ sigma)
    (hK : 2 ≤ K) (hAspect : K * rho ≤ sigma)
    (hMargin : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hDeficit : 0 ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    (2 * K ^ 6 - 9) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho ≤
      2 * K ^ 6 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t sigma := by
  have hTwo : 2 * rho ≤ sigma :=
    (mul_le_mul_of_nonneg_right hK hRho.le).trans hAspect
  have hSquare : (2 * rho) ^ 2 ≤ sigma ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ 2 * rho) hTwo 2
  have hWide : 2 * rho ^ 2 ≤ sigma ^ 2 := by
    nlinarith only [hSquare, sq_nonneg rho]
  have hBand :=
    thirdFullPhysical_wideAnnularPositiveDeficit_forces_rawBandEvacuation244
      hH3 b t rho sigma hRho hOrder hWide margin hMargin hExcess hDeficit
  have hMassNonneg :
      0 ≤ thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma := by
    unfold thirdFullPhysicalActualSharpAnnularRawMass244
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hFraction := thirdFullKinetic_wideAnnularBand_normalizedAspect244
    rho sigma K
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma)
    hRho hK hAspect hMassNonneg hBand
  have hSplit := thirdFullPhysical_actualSharpHighMass_annulusOuter_exact244
    hH3 t ht rho sigma hOrder
  exact thirdFullKinetic_outerCarrier_from_annularBudget244
    (2 * K ^ 6)
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (thirdFullPhysicalActualSharpAnnularRawMass244 hH3 t rho sigma)
    (thirdFullPhysicalActualSharpKineticHighMass244 hH3 t sigma)
    hSplit hFraction

/-- Even a ratio 2 already forces at least 119/128 of the highpass mass
beyond the selected outer cutoff, provided the genuine physical deficit
is nonnegative. The original strict kinetic excess is retained. -/
theorem thirdFullPhysical_doubleAperture_outerCarrier119of128244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (b rho sigma margin : ℝ)
    (hRho : 0 < rho) (hOrder : rho ≤ sigma)
    (hAspect : 2 * rho ≤ sigma) (hMargin : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hDeficit : 0 ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    119 * thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho ≤
      128 * thirdFullPhysicalActualSharpKineticHighMass244 hH3 t sigma := by
  have h := thirdFullPhysical_wideAnnularPositiveDeficit_outerCarrier244
    hH3 t ht b rho sigma (2 : ℝ) margin
    hRho hOrder (by norm_num) hAspect hMargin hExcess hDeficit
  norm_num at h
  exact h

/-- In the genuine finite-dissipation cofinal regime, the committed aspect
escape theorem promotes physical outer-carrier retention to EVERY fixed
K >= 2. The result is eventual, with K fixed before the terminal index. -/
theorem thirdFullPhysical_finiteDissipation_selectedNaturalOuterCarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x sigma margin : ℕ → ℝ) (n : ℕ → ℕ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hn : Tendsto n atTop atTop)
    (hOrder : ∀ k : ℕ, (n k : ℝ) + 1 ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          ((n k : ℝ) + 1) (velocityH3Energy0At u b)) + margin k ≤
        ((((n k : ℝ) + 1) ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k)
            ((n k : ℝ) + 1))
    (hDeficit : ∀ k : ℕ,
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) ((n k : ℝ) + 1) (sigma k)) :
    ∀ K : ℝ, 2 ≤ K → ∀ᶠ k : ℕ in atTop,
      (2 * K ^ 6 - 9) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k)
          ((n k : ℝ) + 1) ≤
      2 * K ^ 6 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k)
          (sigma k) := by
  intro K hK
  have hAspect :=
    thirdFullPhysical_finiteDissipation_selectedNaturalExcess_aspectEscape244
      hH3 hClass hDInt b hb x sigma margin n
      hx hCofinal hn hOrder hMargin hExcess K (by linarith only [hK])
  filter_upwards [hAspect] with k hk
  have ht : x k ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 (hx k).1),
      (hx k).2⟩
  exact thirdFullPhysical_wideAnnularPositiveDeficit_outerCarrier244
    hH3 (x k) ht b ((n k : ℝ) + 1) (sigma k) K (margin k)
    (by positivity) (hOrder k) hK hk.le (hMargin k)
    (hExcess k) (hDeficit k)

end
end PrimeTensor.FirstMonomialTriad
