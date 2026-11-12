import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalSharpAnnularPhysicalCompensation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationPointwise
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-!
# Actual annular anti-heat budget: outer Fourier tail charged to physical H3 source

The preceding theorem uses an exact Fourier outer-tail mismatch as its third
necessary expenditure. Here the same tail is transported by the *actual*
physical Plancherel bridge, then bounded by genuine sharp physical highpass
source and kinetic states, and finally by the already proved pointwise
projected-source / full-H3 dissipation estimate.

At a strict time after kinetic anchor b, write E=E0(b), D=D3(t),
C=(3+C_L)(1+6E+3D), rate=(rho^2+sigma^2)/2. The uncompensated outer
Fourier tail is bounded above by

                   2*C^2 + 2*rate^2*E.

This is NOT a viscosity-only L1 bound. It is quadratic in the instantaneous
full-H3 dissipation. The original disjoint viscous clocks provide an L1
budget, which by itself does not control its square. That obstruction is
retained, not silently erased. The inner Young-gap and annulus-width terms
also remain exactly as in the preceding theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeOuterKineticViscous244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceOuterKineticViscous244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact Hilbert triangle/Young estimate for a CONSTANT real rate, without
any positivity assumption on that rate. The rate is squared, not replaced
by its absolute value by assumption. -/
theorem thirdFullKinetic_realHilbertRateMismatch_square_le244
    (X Y : H3PhysicalRealFinVectorL2Hilbert) (rate : ℝ) :
    ‖X - rate • Y‖ ^ 2 ≤
      2 * ‖X‖ ^ 2 + 2 * rate ^ 2 * ‖Y‖ ^ 2 := by
  have hTri : ‖X - rate • Y‖ ≤ ‖X‖ + ‖rate • Y‖ :=
    norm_sub_le X (rate • Y)
  have hNonneg : 0 ≤ ‖X‖ + ‖rate • Y‖ :=
    add_nonneg (norm_nonneg X) (norm_nonneg (rate • Y))
  have hSq : ‖X - rate • Y‖ ^ 2 ≤
      (‖X‖ + ‖rate • Y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hNonneg).mpr hTri
  have hYoung : (‖X‖ + ‖rate • Y‖) ^ 2 ≤
      2 * ‖X‖ ^ 2 + 2 * ‖rate • Y‖ ^ 2 := by
    nlinarith only [sq_nonneg (‖X‖ - ‖rate • Y‖)]
  have hBound := hSq.trans hYoung
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc] using hBound

/-- The ACTUAL real three-component Fourier highpass has no larger L2 mass
than its input. This is the highpass half of sharp physical Pythagoras. -/
theorem thirdFullPhysical_sharpVectorHighpass_norm_le244
    (sigma : ℝ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V‖ ≤ ‖V‖ := by
  have hOrth := thirdFullPhysical_sharpVectorLowHigh_normSquare244 sigma V
  have hSq :
      ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 sigma V‖ ^ 2 ≤
        ‖V‖ ^ 2 := by
    nlinarith only [hOrth,
      sq_nonneg (‖thirdFullPhysicalSharpLowCutoffHilbert244 sigma V‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq

/-- The ACTUAL spectral outer-tail mismatch is controlled by the real
physical outer source and velocity highpass masses, with an exact factor 2.
The Fourier identities are the accepted scalar/vector Plancherel results. -/
theorem thirdFullPhysical_outerFourierMismatch_le_physicalHighpasses244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (sigma rate : ℝ) :
    let U : H3PhysicalRealFinVectorL2Hilbert :=
      h3AuditInitialOldPhysicalHilbertTotal hH3 t
    let R : H3PhysicalRealFinVectorL2Hilbert :=
      h3PathActualProjectedMomentumSource244 hH3 t
    (∑ j : Fin 3, ∫ ξ in (h3TerminalRadialFrequencyBelow sigma)ᶜ,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
        H3FourierPoint3 → ℂ) ξ -
        (rate : ℂ) * h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2 ∂volume) ≤
      2 * ‖R - thirdFullPhysicalSharpLowCutoffHilbert244 sigma R‖ ^ 2 +
        2 * rate ^ 2 *
          ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 sigma U‖ ^ 2 := by
  dsimp only
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  have hExact := thirdFullPhysical_sharpActualRateMismatch_normSquare244
    hH3 t ht sigma rate
  dsimp only at hExact
  calc
    (∑ j : Fin 3, ∫ ξ in (h3TerminalRadialFrequencyBelow sigma)ᶜ,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
        H3FourierPoint3 → ℂ) ξ -
        (rate : ℂ) * h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2 ∂volume) =
      ‖(R - thirdFullPhysicalSharpLowCutoffHilbert244 sigma R) -
        rate • (U - thirdFullPhysicalSharpLowCutoffHilbert244 sigma U)‖ ^ 2 := by
          simpa only [R, U] using hExact.symm
    _ ≤ 2 * ‖R - thirdFullPhysicalSharpLowCutoffHilbert244 sigma R‖ ^ 2 +
        2 * rate ^ 2 *
          ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 sigma U‖ ^ 2 :=
      thirdFullKinetic_realHilbertRateMismatch_square_le244 _ _ rate

/-- An explicit same-time kinetic + full-H3 viscous upper ceiling for the
actual physical Fourier outer-tail source/velocity mismatch. -/
noncomputable def thirdFullPhysicalOuterKineticViscousBudget244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b t rate : ℝ) : ℝ :=
  2 * ((3 + h3AuditInitialLerayEnergyCoefficient) *
      (1 + 6 * velocityH3Energy0At u b +
        3 * velocityH3DissipationAt u t)) ^ 2 +
    2 * rate ^ 2 * velocityH3Energy0At u b

/-- The outer Fourier error is charged entirely to the actual projected
physical source ceiling and kinetic energy at an earlier anchor. The
pointwise full H3 viscous dissipation is explicit, NOT assumed integrable
in square over terminal time. -/
theorem thirdFullPhysical_outerFourierMismatch_le_kineticViscous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (sigma rate : ℝ) :
    (∑ j : Fin 3, ∫ ξ in (h3TerminalRadialFrequencyBelow sigma)ᶜ,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
        H3FourierPoint3 → ℂ) ξ -
        (rate : ℂ) * h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2 ∂volume) ≤
      thirdFullPhysicalOuterKineticViscousBudget244 u b t rate := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let C : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
    (1 + 6 * velocityH3Energy0At u b +
      3 * velocityH3DissipationAt u t)
  have hSrc : ‖R - thirdFullPhysicalSharpLowCutoffHilbert244 sigma R‖ ≤ C :=
    (thirdFullPhysical_sharpVectorHighpass_norm_le244 sigma R).trans
      (h3Critical_projected_source_le_kinetic_anchor_add_dissipation
        hH3 hClass hb ht)
  have hC0 : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have hCoefficient := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [hCoefficient]
  have hC1 : 0 ≤ 1 + 6 * velocityH3Energy0At u b +
      3 * velocityH3DissipationAt u t := by
    have hE : 0 ≤ velocityH3Energy0At u b := velocityH3Energy0At_nonneg u b
    have hD : 0 ≤ velocityH3DissipationAt u t := velocityH3DissipationAt_nonneg u t
    linarith only [hE, hD]
  have hC : 0 ≤ C := mul_nonneg hC0 hC1
  have hSrcSq :
      ‖R - thirdFullPhysicalSharpLowCutoffHilbert244 sigma R‖ ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hC).mpr hSrc
  have hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hbAbs.1 ht.1, ht.2⟩
  have hKin : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    (h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3)
      hbAbs htAbs ht.1.le
  have hNorm : ‖U‖ ^ 2 = velocityH3Energy0At u t :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t htAbs
  have hVel :
      ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 sigma U‖ ≤ ‖U‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_le244 sigma U
  have hVelSq :
      ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 sigma U‖ ^ 2 ≤
        velocityH3Energy0At u b := by
    have hSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hVel
    linarith only [hSq, hNorm, hKin]
  have hFourier := thirdFullPhysical_outerFourierMismatch_le_physicalHighpasses244
    hH3 t htAbs sigma rate
  dsimp only at hFourier
  have hSourceTerm :
      2 * ‖R - thirdFullPhysicalSharpLowCutoffHilbert244 sigma R‖ ^ 2 ≤
        2 * C ^ 2 :=
    mul_le_mul_of_nonneg_left hSrcSq (by norm_num)
  have hVelocityTerm :
      2 * rate ^ 2 *
        ‖U - thirdFullPhysicalSharpLowCutoffHilbert244 sigma U‖ ^ 2 ≤
      2 * rate ^ 2 * velocityH3Energy0At u b :=
    mul_le_mul_of_nonneg_left hVelSq (by positivity)
  have hBound := hFourier.trans (add_le_add hSourceTerm hVelocityTerm)
  simpa only [thirdFullPhysicalOuterKineticViscousBudget244, C, U, R] using hBound

/-- Retain the genuine finite-annulus Young-gap and width expenses, but
replace the Fourier outer-tail term with the explicit physical kinetic and
full-H3 viscous source ceiling. -/
noncomputable def thirdFullPhysicalActualAnnularViscousCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b t rho sigma : ℝ) : ℝ :=
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
    thirdFullPhysicalOuterKineticViscousBudget244 u b t rate

/-- A purely quantitative comparison of the previous exact Fourier ledger
with the new PHYSICAL full-dissipation version. The actual outer tail is
never claimed zero and no integration over time is performed. -/
theorem thirdFullPhysical_actualAnnularLedger_le_viscousCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (rho sigma : ℝ) :
    thirdFullPhysicalActualAnnularLedgerCost244 hH3 t rho sigma ≤
      thirdFullPhysicalActualAnnularViscousCost244 hH3 b t rho sigma := by
  have hTail := thirdFullPhysical_outerFourierMismatch_le_kineticViscous244
    hH3 hClass b hb t ht sigma ((rho ^ 2 + sigma ^ 2) / 2)
  have hW : 0 ≤ (rho ^ 2) ^ 3 :=
    pow_nonneg (sq_nonneg rho) 3
  have hWeighted := mul_le_mul_of_nonneg_left hTail hW
  unfold thirdFullPhysicalActualAnnularLedgerCost244
    thirdFullPhysicalActualAnnularViscousCost244
  dsimp only
  exact add_le_add_right hWeighted _

/-- The ACTUAL kinetic excess must be paid by annular Young-gap, annulus
width, and the explicit source/viscous outer budget. The latter has a D3(t)^2
term, so disjoint L1 dissipation alone does NOT close the endpoint estimate. -/
theorem thirdFullPhysical_kineticExcess_forces_annularViscousCost244
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
        thirdFullPhysicalActualAnnularViscousCost244 hH3 b t rho sigma := by
  have hPrevious := thirdFullPhysical_kineticExcess_forces_annularYoungGapTail244
    hH3 hClass b hb rho sigma hRho hOrder t ht hExcess
  have hCost := thirdFullPhysical_actualAnnularLedger_le_viscousCost244
    hH3 hClass b hb t ht rho sigma
  have hNonneg :
      0 ≤ ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2 :=
    sq_nonneg _
  exact hPrevious.trans (mul_le_mul_of_nonneg_left hCost hNonneg)

end
end PrimeTensor.FirstMonomialTriad
