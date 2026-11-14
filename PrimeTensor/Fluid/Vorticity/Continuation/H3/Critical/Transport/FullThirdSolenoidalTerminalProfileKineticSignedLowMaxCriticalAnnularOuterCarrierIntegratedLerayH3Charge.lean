import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierSharpHighpassCLM
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceMeasurability
import Mathlib.Tactic

/-!
# Selected outer nonlinear Leray work requires integrated physical H³ cost

The sharp Fourier highpass is now a genuine contractive real Hilbert CLM.
Instead of postulating an unquantified nonlinear increment B, this file
charges B to the actual physical quadratic Leray source, integrated over
THE SAME positive-time window:

  ||P_high ∫ N(u)|| <= C_Leray ∫ ||U(t)||_{H³}² dt.

The physical source is the previously identified inverse-Fourier Leray
forcing of the ACTUAL spectral state. The bound has no cutoff dependence.

When frozen diffusion plus the cutoff-uniform commutator cannot finance a
selected highpass kinetic drain, the signed alignment theorem then forces

  ||A-B||² < 2 ||H|| C_Leray ∫ ||U(t)||_{H³}² dt.

Crucially this is an INTEGRATED H³² charge, not a supremum-based envelope.
It is a conditional necessary cost, not terminal-uniform regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- At a genuine strict physical time the ACTUAL inverse-Fourier Leray
forcing is quadratically controlled by the actual weighted H³ state. -/
theorem thirdFullPhysical_actualLeray_norm_le_H3Square244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialActualSpectralLerayTotal hH3 t‖ ≤
      h3AuditInitialLerayEnergyCoefficient *
        ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 := by
  have hActual : h3AuditInitialActualSpectralLerayTotal hH3 t =
      h3AuditSpectralPhysicalLerayForcing
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
    simp only [h3AuditInitialActualSpectralLerayTotal, dite_eq_left ht]
  rw [hActual]
  simpa only [pow_two] using
    (h3AuditSpectralPhysicalLerayForcing_norm_le
      (h3AuditActualSpectralVelocityTotal hH3 t))

/-- On an arbitrary compact strictly positive time interval, both the actual
Leray source and the squared actual spectral H³ norm are Bochner/scalar L¹.
The integrability follows from the already-proved continuous H³ path. -/
theorem thirdFullPhysical_actualLeray_and_H3Square_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) (hxs : x ≤ s) :
    IntervalIntegrable (h3AuditInitialActualSpectralLerayTotal hH3) volume x s ∧
    IntervalIntegrable
      (fun r : ℝ => ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2)
      volume x s := by
  let U := h3AuditActualSpectralVelocityTotal hH3
  have hSub : Set.Icc x s ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hx.1 hr.1, lt_of_le_of_lt hr.2 hs.2⟩
  have hU : ContinuousOn U (Set.Icc x s) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub
  have hNComp : ContinuousOn
      (fun r : ℝ => h3AuditSpectralPhysicalLerayForcing (U r))
      (Set.Icc x s) :=
    continuous_h3AuditSpectralPhysicalLerayForcing.comp_continuousOn hU
  have hN : ContinuousOn
      (h3AuditInitialActualSpectralLerayTotal hH3) (Set.Icc x s) := by
    apply hNComp.congr
    intro r hr
    change h3AuditInitialActualSpectralLerayTotal hH3 r =
      h3AuditSpectralPhysicalLerayForcing
        (h3AuditActualSpectralVelocityTotal hH3 r)
    simp only [h3AuditInitialActualSpectralLerayTotal,
      dite_eq_left (hSub hr)]
  constructor
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxs]
    exact hN
  · have hNormSq : ContinuousOn
        (fun r : ℝ => ‖U r‖ ^ 2) (Set.Icc x s) := hU.norm.pow 2
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxs]
    exact hNormSq

/-- Exact cutoff-INDEPENDENT payment of an ACTUAL nonlinear Leray highpass
increment by the integral of the actual physical spectral H³² energy. -/
theorem thirdFullPhysical_outerIntegratedLeray_norm_le_H3Cost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) (hxs : x ≤ s) :
    ‖thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho‖ ≤
      h3AuditInitialLerayEnergyCoefficient *
        ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 := by
  let N := h3AuditInitialActualSpectralLerayTotal hH3
  let U := h3AuditActualSpectralVelocityTotal hH3
  let C : ℝ := h3AuditInitialLerayEnergyCoefficient
  have hC : 0 ≤ C := h3AuditInitialLerayEnergyCoefficient_nonneg
  obtain ⟨hNInt, hUInt⟩ :=
    thirdFullPhysical_actualLeray_and_H3Square_intervalIntegrable244
      hH3 x s hx hs hxs
  have hPoint (r : ℝ) (hr : r ∈ Set.Icc x s) :
      ‖N r‖ ≤ C * ‖U r‖ ^ 2 := by
    have hrT : r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le hx.1 hr.1, lt_of_le_of_lt hr.2 hs.2⟩
    exact thirdFullPhysical_actualLeray_norm_le_H3Square244 hH3 r hrT
  have hIntegral :
      ‖∫ r in x..s, N r‖ ≤
        C * ∫ r in x..s, ‖U r‖ ^ 2 := by
    calc
      ‖∫ r in x..s, N r‖ ≤ ∫ r in x..s, ‖N r‖ :=
        intervalIntegral.norm_integral_le_integral_norm hxs
      _ ≤ ∫ r in x..s, C * ‖U r‖ ^ 2 :=
        intervalIntegral.integral_mono_on hxs hNInt.norm
          (hUInt.const_mul C) hPoint
      _ = C * ∫ r in x..s, ‖U r‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
  change ‖(∫ r in x..s, N r) -
    thirdFullPhysicalSharpLowCutoffHilbert244 rho (∫ r in x..s, N r)‖ ≤ _
  exact (thirdFullPhysical_sharpVectorHighpass_norm_le244 rho _).trans hIntegral

/-- Hilbert Cauchy-Schwarz converts strict initial-carrier alignment into a
strict lower bound on the nonlinear action, without dividing by ||H||. -/
theorem thirdFullKinetic_initialAlignment_forcesLerayActionCost244
    (H A B : H3PhysicalRealFinVectorL2Hilbert)
    (M : ℝ) (hB : ‖B‖ ≤ M)
    (hAlignment : ‖A - B‖ ^ 2 < 2 * inner ℝ H B) :
    ‖A - B‖ ^ 2 < 2 * ‖H‖ * M := by
  have hCauchy : inner ℝ H B ≤ ‖H‖ * ‖B‖ :=
    (abs_le.mp (abs_real_inner_le_norm H B)).2
  have hWeighted : 2 * ‖H‖ * ‖B‖ ≤ 2 * ‖H‖ * M :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  nlinarith only [hAlignment, hCauchy, hWeighted]

/-- The signed Leray cost can also be read as positivity of the temporal
H³² action whenever the net highpass velocity displacement is charged. -/
theorem thirdFullKinetic_positiveH3Action_of_alignment244
    (H A B : H3PhysicalRealFinVectorL2Hilbert)
    (C E : ℝ) (hC : 0 ≤ C)
    (hB : ‖B‖ ≤ C * E)
    (hAlignment : ‖A - B‖ ^ 2 < 2 * inner ℝ H B) :
    0 < E := by
  have hPrice := thirdFullKinetic_initialAlignment_forcesLerayActionCost244
    H A B (C * E) hB hAlignment
  have hSq : 0 ≤ ‖A - B‖ ^ 2 := sq_nonneg _
  have hPositive : 0 < 2 * ‖H‖ * (C * E) := lt_of_le_of_lt hSq hPrice
  by_contra hNot
  have hE : E ≤ 0 := le_of_not_gt hNot
  have hCE : C * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hE
  have hRight : 2 * ‖H‖ * (C * E) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hCE
  exact (not_le_of_gt hPositive) hRight

/-- The selected outer physical highpass alignment now pays an integral
of the ACTUAL H³² path, not an abstract source vector or time supremum.
The same interior-time delta works for ALL sharp radii. -/
theorem thirdFullPhysical_outerForcedLeray_integratedH3Charge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T → x ≤ s → s - x < delta →
        ∀ rho K epsilon : ℝ, 0 < K →
        epsilon < K *
          (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) →
        let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
        let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
        let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
        let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
        K * (2 * (s - x) * (-inner ℝ H D) +
          2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon →
        ‖A - B‖ ^ 2 <
          2 * ‖H‖ * (h3AuditInitialLerayEnergyCoefficient *
            ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2) := by
  obtain ⟨delta, hdelta, hNear⟩ :=
    thirdFullPhysical_outerFrozenForcesInitialAlignment_uniformActual244
      hH3 x eta hx heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hxs hsDelta rho K epsilon hK hForced
  intro H D A B hBudget
  have hAlignment := hNear s hs hxs hsDelta rho K epsilon hK hForced
  change (K * (2 * (s - x) * (-inner ℝ H D) +
      2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon) →
      ‖A - B‖ ^ 2 < 2 * inner ℝ H B at hAlignment
  have hSigned := hAlignment hBudget
  have hAction : ‖B‖ ≤
      h3AuditInitialLerayEnergyCoefficient *
        ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 := by
    exact thirdFullPhysical_outerIntegratedLeray_norm_le_H3Cost244
      hH3 x s rho hx hs hxs
  exact thirdFullKinetic_initialAlignment_forcesLerayActionCost244
    H A B _ hAction hSigned

/-- On each forced nonlinear-transfer window the actual spectral H³²
integral is STRICTLY positive. This follows from a quantitative cost,
not from an assumed nonzero Fourier carrier or extra regularity. -/
theorem thirdFullPhysical_outerForcedLeray_positiveIntegratedH3Charge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T → x ≤ s → s - x < delta →
        ∀ rho K epsilon : ℝ, 0 < K →
        epsilon < K *
          (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) →
        let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
        let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
        let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
        let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
        K * (2 * (s - x) * (-inner ℝ H D) +
          2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon →
        0 < ∫ r in x..s,
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 := by
  obtain ⟨delta, hdelta, hNear⟩ :=
    thirdFullPhysical_outerFrozenForcesInitialAlignment_uniformActual244
      hH3 x eta hx heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hxs hsDelta rho K epsilon hK hForced
  intro H D A B hBudget
  have hAlignment := hNear s hs hxs hsDelta rho K epsilon hK hForced
  change (K * (2 * (s - x) * (-inner ℝ H D) +
      2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon) →
      ‖A - B‖ ^ 2 < 2 * inner ℝ H B at hAlignment
  have hAction : ‖B‖ ≤
      h3AuditInitialLerayEnergyCoefficient *
        ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 := by
    exact thirdFullPhysical_outerIntegratedLeray_norm_le_H3Cost244
      hH3 x s rho hx hs hxs
  exact thirdFullKinetic_positiveH3Action_of_alignment244
    H A B h3AuditInitialLerayEnergyCoefficient
      (∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2)
      h3AuditInitialLerayEnergyCoefficient_nonneg hAction
      (hAlignment hBudget)


/-- The ORIGINAL highpass carrier is bounded by earlier genuine kinetic
energy. There is no frequency-cutoff factor in this ceiling. -/
theorem thirdFullPhysical_outerFrozenHighpass_kineticAnchor_norm_le244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T) (rho : ℝ) :
    ‖thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho‖ ≤
      Real.sqrt (velocityH3Energy0At u b) := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  have hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hbAbs.1 hx.1, hx.2⟩
  have hKinetic : velocityH3Energy0At u x ≤ velocityH3Energy0At u b :=
    (h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3)
      hbAbs hxAbs hx.1.le
  have hIdentity : ‖V‖ ^ 2 = velocityH3Energy0At u x :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 x hxAbs
  have hHigh : ‖thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho‖ ≤
      ‖V‖ := by
    exact thirdFullPhysical_sharpVectorHighpass_norm_le244 rho V
  have hE : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hRoot : Real.sqrt (velocityH3Energy0At u b) ^ 2 =
      velocityH3Energy0At u b := Real.sq_sqrt hE
  have hRootNonneg := Real.sqrt_nonneg (velocityH3Energy0At u b)
  nlinarith only [hKinetic, hIdentity, hHigh, hRoot, hRootNonneg,
    norm_nonneg V,
    norm_nonneg (thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho)]

/-- Fully PHYSICAL window cost: the nonlinear Leray alternative requires
integrated H³² energy with a coefficient fixed by the earlier kinetic
anchor, independent of cutoff and of the selected window's frequency.
No terminal-uniform time modulus is assumed. -/
theorem thirdFullPhysical_outerForcedLeray_kineticAnchoredH3Charge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x eta : ℝ) (hx : x ∈ Set.Ioo b T) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : ℝ, s ∈ Set.Ioo b T → x ≤ s → s - x < delta →
        ∀ rho K epsilon : ℝ, 0 < K →
        epsilon < K *
          (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) →
        let H := thirdFullPhysical_outerFrozenHighpassVelocity244 hH3 x rho
        let D := thirdFullPhysical_outerFrozenHighpassDiffusion244 hH3 x rho
        let A := thirdFullPhysical_outerIntegratedHighpassDiffusion244 hH3 x s rho
        let B := thirdFullPhysical_outerIntegratedHighpassLeray244 hH3 x s rho
        K * (2 * (s - x) * (-inner ℝ H D) +
          2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon →
        ‖A - B‖ ^ 2 <
          2 * Real.sqrt (velocityH3Energy0At u b) *
            (h3AuditInitialLerayEnergyCoefficient *
              ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2) := by
  have hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hbAbs.1 hx.1, hx.2⟩
  obtain ⟨delta, hdelta, hNear⟩ :=
    thirdFullPhysical_outerForcedLeray_integratedH3Charge244
      hH3 x eta hxAbs heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hxs hsDelta rho K epsilon hK hForced
  intro H D A B hBudget
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hbAbs.1 hs.1, hs.2⟩
  have hPrice := hNear s hsAbs hxs hsDelta rho K epsilon hK hForced
  change (K * (2 * (s - x) * (-inner ℝ H D) +
      2 * ‖H‖ * ((s - x) * eta)) ≤ epsilon) →
      ‖A - B‖ ^ 2 <
        2 * ‖H‖ * (h3AuditInitialLerayEnergyCoefficient *
          ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2)
    at hPrice
  have hH : ‖H‖ ≤ Real.sqrt (velocityH3Energy0At u b) :=
    thirdFullPhysical_outerFrozenHighpass_kineticAnchor_norm_le244
      hH3 hClass b hb x hx rho
  have hAction : ‖B‖ ≤
      h3AuditInitialLerayEnergyCoefficient *
        ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 :=
    thirdFullPhysical_outerIntegratedLeray_norm_le_H3Cost244
      hH3 x s rho hxAbs hsAbs hxs
  have hM : 0 ≤ h3AuditInitialLerayEnergyCoefficient *
      ∫ r in x..s, ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 :=
    (norm_nonneg B).trans hAction
  have hTwice : 2 * ‖H‖ ≤
      2 * Real.sqrt (velocityH3Energy0At u b) := by
    linarith only [hH]
  have hScaled := mul_le_mul_of_nonneg_right hTwice hM
  exact lt_of_lt_of_le (hPrice hBudget) hScaled

end
end PrimeTensor.FirstMonomialTriad
