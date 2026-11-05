import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalFiniteBandPhysicalLowpass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertGlobalFTC
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualPhysicalLowpassHighpassEscape
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-!
# Actual finite-band H³ Cauchy from projected source L¹ and physical FTC

The low-pass projected PHYSICAL momentum source is already Bochner L¹ up to
T, regardless of whether the full source is integrable. A bounded
real-linear map transports the physical FTC to each Fourier low band.
The bounded Sobolev weight on that band then gives the weighted H³ Cauchy
modulus. This removes the full kinetic Cauchy premise of the previous gate.

The one remaining temporal hypothesis below is the established explicit
`H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous`, which
the existing global Hilbert-FTC theorem uses. It is NOT claimed to follow
from H³ path admissibility alone. If that temporal joint hypothesis is
later discharged, the fixed-band Cauchy conclusion becomes unconditional
within the original path assumptions.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalLowBandBochnerFTC244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A genuinely endpoint-integrable Bochner source makes every trajectory
with that exact increment formula Cauchy at the terminal time. No a priori
bound on the derivative or endpoint value is required. -/
theorem thirdFullBochnerTerminalCauchy_of_integrableIncrements244
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F G : ℝ → E) (b T : ℝ) (hb : b < T)
    (hG : IntervalIntegrable G volume b T)
    (hInc : ∀ s t : ℝ, s ∈ Set.Ioo b T → t ∈ Set.Ioo b T →
      F t - F s = ∫ r in s..t, G r) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ, s ∈ Set.Ioo b T → t ∈ Set.Ioo b T →
        T - s < δ → T - t < δ → ‖F s - F t‖ < ε := by
  let P : ℝ → E := fun z => ∫ r in b..z, G r
  have hP : ContinuousOn P (Set.Icc b T) := by
    have hc := intervalIntegral.continuousOn_primitive_interval' hG Set.left_mem_uIcc
    simpa only [P, Set.uIcc_of_le hb.le] using hc
  have hAt : ContinuousWithinAt P (Set.Icc b T) T :=
    hP T ⟨hb.le, le_rfl⟩
  intro ε hε
  have hHalf : 0 < ε / 2 := by linarith
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.continuousWithinAt_iff.mp hAt) (ε / 2) hHalf
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht hsNear htNear
  have hsIcc : s ∈ Set.Icc b T := ⟨hs.1.le, hs.2.le⟩
  have htIcc : t ∈ Set.Icc b T := ⟨ht.1.le, ht.2.le⟩
  have hsDist : dist s T < δ := by
    simpa only [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hs.2.le), neg_sub] using hsNear
  have htDist : dist t T < δ := by
    simpa only [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr ht.2.le), neg_sub] using htNear
  have hsSmall : ‖P s - P T‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hNear hsIcc hsDist
  have htSmall : ‖P t - P T‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hNear htIcc htDist
  have hLocal (z : ℝ) (hz : z ∈ Set.Ioo b T) :
      IntervalIntegrable G volume b z := by
    apply hG.mono_set
    rw [Set.uIcc_of_le hz.1.le, Set.uIcc_of_le hb.le]
    exact Set.Icc_subset_Icc le_rfl hz.2.le
  have hInt : (∫ r in s..t, G r) = P t - P s := by
    exact (intervalIntegral.integral_interval_sub_left
      (hLocal t ht) (hLocal s hs)).symm
  have hTriangle : ‖P t - P s‖ ≤ ‖P t - P T‖ + ‖P s - P T‖ := by
    calc
      ‖P t - P s‖ = ‖(P t - P T) + (P T - P s)‖ := by
        congr 1
        abel
      _ ≤ ‖P t - P T‖ + ‖P T - P s‖ := norm_add_le _ _
      _ = ‖P t - P T‖ + ‖P s - P T‖ := by
        rw [norm_sub_rev (P T) (P s)]
  have hBound : ‖F t - F s‖ < ε := by
    calc
      ‖F t - F s‖ = ‖∫ r in s..t, G r‖ := by rw [hInc s t hs ht]
      _ = ‖P t - P s‖ := by rw [hInt]
      _ ≤ ‖P t - P T‖ + ‖P s - P T‖ := hTriangle
      _ < ε := by linarith only [htSmall, hsSmall]
  calc
    ‖F s - F t‖ = ‖F t - F s‖ := norm_sub_rev _ _
    _ < ε := hBound

/-- Exact source integrability on the natural low band of the physical
Fourier-velocity CLM. This uses the previously established lowpass source
Bochner-L¹ theorem, followed by real Plancherel. -/
theorem thirdFullActualLowBandFourierSource_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (j : Fin 3) :
    IntervalIntegrable (fun r : ℝ =>
      thirdFullPhysicalLowBandFourierCLM244 R j
        (h3PathActualProjectedMomentumSource244 hH3 r)) volume b T := by
  let ρ : ℝ := (R : ℝ) + 1
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  let B : ℝ → H3ScalarL2 := fun r =>
    h3CriticalPhysicalSharpLowCutoffApply ρ
      ((h3PathActualProjectedMomentumSource244 hH3 r).ofLp j)
  have hB : IntervalIntegrable B volume b T :=
    h3Critical_actualPhysicalSharpLowCutoff_source_intervalIntegrable
      hH3 hClass b hb ρ hρ j
  have hBOn : IntegrableOn B (Set.Ioo b T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1 hB
  have hFourierOn : IntegrableOn
      (fun r : ℝ => h3ScalarFourierL2RealContinuousLinearMap (B r))
      (Set.Ioo b T) volume := by
    exact h3ScalarFourierL2RealContinuousLinearMap.integrableOn_comp hBOn
  have hFourier : IntervalIntegrable (fun r : ℝ => h3ScalarFourierL2 (B r))
      volume b T := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2
    exact hFourierOn
  have hEq : (fun r : ℝ =>
      thirdFullPhysicalLowBandFourierCLM244 R j
        (h3PathActualProjectedMomentumSource244 hH3 r)) =
    (fun r : ℝ => h3ScalarFourierL2 (B r)) := by
    funext r
    rw [thirdFullPhysicalLowBandFourierCLM_apply244]
    exact (h3Critical_scalarFourier_physicalSharpLowCutoff_eq ρ _).symm
  rw [hEq]
  exact hFourier

/-- Integrability simultaneously in ALL THREE physical Fourier channels.
The output is a genuine finite-product Bochner-integrable vector state. -/
theorem thirdFullActualLowBandFourierVectorSource_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (R : ℕ) :
    IntervalIntegrable (fun r : ℝ =>
      thirdFullPhysicalLowBandFourierVectorCLM244 R
        (h3PathActualProjectedMomentumSource244 hH3 r)) volume b T := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).2
  change Integrable (fun r : ℝ =>
    thirdFullPhysicalLowBandFourierVectorCLM244 R
      (h3PathActualProjectedMomentumSource244 hH3 r))
    ((volume : Measure ℝ).restrict (Set.Ioo b T))
  apply (MeasureTheory.integrable_pi_iff).2
  intro j
  change IntegrableOn (fun r : ℝ =>
      thirdFullPhysicalLowBandFourierCLM244 R j
        (h3PathActualProjectedMomentumSource244 hH3 r))
      (Set.Ioo b T) volume
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.2.le).1
    (thirdFullActualLowBandFourierSource_intervalIntegrable244
      hH3 hClass b hb R j)

/-- The existing physical Bochner FTC transports EXACTLY through the bounded
finite-band Fourier map. This is a real theorem under the explicit old-branch
joint temporal-derivative hypothesis, not a postulated spectral FTC. -/
theorem thirdFullActualLowBandFourierVector_strictFTC_of_oldJoint244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (R : ℕ) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    thirdFullPhysicalLowBandFourierVectorCLM244 R
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t) -
      thirdFullPhysicalLowBandFourierVectorCLM244 R
        (h3AuditInitialOldPhysicalHilbertTotal hH3 s) =
    ∫ r in s..t,
      thirdFullPhysicalLowBandFourierVectorCLM244 R
        (h3PathActualProjectedMomentumSource244 hH3 r) := by
  let L := thirdFullPhysicalLowBandFourierVectorCLM244 R
  let X := h3AuditInitialOldPhysicalHilbertTotal hH3
  let G := h3PathActualProjectedMomentumSource244 hH3
  have hG : IntervalIntegrable G volume s t := by
    change IntervalIntegrable (fun r : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLerayTotal hH3 r) volume s t
    exact h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes
      hH3 s t hs ht
  have hFTC := h3Audit_initialOldJoint_implies_physicalHilbertFTC_between_positiveTimes
    hH3 hOldJoint s t hs ht
  change X t - X s = ∫ r in s..t, G r at hFTC
  change L (X t) - L (X s) = ∫ r in s..t, L (G r)
  calc
    L (X t) - L (X s) = L (X t - X s) := (map_sub L _ _).symm
    _ = L (∫ r in s..t, G r) := by rw [hFTC]
    _ = ∫ r in s..t, L (G r) :=
      (L.intervalIntegral_comp_comm hG).symm

/-- HARD ENDPOINT TRANSFER: source Bochner-L¹ on each fixed physical Fourier
ball, plus the explicitly supplied old-branch FTC, produces terminal Cauchy
in every weighted H³ low band. No FULL physical L² terminal Cauchy premise,
no full projected-source L¹ premise, and no higher Fourier moment are used. -/
theorem thirdFullPhysical_terminalLowRadialCauchy_of_oldJoint244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ThirdFullTerminalLowRadialCauchyOn244
      (h3AuditActualSpectralVelocityTotal hH3) b T := by
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  intro R ε hε
  let C : ℝ := thirdFullFiniteBandH3WeightCeiling244 R
  have hC : 0 ≤ C := thirdFullFiniteBandH3WeightCeiling_nonneg244 R
  have hOneC : 0 < 1 + C := by linarith
  have hSmallArg : 0 < ε / (1 + C) := div_pos hε hOneC
  let F_R : ℝ → H3SpectralFinVectorState := fun t =>
    thirdFullPhysicalLowBandFourierVectorCLM244 R (X t)
  let G_R : ℝ → H3SpectralFinVectorState := fun t =>
    thirdFullPhysicalLowBandFourierVectorCLM244 R (G t)
  have hG_R : IntervalIntegrable G_R volume b T :=
    thirdFullActualLowBandFourierVectorSource_intervalIntegrable244
      hH3 hClass b hb R
  have hInc : ∀ s t : ℝ, s ∈ Set.Ioo b T → t ∈ Set.Ioo b T →
      F_R t - F_R s = ∫ r in s..t, G_R r := by
    intro s t hs ht
    have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hs.1), hs.2⟩
    have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 ht.1), ht.2⟩
    exact thirdFullActualLowBandFourierVector_strictFTC_of_oldJoint244
      hH3 hOldJoint R s t hsAbs htAbs
  obtain ⟨δ, hδ, hCauchy⟩ :=
    thirdFullBochnerTerminalCauchy_of_integrableIncrements244
      F_R G_R b T hb.2 hG_R hInc
      (ε / (1 + C)) hSmallArg
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht hsNear htNear
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hs.1), hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 ht.1), ht.2⟩
  have hLow :=
    thirdFullPhysicalStrictTimes_lowRadial_distance_le_lowpassFourier244
      hH3 R s t hsAbs htAbs
  change ‖thirdFullSpectralVelocityLowRadialApply244 R
      (h3AuditActualSpectralVelocityTotal hH3 s) -
      thirdFullSpectralVelocityLowRadialApply244 R
      (h3AuditActualSpectralVelocityTotal hH3 t)‖ ≤
      C * ‖F_R s - F_R t‖ at hLow
  have hSmall := hCauchy s t hs ht hsNear htNear
  have hProduct : C * ‖F_R s - F_R t‖ ≤ C * (ε / (1 + C)) :=
    mul_le_mul_of_nonneg_left hSmall.le hC
  have hStrict : C * (ε / (1 + C)) < ε := by
    calc
      C * (ε / (1 + C)) < (1 + C) * (ε / (1 + C)) :=
        mul_lt_mul_of_pos_right (by linarith) hSmallArg
      _ = ε := by
        rw [mul_comm (1 + C)]
        exact div_mul_cancel₀ ε hOneC.ne'
  exact (hLow.trans hProduct).trans_lt hStrict

/-- The terminal H³ trace criterion now uses the ACTUAL fixed-band PDE
source control (under the explicit temporal joint regularity) and only
requires high-radial endpoint tightness to close the full H³ state. -/
theorem thirdFullPhysical_terminalH3Trace_of_oldJoint_and_tight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hTight : ThirdFullTerminalUniformHighRadialTightOn244
      (h3AuditActualSpectralVelocityTotal hH3) b T) :
    ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L) := by
  exact thirdFullPhysicalTerminalSpectralTrace_of_lowAndTight244
    hH3 hb.2
    (thirdFullPhysical_terminalLowRadialCauchy_of_oldJoint244
      hH3 hClass hOldJoint b hb) hTight

/-- Under old-branch physical FTC, the absence of a terminal H³ trace
forces a SINGLE positive weighted high-frequency threshold beyond every
fixed frequency cutoff at cofinal times. The source lowpass Cauchy control
is now proved rather than separately hypothesized. -/
theorem thirdFullPhysical_noH3Trace_cofinalHighRadialEscape_of_oldJoint244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (R : ℕ) (δ : ℝ), 0 < δ →
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ T - t < δ ∧
          ε ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ := by
  exact thirdFullPhysical_noH3Trace_cofinalHighRadialEscape244
    hH3 hb.2
    (thirdFullPhysical_terminalLowRadialCauchy_of_oldJoint244
      hH3 hClass hOldJoint b hb) hNoTrace

end
end PrimeTensor.FirstMonomialTriad
