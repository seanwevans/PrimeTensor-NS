import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalLowBandBochnerFTC
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopUnconditionalHilbertFTCKinetic244
import Mathlib.Tactic

/-!
# Unconditional terminal low-band H³ Cauchy from the actual physical momentum PDE

The prior low-band Bochner-FTC module carried an old temporal joint-continuity
hypothesis. The separately established global physical Hilbert FTC already
removes this hypothesis, albeit through its own earlier old-pressure/curl
weak-evolution dependency chain. We now transport that *existing unconditional*
physical Hilbert identity through the exact sharp physical Fourier cutoff.

The actual projected source has Bochner-L¹ time integrability on every fixed
low-frequency ball. Together with the physical FTC, it forces a terminal
Cauchy modulus and a strong limit for every fixed weighted H³ spectral band.
No common cutoff toward the endpoint is assumed, and no H³ terminal trace
is asserted in the absence of high-radial tightness.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeUnconditionalTerminalLowBand244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual physical Hilbert FTC commutes with the genuine low-frequency
Fourier cutoff. No separate old temporal-joint-continuity hypothesis occurs. -/
theorem thirdFullActualLowBandFourierVector_strictFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
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
  have hFTC := h3Path_physicalHilbertFTC_betweenPositiveTimes244
    hH3 s t hs ht
  change X t - X s = ∫ r in s..t, G r at hFTC
  change L (X t) - L (X s) = ∫ r in s..t, L (G r)
  calc
    L (X t) - L (X s) = L (X t - X s) := (map_sub L _ _).symm
    _ = L (∫ r in s..t, G r) := by rw [hFTC]
    _ = ∫ r in s..t, L (G r) :=
      (L.intervalIntegral_comp_comm hG).symm

/-- HARD ENDPOINT TRANSFER: the actual physical low-pass projected source
is Bochner-L¹ up to T, and the unconditional physical Hilbert FTC therefore
forces terminal Cauchy control in EVERY fixed weighted H³ low-frequency band.
No kinetic Cauchy or old temporal joint-continuity hypothesis is required. -/
theorem thirdFullPhysical_terminalLowRadialCauchy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
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
    exact thirdFullActualLowBandFourierVector_strictFTC244
      hH3 R s t hsAbs htAbs
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

/-- Every individual fixed H³ Fourier low band has a genuine strong terminal
limit. These limits can depend on the radius; this does NOT imply that the
unprojected full H³ state converges at the terminal time. -/
theorem thirdFullPhysical_terminalEachLowRadialTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (R : ℕ) :
    ∃ L_R : H3SpectralVelocityState,
      Tendsto (fun t : ℝ => thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t))
        (𝓝[<] T) (𝓝 L_R) := by
  have hLow := thirdFullPhysical_terminalLowRadialCauchy244 hH3 hClass b hb
  have hCauchy : ThirdFullTerminalSpectralCauchyOn244
      (fun t : ℝ => thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)) b T := by
    intro ε hε
    exact hLow R ε hε
  exact thirdFullTerminalSpectralTrace_of_Cauchy244
    (fun t : ℝ => thirdFullSpectralVelocityLowRadialApply244 R
      (h3AuditActualSpectralVelocityTotal hH3 t))
    b T hb.2 hCauchy

/-- Once endpoint-uniform high-frequency tightness is available, the actual
preterminal weighted H³ velocity has a strong terminal trace; all low-band
Cauchy obligations have already been proved from the existing Navier-Stokes
Hilbert FTC and low-pass Bochner-L¹ estimates. -/
theorem thirdFullPhysical_terminalH3Trace_of_radialTight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hTight : ThirdFullTerminalUniformHighRadialTightOn244
      (h3AuditActualSpectralVelocityTotal hH3) b T) :
    ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L) :=
  thirdFullPhysicalTerminalSpectralTrace_of_lowAndTight244
    hH3 hb.2
    (thirdFullPhysical_terminalLowRadialCauchy244 hH3 hClass b hb) hTight

/-- Without a separate kinetic trace or temporal-joint-continuity premise,
failure of a strong terminal H³ limit forces a cofinal weighted high-radial
tail of one fixed positive size beyond every radius. -/
theorem thirdFullPhysical_noH3Trace_cofinalHighRadialEscape_automaticLow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (R : ℕ) (δ : ℝ), 0 < δ →
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ T - t < δ ∧
          ε ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ :=
  thirdFullPhysical_noH3Trace_cofinalHighRadialEscape244
    hH3 hb.2
    (thirdFullPhysical_terminalLowRadialCauchy244 hH3 hClass b hb) hNoTrace

end
end PrimeTensor.FirstMonomialTriad
