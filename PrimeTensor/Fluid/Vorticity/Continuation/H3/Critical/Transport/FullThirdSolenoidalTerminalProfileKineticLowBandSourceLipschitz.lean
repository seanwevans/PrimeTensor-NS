import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryAnnularClockRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalUnconditionalTerminalLowBandFTC
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualPhysicalLowpassHighpassEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLerayPhysicalL2Bound
import Mathlib.Tactic

/-!
# Kinetic-only finite-band projected source and physical H³ time modulus

The preceding secondary annular PDE clock requires attained full-H³ spectral
and projected-momentum source maxima in its variation coefficient. At any
FIXED physical frequency cutoff, the actual Navier--Stokes projected source
has a much stronger estimate: its physical sharp lowpass is uniformly bounded
on every anchored terminal tail by kinetic energy alone.

This is assembled from the genuine physical Fourier Laplacian estimate and
the full quadratic Leray convolution Bernstein estimate, with Plancherel and
the exact sharp physical cutoff/source identity. Transporting that bound
through the already proved unconditional physical Hilbert FTC gives a
fixed-band weighted H³ Lipschitz time modulus. No full-H³ state ceiling,
full projected-source bound, extra PDE axiom, or uniform moving cutoff is used.

The frequency dependence is explicit but not yet optimized. The actual
terminal cofinal annulus has a MOVING outer cutoff, so this fixed-band
estimate alone does not close continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

-- Use the canonical product Lebesgue measure on the physical three-dimensional
-- Fourier frequency space.  The imported kinetic bound employs this same
-- local pi-measure construction; it is not inferred automatically here.
noncomputable local instance axisFintypeKineticLowBand244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceKineticLowBand244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The kinetic-only pointwise norm ceiling for the *actual sharp Fourier
lowpass* of the physical projected Navier--Stokes momentum source. -/
noncomputable def thirdFullPhysicalKineticLowBandSourceCeiling244
    (ρ E : ℝ) : ℝ :=
  ρ ^ 2 * Real.sqrt E +
    Real.sqrt ((volume : Measure H3FourierPoint3).real
      (h3TerminalRadialFrequencyBelow ρ) * (18 * (ρ * E)) ^ 2)

theorem thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244
    (ρ E : ℝ) :
    0 ≤ thirdFullPhysicalKineticLowBandSourceCeiling244 ρ E := by
  unfold thirdFullPhysicalKineticLowBandSourceCeiling244
  exact add_nonneg
    (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- A genuinely uniform pointwise Bernstein estimate for the low-frequency
projected PHYSICAL momentum source, with no full H³ amplitude dependence.
The two contributions are the kinetic Laplacian and nonlinear Leray forcing. -/
theorem thirdFullPhysical_actualLowBandSource_kineticCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (i : Fin 3) :
    ‖h3CriticalPhysicalSharpLowCutoffApply ρ
      ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i)‖ ≤
      thirdFullPhysicalKineticLowBandSourceCeiling244
        ρ (velocityH3Energy0At u b) := by
  let E : ℝ := velocityH3Energy0At u b
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let L : H3ScalarL2 := h3CriticalLowRadialLaplacianPhysicalL2 ρ (U i)
  let N : H3ScalarL2 := h3CriticalLowRadialLerayPhysicalL2 ρ U i
  let C : ℝ := (volume : Measure H3FourierPoint3).real
    (h3TerminalRadialFrequencyBelow ρ) * (18 * (ρ * E)) ^ 2
  have hL : ‖L‖ ≤ ρ ^ 2 * Real.sqrt E := by
    exact h3Critical_actual_lowRadialLaplacianPhysicalL2_norm_le_kineticAnchor
      hH3 hClass b hb ρ hρ t ht i
  have hNSq : ‖N‖ ^ 2 ≤ C := by
    exact h3Critical_actual_lowRadial_lerayPhysicalL2_sq_le_kineticAnchor
      hH3 hClass b hb ρ hρ t ht i
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg measureReal_nonneg (sq_nonneg _)
  have hN : ‖N‖ ≤ Real.sqrt C := by
    have hs := Real.sq_sqrt hC
    have hn := Real.sqrt_nonneg C
    nlinarith only [hNSq, hs, hn, norm_nonneg N]
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  have hIdentity :
      h3CriticalPhysicalSharpLowCutoffApply ρ
        ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp i) = L - N := by
    exact h3Critical_actualPhysicalSharpLowCutoff_source_eq hH3 t htAbs ρ i
  rw [hIdentity]
  change ‖L - N‖ ≤ ρ ^ 2 * Real.sqrt E + Real.sqrt C
  exact (norm_sub_le L N).trans (add_le_add hL hN)

/-- Plancherel transports the same kinetic bound into the EXACT Fourier
multiplier applied to the actual real physical projected source. -/
theorem thirdFullPhysical_actualLowBandFourierSource_kineticCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo b T) (i : Fin 3) :
    ‖thirdFullPhysicalLowBandFourierCLM244 R i
      (h3PathActualProjectedMomentumSource244 hH3 t)‖ ≤
      thirdFullPhysicalKineticLowBandSourceCeiling244
        ((R : ℝ) + 1) (velocityH3Energy0At u b) := by
  let ρ : ℝ := (R : ℝ) + 1
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hPhysical := thirdFullPhysical_actualLowBandSource_kineticCeiling244
    hH3 hClass b hb ρ hρ t ht i
  rw [thirdFullPhysicalLowBandFourierCLM_apply244]
  rw [← h3Critical_scalarFourier_physicalSharpLowCutoff_eq]
  rw [norm_h3ScalarFourierL2]
  simpa only [ρ] using hPhysical

/-- A FIXED sharp Fourier low band of the actual physical velocity is
Lipschitz in physical time, at a constant depending ONLY on the fixed
frequency radius and the earlier physical kinetic energy anchor. The exact
Hilbert FTC, not an assumed spectral-time derivative, supplies the increment. -/
theorem thirdFullPhysical_kineticLowBandFourierCoordinateLipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (s t : ℝ) (hs : s ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo b T) (hst : s ≤ t) (i : Fin 3) :
    ‖thirdFullPhysicalLowBandFourierCLM244 R i
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t) -
      thirdFullPhysicalLowBandFourierCLM244 R i
        (h3AuditInitialOldPhysicalHilbertTotal hH3 s)‖ ≤
      thirdFullPhysicalKineticLowBandSourceCeiling244
        ((R : ℝ) + 1) (velocityH3Energy0At u b) * (t - s) := by
  let L := thirdFullPhysicalLowBandFourierCLM244 R i
  let X := h3AuditInitialOldPhysicalHilbertTotal hH3
  let G := h3PathActualProjectedMomentumSource244 hH3
  let C := thirdFullPhysicalKineticLowBandSourceCeiling244
    ((R : ℝ) + 1) (velocityH3Energy0At u b)
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 hs.1), hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  have hFTC : X t - X s = ∫ r in s..t, G r :=
    h3Path_physicalHilbertFTC_betweenPositiveTimes244 hH3 s t hsAbs htAbs
  have hG : IntervalIntegrable G volume s t := by
    change IntervalIntegrable (fun r : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLerayTotal hH3 r) volume s t
    exact h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes
      hH3 s t hsAbs htAbs
  have hPoint (r : ℝ) (hr : r ∈ Set.Ioc s t) : ‖L (G r)‖ ≤ C := by
    have hrTail : r ∈ Set.Ioo b T :=
      ⟨lt_trans hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    exact thirdFullPhysical_actualLowBandFourierSource_kineticCeiling244
      hH3 hClass b hb R r hrTail i
  have hBound : ‖∫ r in s..t, L (G r)‖ ≤ C * |t - s| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    have hrIoc : r ∈ Set.Ioc s t := by
      simpa only [Set.uIoc_of_le hst] using hr
    exact hPoint r hrIoc
  calc
    ‖L (X t) - L (X s)‖ = ‖L (X t - X s)‖ := by rw [map_sub]
    _ = ‖L (∫ r in s..t, G r)‖ := by rw [hFTC]
    _ = ‖∫ r in s..t, L (G r)‖ := by
      rw [← L.intervalIntegral_comp_comm hG]
    _ ≤ C * |t - s| := hBound
    _ = C * (t - s) := by rw [abs_of_nonneg (sub_nonneg.mpr hst)]

/-- The ACTUAL weighted H³ spectral low band inherits the physical kinetic
Lipschitz modulus via the exact finite-band Sobolev multiplier. This removes
both full-H³ and full-source maxima from fixed-frequency temporal control. -/
theorem thirdFullPhysical_kineticLowRadialH3Lipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (s t : ℝ) (hs : s ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo b T) (hst : s ≤ t) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        (thirdFullPhysicalKineticLowBandSourceCeiling244
          ((R : ℝ) + 1) (velocityH3Energy0At u b) * (t - s)) := by
  let X := h3AuditInitialOldPhysicalHilbertTotal hH3
  let C := thirdFullPhysicalKineticLowBandSourceCeiling244
    ((R : ℝ) + 1) (velocityH3Energy0At u b)
  have hC : 0 ≤ C := thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 _ _
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 hs.1), hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  have hVec :
      ‖(fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j (X s)) -
        (fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j (X t))‖ ≤
      C * (t - s) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hd)).2
    intro j
    have hj := thirdFullPhysical_kineticLowBandFourierCoordinateLipschitz244
      hH3 hClass b hb R s t hs ht hst j
    change ‖thirdFullPhysicalLowBandFourierCLM244 R j (X s) -
        thirdFullPhysicalLowBandFourierCLM244 R j (X t)‖ ≤ C * (t - s)
    calc
      _ = ‖thirdFullPhysicalLowBandFourierCLM244 R j (X t) -
        thirdFullPhysicalLowBandFourierCLM244 R j (X s)‖ := norm_sub_rev _ _
      _ ≤ C * (t - s) := hj
  have hPhysical := thirdFullPhysicalStrictTimes_lowRadial_distance_le_lowpassFourier244
    hH3 R s t hsAbs htAbs
  exact hPhysical.trans
    (mul_le_mul_of_nonneg_left hVec
      (thirdFullFiniteBandH3WeightCeiling_nonneg244 R))


/-- The ORIGINAL late secondary state and projected-source observation times
are separated by at most half the remaining horizon. Every fixed weighted
H³ low band therefore has a kinetic-only bound on their actual temporal
drift, independent of both attained full-H³ maxima and moving cutoff J₂.
No new observation time is selected and no terminal H³ ceiling is used. -/
theorem thirdFullPhysical_secondarySelectedTimes_fixedLowBandDrift244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s zState zSource : ℝ) (hs : s ∈ Set.Ioo b T)
    (hzState : zState ∈ Set.Icc s (s + (T - s) / 2))
    (hzSource : zSource ∈ Set.Icc s (s + (T - s) / 2))
    (R : ℕ) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 zState) -
      thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 zSource)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        (thirdFullPhysicalKineticLowBandSourceCeiling244
          ((R : ℝ) + 1) (velocityH3Energy0At u b) * ((T - s) / 2)) := by
  let W : ℝ := thirdFullFiniteBandH3WeightCeiling244 R
  let C : ℝ := thirdFullPhysicalKineticLowBandSourceCeiling244
    ((R : ℝ) + 1) (velocityH3Energy0At u b)
  let U := h3AuditActualSpectralVelocityTotal hH3
  have hW : 0 ≤ W := thirdFullFiniteBandH3WeightCeiling_nonneg244 R
  have hC : 0 ≤ C := thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 _ _
  have hHalfEnd : s + (T - s) / 2 < T := by
    linarith only [hs.2]
  have hState : zState ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hs.1 hzState.1,
      lt_of_le_of_lt hzState.2 hHalfEnd⟩
  have hSource : zSource ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hs.1 hzSource.1,
      lt_of_le_of_lt hzSource.2 hHalfEnd⟩
  rcases le_total zState zSource with hOrder | hOrder
  · have hSpan : zSource - zState ≤ (T - s) / 2 := by
      linarith only [hzState.1, hzSource.2]
    have hBound := thirdFullPhysical_kineticLowRadialH3Lipschitz244
      hH3 hClass b hb R zState zSource hState hSource hOrder
    change ‖thirdFullSpectralVelocityLowRadialApply244 R (U zState) -
        thirdFullSpectralVelocityLowRadialApply244 R (U zSource)‖ ≤
      W * (C * ((T - s) / 2))
    calc
      _ ≤ W * (C * (zSource - zState)) := hBound
      _ ≤ W * (C * ((T - s) / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hSpan hC) hW
  · have hSpan : zState - zSource ≤ (T - s) / 2 := by
      linarith only [hzSource.1, hzState.2]
    have hBound := thirdFullPhysical_kineticLowRadialH3Lipschitz244
      hH3 hClass b hb R zSource zState hSource hState hOrder
    change ‖thirdFullSpectralVelocityLowRadialApply244 R (U zState) -
        thirdFullSpectralVelocityLowRadialApply244 R (U zSource)‖ ≤
      W * (C * ((T - s) / 2))
    calc
      _ = ‖thirdFullSpectralVelocityLowRadialApply244 R (U zSource) -
            thirdFullSpectralVelocityLowRadialApply244 R (U zState)‖ :=
            norm_sub_rev _ _
      _ ≤ W * (C * (zState - zSource)) := hBound
      _ ≤ W * (C * ((T - s) / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hSpan hC) hW

end
end PrimeTensor.FirstMonomialTriad
