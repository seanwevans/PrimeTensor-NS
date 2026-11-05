import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalFiniteBandKineticTransfer
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialOldKineticCeilingRelativeEnergy
import Mathlib.Tactic

/-!
# Terminal kinetic Cauchy control transfers to the exact low H³ Fourier bands

The Fourier-side finite-band `W₃` estimate and the existing exact physical
zeroth-order Fourier encoding combine into a real physical theorem. On ANY two
strict preterminal times, the low-frequency difference of the genuine H³
spectral state is bounded by a finite radial constant times the actual
physical kinetic L² difference. Thus kinetic terminal Cauchy implies every
fixed weighted H³ low-band Cauchy property.

This result is not the kinetic trace itself. In particular, Bochner-L¹ of the
low-pass projected momentum source is not sufficient to assert the kinetic
trace without the physical momentum FTC identification. That identification
remains the next PDE task.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalKineticLowBandCauchy244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual full H³ low-frequency Fourier difference is controlled by
ordinary physical kinetic L² distance, with the exact finite-band weight.
The same original old physical velocity and H³ spectral state appear on both
sides. -/
theorem thirdFullPhysicalStrictTimes_lowRadial_distance_le_kinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ ≤
    thirdFullFiniteBandH3WeightCeiling244 R *
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ := by
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hEq (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) T) (j : Fin 3) :
      h3SpectralScalarRawFourierL2 (U z j) =
        h3ScalarFourierL2 ((X z).ofLp j) := by
    change h3SpectralScalarRawFourierL2
        (h3AuditActualSpectralVelocityTotal hH3 z j) = _
    rw [h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2 hH3 j z hz]
    simp only [X, h3AuditInitialOldPhysicalHilbertTotal, PiLp.toLp_apply]
  have hRaw :
      ‖(fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U s j)) -
        (fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U t j))‖ ≤
        ‖X s - X t‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (X s - X t))).2
    intro j
    change ‖h3SpectralScalarRawFourierL2 (U s j) -
        h3SpectralScalarRawFourierL2 (U t j)‖ ≤ ‖X s - X t‖
    rw [hEq s hs j, hEq t ht j]
    calc
      ‖h3ScalarFourierL2 ((X s).ofLp j) -
          h3ScalarFourierL2 ((X t).ofLp j)‖ =
        ‖h3ScalarFourierL2 ((X s).ofLp j - (X t).ofLp j)‖ := by
          rw [h3ScalarFourierL2_sub]
      _ = ‖(X s).ofLp j - (X t).ofLp j‖ :=
        norm_h3ScalarFourierL2 _
      _ = ‖(X s - X t).ofLp j‖ := by rw [PiLp.sub_apply]
      _ ≤ ‖X s - X t‖ := PiLp.norm_apply_le _ j
  have hLow := thirdFullSpectralVelocityLowRadial_distance_le_raw244
    R (U s) (U t)
  calc
    ‖thirdFullSpectralVelocityLowRadialApply244 R (U s) -
      thirdFullSpectralVelocityLowRadialApply244 R (U t)‖ ≤
        thirdFullFiniteBandH3WeightCeiling244 R *
        ‖(fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U s j)) -
          (fun j : Fin 3 => h3SpectralScalarRawFourierL2 (U t j))‖ := hLow
    _ ≤ thirdFullFiniteBandH3WeightCeiling244 R * ‖X s - X t‖ :=
      mul_le_mul_of_nonneg_left hRaw
        (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)

/-- Physical kinetic terminal Cauchy condition for the actual old solution.
A terminal limit gives this condition, but it is not assumed from continuity
on `(0,T)` alone. -/
def ThirdFullPhysicalTerminalKineticCauchyOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) (a : ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ, s ∈ Set.Ioo a T → t ∈ Set.Ioo a T →
        T - s < δ → T - t < δ →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
          h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ < ε

/-- Physical kinetic terminal Cauchy implies fixed-band H³ Cauchy for
EVERY radius, with exactly the native spectral state and natural cutoff. -/
theorem thirdFullPhysical_terminalLowRadialCauchy_of_kineticCauchy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : 0 ≤ a) (haT : a < T)
    (hKinetic : ThirdFullPhysicalTerminalKineticCauchyOn244 hH3 a) :
    ThirdFullTerminalLowRadialCauchyOn244
      (h3AuditActualSpectralVelocityTotal hH3) a T := by
  intro R ε hε
  let C : ℝ := thirdFullFiniteBandH3WeightCeiling244 R
  have hC : 0 ≤ C := thirdFullFiniteBandH3WeightCeiling_nonneg244 R
  have hOneC : 0 < 1 + C := by linarith
  have hSmallArg : 0 < ε / (1 + C) := div_pos hε hOneC
  obtain ⟨δ, hδ, hSmall⟩ := hKinetic (ε / (1 + C)) hSmallArg
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht hsNear htNear
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_le_of_lt ha hs.1, hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_le_of_lt ha ht.1, ht.2⟩
  have hLow := thirdFullPhysicalStrictTimes_lowRadial_distance_le_kinetic244
    hH3 R s t hsAbs htAbs
  have hKinSmall := hSmall s t hs ht hsNear htNear
  have hProduct : C *
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤
      C * (ε / (1 + C)) :=
    mul_le_mul_of_nonneg_left hKinSmall.le hC
  have hStrict : C * (ε / (1 + C)) < ε := by
    calc
      C * (ε / (1 + C)) <
          (1 + C) * (ε / (1 + C)) :=
        mul_lt_mul_of_pos_right (by linarith) hSmallArg
      _ = ε := by
        rw [mul_comm (1 + C)]
        exact div_mul_cancel₀ ε hOneC.ne'
  exact (hLow.trans hProduct).trans_lt hStrict

/-- The kinetic Cauchy condition removes the low-frequency premise from the
terminal H³ trace criterion. High-frequency tightness remains necessary. -/
theorem thirdFullPhysical_terminalH3Trace_of_kineticCauchy_and_tight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : 0 ≤ a) (haT : a < T)
    (hKinetic : ThirdFullPhysicalTerminalKineticCauchyOn244 hH3 a)
    (hTight : ThirdFullTerminalUniformHighRadialTightOn244
      (h3AuditActualSpectralVelocityTotal hH3) a T) :
    ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L) := by
  exact thirdFullPhysicalTerminalSpectralTrace_of_lowAndTight244
    hH3 haT
    (thirdFullPhysical_terminalLowRadialCauchy_of_kineticCauchy244
      hH3 ha haT hKinetic) hTight

/-- Under kinetic Cauchy, any failure of terminal H³ convergence forces
cofinal high-frequency escape beyond every fixed Fourier cutoff. -/
theorem thirdFullPhysical_noH3Trace_cofinalHighRadialEscape_of_kineticCauchy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : 0 ≤ a) (haT : a < T)
    (hKinetic : ThirdFullPhysicalTerminalKineticCauchyOn244 hH3 a)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (R : ℕ) (δ : ℝ), 0 < δ →
        ∃ t : ℝ, t ∈ Set.Ioo a T ∧ T - t < δ ∧
          ε ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ := by
  exact thirdFullPhysical_noH3Trace_cofinalHighRadialEscape244
    hH3 haT
    (thirdFullPhysical_terminalLowRadialCauchy_of_kineticCauchy244
      hH3 ha haT hKinetic) hNoTrace

end
end PrimeTensor.FirstMonomialTriad
