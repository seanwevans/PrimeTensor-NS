import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalKineticLowBandCauchy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassFourierMassEscape
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Reduction
import Mathlib.Tactic

/-!
# Exact sharp finite-band physical/weighted Fourier transfer

The preceding bound used the FULL unweighted kinetic difference, hence it
required full physical L² Cauchy. This sharper result retains the fixed
Fourier projection on the right. The weight W₃ is bounded on the fixed ball,
and the actual physical Fourier projection has an exact real/Hermitian
round-trip in the existing critical-energy branch.

  ‖Q_R(U-V)‖_{H³} ≤ C_R ‖P_R(û-ṽ)‖_{L²}.

This is the correct bridge for deriving low-H³ terminal Cauchy from the
Bochner-L¹ LOWPASS source, without requiring the entire physical momentum
source to be L¹ in terminal time. There are no new smoothness assumptions.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFiniteBandPhysicalLowpass244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The TRUE finite-band Sobolev inequality: only the corresponding
*projected* raw Fourier amplitude is charged, not the full kinetic mass. -/
theorem thirdFullSpectralScalarLowRadial_norm_le_rawLowpass244
    (R : ℕ) (G : H3SpectralScalarState) :
    ‖G - thirdFullSpectralHighRadialApply244 R G‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
          (h3SpectralScalarRawFourierL2 G)‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    thirdFullSpectralScalarLowRadial_ae244 R G,
    h3SpectralScalarRawFourierL2_ae G,
    h3SpectralScalarRawFourier_reweight_ae G,
    h3Critical_fourierSharpLowCutoffApply_ae ((R : ℝ) + 1)
      (h3SpectralScalarRawFourierL2 G)
  ] with ξ hLow hRaw hWeight hCut
  rw [hLow]
  change ‖(h3TerminalRadialFrequencyBelow ((R : ℝ) + 1)).indicator G ξ‖ ≤
    thirdFullFiniteBandH3WeightCeiling244 R *
      ‖(h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
        (h3SpectralScalarRawFourierL2 G) : V3 → ℂ) ξ‖
  -- The CLM is definitionally the raw indicator application; expose
  -- that application before using its a.e. representative.
  change ‖(h3TerminalRadialFrequencyBelow ((R : ℝ) + 1)).indicator G ξ‖ ≤
    thirdFullFiniteBandH3WeightCeiling244 R *
      ‖(h3CriticalFourierSharpLowCutoffApply ((R : ℝ) + 1)
          (h3SpectralScalarRawFourierL2 G) : V3 → ℂ) ξ‖
  rw [hCut]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ((R : ℝ) + 1)
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, hRaw, ← hWeight,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h3SobolevFrequencyWeight_pos ξ).le]
    exact mul_le_mul_of_nonneg_right
      (thirdFullFiniteBandH3Weight_le244 R ξ hξ) (norm_nonneg _)
  · simp only [Set.indicator_of_notMem hξ, norm_zero, mul_zero, le_refl]

/-- Native three-component low-H³ difference bounded by the SAME sharp
lowpass of the raw Fourier difference. -/
theorem thirdFullSpectralVelocityLowRadial_distance_le_rawLowpass244
    (R : ℕ) (U V : H3SpectralVelocityState) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R U -
        thirdFullSpectralVelocityLowRadialApply244 R V‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖(fun j : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
            (h3SpectralScalarRawFourierL2 (U j))) -
          (fun j : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
            (h3SpectralScalarRawFourierL2 (V j)))‖ := by
  have hLowSub :
      thirdFullSpectralVelocityLowRadialApply244 R U -
        thirdFullSpectralVelocityLowRadialApply244 R V =
      thirdFullSpectralVelocityLowRadialApply244 R (U - V) := by
    have hHigh := thirdFullSpectralVelocityHighRadialApply_add244 R (U - V) V
    rw [sub_add_cancel] at hHigh
    unfold thirdFullSpectralVelocityLowRadialApply244
    rw [hHigh]
    abel
  rw [hLowSub]
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)
      (norm_nonneg _))).2
  intro j
  change ‖(U - V) j - thirdFullSpectralHighRadialApply244 R ((U - V) j)‖ ≤ _
  calc
    ‖(U - V) j - thirdFullSpectralHighRadialApply244 R ((U - V) j)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
          (h3SpectralScalarRawFourierL2 ((U - V) j))‖ :=
      thirdFullSpectralScalarLowRadial_norm_le_rawLowpass244 R ((U - V) j)
    _ = thirdFullFiniteBandH3WeightCeiling244 R *
        ‖h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
          (h3SpectralScalarRawFourierL2 (U j)) -
          h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
          (h3SpectralScalarRawFourierL2 (V j))‖ := by
      simp only [Pi.sub_apply, h3SpectralScalarRawFourierL2_sub, map_sub]
    _ ≤ thirdFullFiniteBandH3WeightCeiling244 R *
        ‖(fun k : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
            (h3SpectralScalarRawFourierL2 (U k))) -
          (fun k : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
            (h3SpectralScalarRawFourierL2 (V k)))‖ := by
      apply mul_le_mul_of_nonneg_left _
        (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)
      simpa only [Pi.sub_apply] using
        (h3SpectralVelocity_coordinate_norm_le
          ((fun k : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
              (h3SpectralScalarRawFourierL2 (U k))) -
            (fun k : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
              (h3SpectralScalarRawFourierL2 (V k)))) j)

/-- A genuinely bounded real-linear physical-to-Fourier lowpass. Each
coordinate is the exact physical Plancherel transform followed by the
Hermitian-compatible sharp radial indicator. -/
noncomputable def thirdFullPhysicalLowBandFourierCLM244
    (R : ℕ) (j : Fin 3) :
    H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3FourierComplexL2 :=
  ((h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)).restrictScalars ℝ).comp
    ((ContinuousLinearMap.proj j :
        H3SpectralFinVectorState →L[ℝ] H3FourierComplexL2).comp
      h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap)

@[simp] theorem thirdFullPhysicalLowBandFourierCLM_apply244
    (R : ℕ) (j : Fin 3) (X : H3PhysicalRealFinVectorL2Hilbert) :
    thirdFullPhysicalLowBandFourierCLM244 R j X =
      h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
        (h3ScalarFourierL2 (X.ofLp j)) := by
  rfl

/-- The three sharp finite-band Fourier projections form one bounded
real-linear map on the complete physical kinetic Hilbert space. -/
noncomputable def thirdFullPhysicalLowBandFourierVectorCLM244 (R : ℕ) :
    H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralFinVectorState :=
  ContinuousLinearMap.pi
    (fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j)

@[simp] theorem thirdFullPhysicalLowBandFourierVectorCLM_apply244
    (R : ℕ) (X : H3PhysicalRealFinVectorL2Hilbert) (j : Fin 3) :
    thirdFullPhysicalLowBandFourierVectorCLM244 R X j =
      thirdFullPhysicalLowBandFourierCLM244 R j X := rfl

/-- The first genuinely physical cutoff bridge. No full kinetic norm is
charged: only the three already localized physical Fourier coordinates. -/
theorem thirdFullPhysicalStrictTimes_lowRadial_distance_le_lowpassFourier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖(fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j
            (h3AuditInitialOldPhysicalHilbertTotal hH3 s)) -
          (fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ := by
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let X : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hEq (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) T) (j : Fin 3) :
      h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
        (h3SpectralScalarRawFourierL2 (U z j)) =
      thirdFullPhysicalLowBandFourierCLM244 R j (X z) := by
    rw [thirdFullPhysicalLowBandFourierCLM_apply244]
    change h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
      (h3SpectralScalarRawFourierL2
        (h3AuditActualSpectralVelocityTotal hH3 z j)) = _
    rw [h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2 hH3 j z hz]
    rfl
  have hLow := thirdFullSpectralVelocityLowRadial_distance_le_rawLowpass244
    R (U s) (U t)
  calc
    ‖thirdFullSpectralVelocityLowRadialApply244 R (U s) -
        thirdFullSpectralVelocityLowRadialApply244 R (U t)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ‖(fun j : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
            (h3SpectralScalarRawFourierL2 (U s j))) -
          (fun j : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
            (h3SpectralScalarRawFourierL2 (U t j)))‖ := hLow
    _ = thirdFullFiniteBandH3WeightCeiling244 R *
        ‖(fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j (X s)) -
          (fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j (X t))‖ := by
      have hAtS :
          (fun j : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
              (h3SpectralScalarRawFourierL2 (U s j))) =
          (fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j (X s)) := by
        funext j
        exact hEq s hs j
      have hAtT :
          (fun j : Fin 3 => h3CriticalFourierSharpLowCutoffCLM ((R : ℝ) + 1)
              (h3SpectralScalarRawFourierL2 (U t j))) =
          (fun j : Fin 3 => thirdFullPhysicalLowBandFourierCLM244 R j (X t)) := by
        funext j
        exact hEq t ht j
      rw [hAtS, hAtT]

end
end PrimeTensor.FirstMonomialTriad
