import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusQuantitativeModulus244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionOldPressureGlobalJoint244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceH3EnergyEscape244
import Mathlib.Tactic

/-!
# Genuine projected-PDE source bound on physical L² momentum increments

The quantitative finite-annulus theorem controls a bounded Fourier quadratic
in the strong H³ spectral state. The physical projected source, on the other
hand, is an L²-valued time derivative of the OLD physical momentum.
These Hilbert spaces are not interchangeable.

This file proves a missing PDE-facing quantitative ingredient directly:
  ‖u(t) - u(s)‖_{physical L²} ≤ C (t-s),
where C is a uniform L² ceiling for the actual projected PDE source.
Its H³-energy version has C=(3+C_Leray) sup E3.

The estimate is unconditional relative to LoggedPreterminalH3PathAdmissible.
The *next* step requires a genuine Plancherel and sharp Fourier-cutoff
transfer from physical L² increments to finite-band spectral increments,
NOT an unbounded H³ estimate from physical L².
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A ceiling on the actual projected physical PDE source gives a two-time
Lipschitz estimate in the actual physical L² Hilbert space. The derivative
identification comes from the old-pressure distributional FTC chain, not from
an auxiliary mild representative. -/
theorem h3Path_physicalMomentum_increment_le_projectedPDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
      h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤ C * (t - s) := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hDerivative : ∀ r ∈ Set.Icc s t,
      HasDerivWithinAt U (F r) (Set.Icc s t) r := by
    intro r hr
    have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    exact (h3Path_physicalHilbertHasDerivAt_fromH3Admissible244
      hH3 hrAbs).hasDerivWithinAt
  have hSourceBound : ∀ r ∈ Set.Ico s t, ‖F r‖ ≤ C := by
    intro r hr
    exact hCeil r ⟨hr.1, hr.2.le⟩
  have hResult : ‖U t - U s‖ ≤ C * (t - s) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hDerivative hSourceBound t ⟨hst, le_rfl⟩
  exact hResult

/-- A scalar H³ energy ceiling makes the physical momentum Lipschitz, with
its explicit Fourier-Leray coefficient inherited from the actual PDE source. -/
theorem h3Path_physicalMomentum_increment_le_H3EnergyCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t E : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hE : ∀ r : ℝ, r ∈ Set.Icc s t →
      velocityH3EnergyAt u r ≤ E) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
      h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤
      ((3 + h3AuditInitialLerayEnergyCoefficient) * E) * (t - s) := by
  have hCoefficient : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [hCoeff]
  apply h3Path_physicalMomentum_increment_le_projectedPDECeiling244
    hH3 s t ((3 + h3AuditInitialLerayEnergyCoefficient) * E) hs ht hst
  intro r hr
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  exact (h3Path_physicalProjectedSource_norm_le_H3Energy244
    hH3 r hrAbs).trans
      (mul_le_mul_of_nonneg_left (hE r hr) hCoefficient)

/-- The admitted physical path has a single honest physical L² momentum
Lipschitz constant on every compact interval inside (0,T), obtained from
compactness and continuity of its projected PDE source. -/
theorem h3Path_physicalMomentum_uniformLipschitzOnStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤ C * (t - s) := by
  obtain ⟨C, hC, hBound⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
      hH3 ha hab hb
  refine ⟨C, hC, ?_⟩
  intro s t hs ht hst
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  apply h3Path_physicalMomentum_increment_le_projectedPDECeiling244
    hH3 s t C hsAbs htAbs hst
  intro r hr
  exact hBound r ⟨le_trans hs.1 hr.1, le_trans hr.2 ht.2⟩

/-- The same quantitative control holds simultaneously against all physical
L² probes, including compact solenoidal Schwartz tests, with the exact
operator norm of the test pairing. -/
theorem h3Path_physicalMomentum_weakProbeIncrement_le_sourceCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (ψ : H3PhysicalRealFinVectorL2Hilbert) :
    |inner ℝ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3AuditInitialOldPhysicalHilbertTotal hH3 s) ψ| ≤
      (C * (t - s)) * ‖ψ‖ := by
  have hNorm := h3Path_physicalMomentum_increment_le_projectedPDECeiling244
    hH3 s t C hs ht hst hCeil
  calc
    |inner ℝ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3AuditInitialOldPhysicalHilbertTotal hH3 s) ψ| ≤
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ * ‖ψ‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (C * (t - s)) * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right hNorm (norm_nonneg ψ)

end
end PrimeTensor.FirstMonomialTriad
