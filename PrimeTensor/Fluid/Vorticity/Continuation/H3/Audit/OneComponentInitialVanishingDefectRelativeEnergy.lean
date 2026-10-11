import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialScalarRelativeEnergy

/-!
# Initial physical uniqueness from vanishing relative-energy defects

The preceding initial-time argument closes canonical old/selected overlap if the
scalar relative energy is continuous on `[0,b]` and obeys one exact integral
inequality. In an approximation proof (mollified weak equations, cutoff tests,
pressure-defect removal), the natural statement often carries an error `δ n`
which tends to zero as the approximation index tends to infinity.

This file removes the need to assume the exact inequality at the PDE interface:
if one **fixed** comparison coefficient `K` works for all indices and the
real-valued defect tends to zero, the exact inequality follows by order
closure. The scalar Gronwall theorem then closes physical L² equality,
compact weak-test equality, the initial H³ overlap and the conditional
full-time transverse homogeneous 3/2-Sobolev conclusion.

Crucially, the uniform-in-n inequality and the vanishing-defect limit are
substantive PDE obligations. They are not deduced here from open-time
Navier--Stokes admissibility. Nor is continuity of the scalar relative
energy at the artificially zero-valued endpoint. The terminal vorticity
strong-H³ endpoint remains a separate assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- An approximately valid scalar integral inequality, with one coefficient
independent of the approximation index and with defects tending to zero,
implies the exact inequality. No continuity or integrability of `e` is used
in this order-theoretic step. -/
theorem h3Audit_initialRelativeEnergy_exact_of_vanishingDefects
    (e : ℝ → ℝ) (b K : ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (hApprox : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ (K * ∫ s in (0 : ℝ)..t, e s) + δ n) :
    ∀ t ∈ Set.Icc (0 : ℝ) b,
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ :=
    (hδ.eventually (Iio_mem_nhds hε)).exists
  let I : ℝ := K * ∫ s in (0 : ℝ)..t, e s
  change e t ≤ I + ε
  have hBound : e t ≤ I + δ n := hApprox n t ht
  calc
    e t ≤ I + δ n := hBound
    _ ≤ I + ε := add_le_add_right hn.le I

/-- Continuous nonnegative scalar energy obeying a uniformly controlled
family of approximate inequalities must vanish everywhere on `[0,b]`. -/
theorem h3Audit_initialScalarEnergy_integralGronwall_of_vanishingDefects
    (e : ℝ → ℝ) (b K : ℝ) (δ : ℕ → ℝ)
    (hb : 0 < b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heCont : ContinuousOn e (Set.Icc (0 : ℝ) b))
    (hδ : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (hApprox : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ (K * ∫ s in (0 : ℝ)..t, e s) + δ n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  exact h3Audit_initialScalarEnergy_integralGronwall e b K hb
    heNonneg heCont
    (h3Audit_initialRelativeEnergy_exact_of_vanishingDefects
      e b K δ hδ hApprox) t ht

/-- PDE-facing initial physical comparison data formulated using a sequence
of approximate relative-energy estimates. The same `K` must work for every
approximation level; only the additive defect is allowed to vary. -/
def H3AuditInitialCanonicalVanishingDefectRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (K : ℝ) (δ : ℕ → ℝ),
      Tendsto δ atTop (𝓝 (0 : ℝ)) ∧
      ContinuousOn
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (Set.Icc (0 : ℝ) b) ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) b →
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
        (K * ∫ s in (0 : ℝ)..t,
          ‖h3AuditInitialCanonicalPhysicalDifference
            hH3 hFourier0 A hA hU₀ s‖ ^ 2) + δ n

/-- Remove all approximation errors from the PDE-facing scalar energy bound;
this discharges the exact integral inequality without postulating it. -/
theorem h3Audit_initialVanishingDefect_implies_scalarRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVanishingDefectRelativeEnergyData hH3) :
    H3AuditInitialCanonicalScalarRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, δ, hδ, hScalar, hApprox⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, ?_⟩
  exact h3Audit_initialRelativeEnergy_exact_of_vanishingDefects
    (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ t‖ ^ 2)
    b K δ hδ hApprox

/-- Exact comparison implies an approximate comparison with identically
zero defect, so the vanishing-defect contract adds no analytic assumption
beyond the preceding scalar relative-energy contract. -/
theorem h3Audit_initialScalarRelativeEnergy_implies_vanishingDefectData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalScalarRelativeEnergyData hH3) :
    H3AuditInitialCanonicalVanishingDefectRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, hEnergy⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, (fun _ : ℕ => (0 : ℝ)),
    tendsto_const_nhds, hScalar, ?_⟩
  intro n t ht
  simpa using hEnergy t ht

/-- Vanishing relative-energy defects force equality against every compact
physical L² test, and thus the actual canonical initial weighted-H³ overlap. -/
theorem h3Audit_initialVanishingDefect_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVanishingDefectRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_compactWeakComparisonData
    hH3
    (h3Audit_initialVanishingDefect_implies_scalarRelativeEnergyData
      hH3 hData)

/-- Physical initial L² right trace and H³ energy upper continuity from
vanishing-defect physical uniqueness and decoder injectivity. -/
theorem h3Audit_initialVanishingDefect_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVanishingDefectRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialVanishingDefect_implies_scalarRelativeEnergyData
      hH3 hData)

/-- The terminal-side full-time estimate is still conditional on the
independent strong-H³ endpoint for one actual physical vorticity component. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialVanishingDefect
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalVanishingDefectRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarRelativeEnergy
    hH3 hClass i hPhysical
    (h3Audit_initialVanishingDefect_implies_scalarRelativeEnergyData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
