import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialDiffusionLerayProjectedRHS
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Initial physical projected RHS controlled by the actual H³ energy mass

The previous initial diffusion/Leray comparison required **two** independent
`L¹_t L²_x` source assumptions. This module reduces those source assumptions
to a single `L¹_t` bound for the actual scalar H³ energy, coupled to explicit
pointwise physical RHS estimates and a.e. measurability of the two physical
Hilbert-valued source paths.

For nonnegative coefficients `cD`, `cN`, the intended PDE estimates are

  ‖D(t)‖ ≤ cD * velocityH3EnergyAt u t,
  ‖N(t)‖ ≤ cN * velocityH3EnergyAt u t.

Domination yields both Bochner source integrability statements, and

  ∫₀ᵇ ‖D(t) - N(t)‖ dt ≤
    (cD + cN) * ∫₀ᵇ velocityH3EnergyAt u t dt.

This is a genuine change of integrability hypotheses, NOT an unconditional
initial-bound theorem. In particular `LoggedPreterminalH3PathAdmissible` does
not imply `L¹(0,b)` control of the H³ energy, nor the two pointwise physical
projected-RHS estimates. The positive-time scalar momentum derivative and
the vanishing old/selected residual remain distinct inputs. Nothing is
assumed or concluded about the independent terminal actual-vorticity H³
endpoint except where explicitly stated.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A scalar `L¹` majorant and a.e.-measurability produce Bochner
integrability of a physical Hilbert source. The norm bound is imposed on the
initial *closed* interval, while integrability is measured on `(0,b]`.
No source integrability is assumed. -/
theorem h3Audit_initialEnergyMajorant_source_intervalIntegrable
    (E : ℝ → ℝ)
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b c : ℝ) (hb : 0 ≤ b)
    (hE : IntervalIntegrable E volume 0 b)
    (hFMeas : AEStronglyMeasurable F
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)))
    (hBound : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      ‖F s‖ ≤ c * E s) :
    IntervalIntegrable F volume 0 b := by
  have hMajor :
      IntegrableOn (fun s : ℝ => c * E s)
        (Set.Ioc (0 : ℝ) b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1
      (hE.const_mul c)
  have hDom :
      ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)),
        ‖F s‖ ≤ c * E s :=
    ae_restrict_of_forall_mem measurableSet_Ioc (by
      intro s hs
      exact hBound s ⟨hs.1.le, hs.2⟩)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2
  exact Integrable.mono' hMajor hFMeas hDom

/-- The physical source norm mass is controlled by the same scalar energy
majorant. The proof uses the newly constructed source integrability, rather
than smuggling it into `integral_mono_on`. -/
theorem h3Audit_initialEnergyMajorant_source_normMass_le
    (E : ℝ → ℝ)
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b c : ℝ) (hb : 0 ≤ b)
    (hE : IntervalIntegrable E volume 0 b)
    (hFMeas : AEStronglyMeasurable F
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)))
    (hBound : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      ‖F s‖ ≤ c * E s) :
    (∫ s in (0 : ℝ)..b, ‖F s‖) ≤
      c * ∫ s in (0 : ℝ)..b, E s := by
  have hF : IntervalIntegrable F volume 0 b :=
    h3Audit_initialEnergyMajorant_source_intervalIntegrable
      E F b c hb hE hFMeas hBound
  calc
    (∫ s in (0 : ℝ)..b, ‖F s‖) ≤
        ∫ s in (0 : ℝ)..b, c * E s :=
      intervalIntegral.integral_mono_on hb hF.norm
        (hE.const_mul c) hBound
    _ = c * ∫ s in (0 : ℝ)..b, E s := by
      rw [intervalIntegral.integral_const_mul]

/-- The physical diffusion-minus-transport RHS needs no separate initial
Bochner integrability hypothesis once both source norms are pointwise
controlled by a common scalar `L¹` energy envelope. -/
theorem h3Audit_initialEnergyMajorant_diffusionLeray_integrable_and_budget
    (E : ℝ → ℝ)
    (D N : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b cD cN : ℝ) (hb : 0 ≤ b)
    (hE : IntervalIntegrable E volume 0 b)
    (hDMeas : AEStronglyMeasurable D
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)))
    (hNMeas : AEStronglyMeasurable N
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)))
    (hDBound : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      ‖D s‖ ≤ cD * E s)
    (hNBound : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      ‖N s‖ ≤ cN * E s) :
    IntervalIntegrable D volume 0 b ∧
    IntervalIntegrable N volume 0 b ∧
    IntervalIntegrable (fun s : ℝ => D s - N s) volume 0 b ∧
    (∫ s in (0 : ℝ)..b, ‖D s - N s‖) ≤
      (cD + cN) * ∫ s in (0 : ℝ)..b, E s := by
  have hD : IntervalIntegrable D volume 0 b :=
    h3Audit_initialEnergyMajorant_source_intervalIntegrable
      E D b cD hb hE hDMeas hDBound
  have hN : IntervalIntegrable N volume 0 b :=
    h3Audit_initialEnergyMajorant_source_intervalIntegrable
      E N b cN hb hE hNMeas hNBound
  obtain ⟨hSplit, hSplitMass⟩ :=
    h3Audit_initialDiffusionLeray_integrableProjectedRHS_and_mass
      D N b hb hD hN
  have hDMass :=
    h3Audit_initialEnergyMajorant_source_normMass_le
      E D b cD hb hE hDMeas hDBound
  have hNMass :=
    h3Audit_initialEnergyMajorant_source_normMass_le
      E N b cN hb hE hNMeas hNBound
  refine ⟨hD, hN, hSplit, ?_⟩
  calc
    (∫ s in (0 : ℝ)..b, ‖D s - N s‖) ≤
        (∫ s in (0 : ℝ)..b, ‖D s‖) +
          (∫ s in (0 : ℝ)..b, ‖N s‖) := hSplitMass
    _ ≤ cD * (∫ s in (0 : ℝ)..b, E s) +
          cN * (∫ s in (0 : ℝ)..b, E s) :=
      add_le_add hDMass hNMass
    _ = (cD + cN) * ∫ s in (0 : ℝ)..b, E s := by
      ring

/-- A single scalar initial H³ energy integral and the two explicit
source-to-energy estimates. The weak momentum derivative is required only
at strictly positive times, and the nonlinear comparison is kept separate.

`D` and `N` are intended to be the physical diffusion and Leray advection
terms; their PDE identification is NOT a consequence of this definition. -/
def H3AuditInitialCanonicalH3EnergyMajorizedDiffusionLerayData
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
    IntervalIntegrable (velocityH3EnergyAt u) volume 0 b ∧
    ∃ (D N : ℝ → H3PhysicalRealFinVectorL2Hilbert)
      (cD cN K : ℝ),
      0 ≤ cD ∧ 0 ≤ cN ∧
      AEStronglyMeasurable D
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)) ∧
      AEStronglyMeasurable N
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
        ‖D s‖ ≤ cD * velocityH3EnergyAt u s) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
        ‖N s‖ ≤ cN * velocityH3EnergyAt u s) ∧
      (∀ (Φ : H3PhysicalRealFinVectorSchwartz) (t : ℝ),
        t ∈ Set.Ioo (0 : ℝ) b →
          HasDerivAt
            (fun x : ℝ =>
              ((innerSL ℝ)
                (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
            (((innerSL ℝ) (D t - N t))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) t) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|))

/-- Energy domination removes BOTH assumed diffusion/transport `L¹`
conditions from the preceding PDE-facing initial comparison contract. -/
theorem h3Audit_initialH3EnergyMajorized_implies_diffusionLerayData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalH3EnergyMajorizedDiffusionLerayData hH3) :
    H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hE, D, N, cD, cN, K, _hcD, _hcN,
    hDMeas, hNMeas, hDBound, hNBound, hDeriv, hEpsilon⟩ := hData
  obtain ⟨hD, hN, _, _⟩ :=
    h3Audit_initialEnergyMajorant_diffusionLeray_integrable_and_budget
      (velocityH3EnergyAt u) D N b cD cN hb.le
      hE hDMeas hNMeas hDBound hNBound
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, D, N, K, hD, hN, hDeriv, hEpsilon⟩

/-- The canonical compact weak initial comparison now consumes an initial
H³ energy `L¹` majorant in place of source-specific `L¹` assumptions. -/
theorem h3Audit_initialH3EnergyMajorized_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalH3EnergyMajorizedDiffusionLerayData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialDiffusionLeray_implies_compactWeakComparisonData
    hH3 (h3Audit_initialH3EnergyMajorized_implies_diffusionLerayData hH3 hData)

/-- Conditional actual initial physical `L²` and upper `H³` traces. -/
theorem h3Audit_initialH3EnergyMajorized_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalH3EnergyMajorizedDiffusionLerayData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialDiffusionLeray_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialH3EnergyMajorized_implies_diffusionLerayData hH3 hData)

/-- The transverse result continues to require a *separate* terminal
actual-vorticity strong-H³ hypothesis; no terminal closure is inferred. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialH3EnergyMajorized
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalH3EnergyMajorizedDiffusionLerayData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialDiffusionLeray
    hH3 hClass i hPhysical
    (h3Audit_initialH3EnergyMajorized_implies_diffusionLerayData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
