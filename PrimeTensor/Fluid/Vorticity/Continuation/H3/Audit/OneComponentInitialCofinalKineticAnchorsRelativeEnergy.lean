import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialIntegratedKineticBudgetRelativeEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPathSmoothingClosure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.From.Derivative.Identities

/-!
# Initial kinetic control from cofinal positive-time anchors

The previous initial uniqueness criterion requested an integrated kinetic
energy budget reaching all the way to time zero. A strictly smaller amount of
information is sufficient to manufacture the bounded old physical `L²` path
needed for the existing relative-energy Gronwall comparison.

The canonical `LoggedPreterminalH3PathAdmissible` class already provides:

* a physical high-order energy class preceding EACH positive time, by the
  previously closed local H³ smoothing/restart theorem;
* exact zeroth-order energy derivative identities on every such class;
* vanishing whole-space order-zero transport and pressure contributions,
  with nonpositive viscous diffusion.

Consequently the ACTUAL kinetic energy is antitone on the ENTIRE `(0,T)`, not
just on one fixed late tail. An arbitrarily early bounded-energy anchor then
controls every later positive time. No kinetic right limit or integrated
kinetic defect is required.

Bounded cofinal anchors are still an *independent initial-data input*; they
are not supplied merely by open-positive-time path admissibility. The genuine
old/selected epsilon-vanishing relative-energy comparison is independent too.
The separate terminal actual-vorticity strong-H³ endpoint is unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The actual zeroth-order physical kinetic energy is nonincreasing on the
WHOLE positive preterminal interval. Earlier BKM arguments only needed a
fixed late tail; the local restart energy-class cover closes the extension
to every pair of times `0 < s ≤ t < T`. -/
theorem h3Audit_initialKineticEnergy_antitoneOn_positiveInterval
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    AntitoneOn (velocityH3Energy0At u) (Set.Ioo (0 : ℝ) T) := by
  have hCover : H3AuditInitialPositiveEnergyClassCover (u := u) (T := T) :=
    h3Audit_h3Path_positiveEnergyClassCover hH3
  have hDifferentiable :
      DifferentiableOn ℝ (velocityH3Energy0At u) (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    obtain ⟨a, hClass, htClass⟩ := hCover t ht
    have hHas :
        HasDerivAt (velocityH3Energy0At u)
          (velocityH3FormalDerivative0At u t) t :=
      (h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3 a hClass t htClass).1
    exact hHas.differentiableAt.differentiableWithinAt
  refine antitoneOn_of_deriv_nonpos
    (convex_Ioo (0 : ℝ) T)
    hDifferentiable.continuousOn
    (hDifferentiable.mono interior_subset)
    ?_
  intro t htInterior
  have ht : t ∈ Set.Ioo (0 : ℝ) T := interior_subset htInterior
  obtain ⟨a, hClass, htClass⟩ := hCover t ht
  exact deriv_velocityH3Energy0At_nonpos_of_h3Path_derivativeIdentities
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
    hH3 hClass htClass

/-- A fixed finite kinetic ceiling on arbitrarily early strictly positive
samples automatically holds at every later time. No time regularity at zero,
kinetic right limit, or integral energy budget is asserted. -/
theorem h3Audit_initialKineticEnergy_le_of_cofinalAnchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b B : ℝ) (hbT : b ≤ T)
    (hAnchors : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
        velocityH3Energy0At u s ≤ B) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤ B := by
  have hAnti := h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3
  intro t ht
  obtain ⟨s, hs, hEnergyS⟩ := hAnchors t ht
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_of_lt_of_le ht.2 hbT⟩
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_trans hs.2 htT.2⟩
  exact (hAnti hsT htT hs.2.le).trans hEnergyS

/-- An approximate initial upper kinetic inequality on arbitrarily early
samples yields the exact dissipative bound `E₀(t) ≤ E₀(0)` for every positive
time. The epsilon limit uses only positive-time kinetic antitonicity. -/
theorem h3Audit_initialKineticEnergy_le_initial_of_cofinalApproximateAnchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hAnchors : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ∀ ε : ℝ, 0 < ε →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
          velocityH3Energy0At u s ≤ velocityH3Energy0At u 0 + ε) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      velocityH3Energy0At u t ≤ velocityH3Energy0At u 0 := by
  have hAnti := h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3
  intro t ht
  by_contra hNot
  have hGap : velocityH3Energy0At u 0 < velocityH3Energy0At u t :=
    lt_of_not_ge hNot
  let ε : ℝ := (velocityH3Energy0At u t - velocityH3Energy0At u 0) / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  obtain ⟨s, hs, hBound⟩ := hAnchors t ht ε hε
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_trans hs.2 ht.2⟩
  have hLater := hAnti hsT ht hs.2.le
  dsimp only [ε] at hBound
  linarith

/-- The selected/old difference comparison needs only cofinally bounded
old kinetic samples: no L¹ kinetic defect or finite right kinetic limit. -/
theorem h3Audit_initialOldPhysicalHilbert_norm_le_of_cofinalKineticAnchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b B : ℝ) (hbT : b ≤ T)
    (hAnchors : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
        velocityH3Energy0At u s ≤ B) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ Real.sqrt B := by
  exact h3Audit_initialOldPhysicalHilbert_norm_le_of_kineticCeiling
    hH3 b B hbT
    (h3Audit_initialKineticEnergy_le_of_cofinalAnchors
      hH3 b B hbT hAnchors)

/-- PDE-facing initial uniqueness data: arbitrarily early bounded kinetic
samples replace an integrated kinetic defect and all kinetic right-limit
assumptions. The vanishing-residual comparison is still a separate input. -/
def H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData
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
    ∃ (B K : ℝ),
      0 ≤ B ∧
      (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
          velocityH3Energy0At u s ≤ B) ∧
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

/-- Positive-time kinetic dissipation and cofinally bounded anchors supply
exactly the old physical `L²` norm ceiling required by initial uniqueness.
Old path measurability was already closed by local H³ spectral continuity. -/
theorem h3Audit_initialCofinalKineticAnchors_implies_oldKineticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3) :
    H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, B, K, hB, hAnchors, hEpsilon⟩ := hData
  have hOldMeas : AEStronglyMeasurable
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) :=
    h3Audit_initialOldPhysicalHilbert_aestronglyMeasurableOnInitial
      hH3 b hbT.le
  have hBound : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ Real.sqrt B :=
    h3Audit_initialOldPhysicalHilbert_norm_le_of_cofinalKineticAnchors
      hH3 b B hbT.le hAnchors
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, Real.sqrt B, K, Real.sqrt_nonneg _,
    hOldMeas, hBound, hEpsilon⟩

/-- Compact initial weak-test uniqueness without kinetic right limits or
integrated kinetic-energy budgets. The epsilon-vanishing comparison remains. -/
theorem h3Audit_initialCofinalKineticAnchors_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_compactWeakComparisonData
    hH3 (h3Audit_initialCofinalKineticAnchors_implies_oldKineticData hH3 hData)

/-- Initial actual physical `L²` and upper `H³` traces under the same
conditional cofinal-sample comparison. -/
theorem h3Audit_initialCofinalKineticAnchors_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialCofinalKineticAnchors_implies_oldKineticData hH3 hData)

/-- The terminal strong-H³ actual-vorticity premise remains an independent
conditional input for both full-time transverse intrinsic estimates. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCofinalKineticAnchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldKineticCeiling
    hH3 hClass i hPhysical
    (h3Audit_initialCofinalKineticAnchors_implies_oldKineticData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
