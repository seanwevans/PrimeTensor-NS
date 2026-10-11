import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAutomaticOldTimeMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy

/-!
# Initial comparison from the actual right kinetic-energy trace

The earlier initial-uniqueness interface assumed a finite *full H³* right
energy limit solely to bound the physical L² velocity near time zero. That
is stronger than needed. The physical order-zero jet-energy identity gives

    ‖u_old(t)‖_(L²)^2 = velocityH3Energy0At u t

for every strict physical time. Therefore a finite right limit of the
order-zero kinetic energy yields the required uniform physical L² ceiling on
some initial interval, with no right-H³-energy trace.

The time measurability of the actual old physical L² velocity has already
been proved from local H³ path continuity. The integrated-coefficient,
vanishing-residual comparison remains a separate PDE-side obligation.
Importantly, this reduction does NOT assert that a finite kinetic right trace
follows from `LoggedPreterminalH3PathAdmissible`: positive-time kinetic
monotonicity, by itself, need not bound the energy as t -> 0+.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- At every strict time the genuine old three-component physical L² norm
squared is *exactly* the order-zero physical kinetic energy; this is not an
H³-energy estimate or a separately chosen bound. -/
theorem h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 =
      velocityH3Energy0At u t := by
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  have hCoord (j : Fin 3) :
      (h3AuditInitialOldPhysicalHilbertTotal hH3 t) j =
        velocityH3L2JetAt u t hInt hMeas (Sum.inl j) := by
    change h3AuditActualPhysicalZeroJetL2Total hH3 j t =
      velocityH3L2JetAt u t hInt hMeas (Sum.inl j)
    exact h3AuditActualPhysicalZeroJetL2Total_eq_at hH3 j t ht
  calc
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 =
        ∑ j : Fin 3,
          ‖(h3AuditInitialOldPhysicalHilbertTotal hH3 t) j‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2
        (fun _ : Fin 3 => H3ScalarL2)
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
    _ = ∑ j : H3JetIndex0,
          ‖velocityH3L2JetAt u t hInt hMeas (Sum.inl j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hCoord j]
    _ = velocityH3Energy0At u t :=
      velocityH3L2JetAt_squareEnergy0_eq hInt hMeas

/-- The physical old-velocity L² norm is the positive square root of its
actual zeroth-order kinetic energy at every strict physical time. -/
theorem h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ =
      Real.sqrt (velocityH3Energy0At u t) := by
  have hSq := h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
    hH3 t ht
  calc
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ =
        Real.sqrt (‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = Real.sqrt (velocityH3Energy0At u t) :=
      congrArg Real.sqrt hSq

/-- A ceiling on the order-zero kinetic energy alone bounds the actual old
physical L² velocity; higher derivative energies play no role. -/
theorem h3Audit_initialOldPhysicalHilbert_norm_le_of_kineticCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b E : ℝ) (hbT : b ≤ T)
    (hKinetic : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤ E) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ Real.sqrt E := by
  intro t ht
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_of_lt_of_le ht.2 hbT⟩
  calc
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ =
        Real.sqrt (velocityH3Energy0At u t) :=
      h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy hH3 t htT
    _ ≤ Real.sqrt E := Real.sqrt_le_sqrt (hKinetic t ht)

/-- Initial uniqueness requires only a finite *kinetic* right trace, not a
right trace for the full H³ energy. Old-velocity time measurability has
already been discharged unconditionally on (0,T). The small-residual
relative-energy inequality remains an explicit, substantive PDE input. -/
def H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b₀ : ℝ),
    0 < b₀ ∧ b₀ < T ∧
    b₀ ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (L K : ℝ),
      Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b₀) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b₀ → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b₀ ∧
          (∫ s in (0 : ℝ)..b₀, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b₀ →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Extract a short physical kinetic-energy ceiling from its independent
right-time trace and manufacture the entire old-L² comparison input. -/
theorem h3Audit_initialRightKineticTrace_implies_oldKineticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData hH3) :
    H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b₀, hb₀, hb₀T, hb₀R, L, K, hRight, hEpsilon⟩ := hData
  obtain ⟨b, hb, hbb₀, hKinetic⟩ :=
    h3Audit_initialRightLimit_shortUpperBound
      (velocityH3Energy0At u) L b₀ 1 hb₀ (by norm_num) hRight
  have hbT : b < T := lt_of_le_of_lt hbb₀ hb₀T
  have hMeas : AEStronglyMeasurable
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) :=
    h3Audit_initialOldPhysicalHilbert_aestronglyMeasurableOnInitial
      hH3 b hbT.le
  have hBound :=
    h3Audit_initialOldPhysicalHilbert_norm_le_of_kineticCeiling
      hH3 b (L + 1) hbT.le hKinetic
  have hEpsilonB :=
    h3Audit_initialIntegratedComparison_restrict_initialInterval
      (fun t : ℝ =>
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
      b b₀ K hb hbb₀ hEpsilon
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbb₀.trans hb₀R,
    Real.sqrt (L + 1), K, Real.sqrt_nonneg _,
    hMeas, hBound, hEpsilonB⟩

/-- Physical weak-test uniqueness from an independent finite right *kinetic*
trace and the still-explicit vanishing-residual PDE comparison. -/
theorem h3Audit_initialRightKineticTrace_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_compactWeakComparisonData
    hH3 (h3Audit_initialRightKineticTrace_implies_oldKineticData hH3 hData)

/-- Consequent initial physical L² trace and H³ upper energy trace. The
H³ result is an *output* of comparison, not an assumption here. -/
theorem h3Audit_initialRightKineticTrace_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialRightKineticTrace_implies_oldKineticData hH3 hData)

/-- The terminal strong-H³ actual-vorticity input remains independent. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightKineticTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData hH3) :
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
    (h3Audit_initialRightKineticTrace_implies_oldKineticData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
