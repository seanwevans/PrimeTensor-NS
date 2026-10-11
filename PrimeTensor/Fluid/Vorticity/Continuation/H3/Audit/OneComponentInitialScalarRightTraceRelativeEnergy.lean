import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialEpsilonResidualRelativeEnergy

/-!
# Initial scalar relative energy: positive-time continuity plus a zero right trace

The epsilon-residual initial uniqueness criterion assumes closed-interval
continuity of the artificially zero-anchored scalar relative energy.
This file factors that condition into two separate inputs:

* scalar energy continuity on the positive half-open interval `(0,b]`;
* a right limit of zero for the same scalar energy at physical time zero.

The second requirement is a substantive initial-matching assumption. It is NOT
proved from the open-time Navier--Stokes admissibility predicate and is NOT
inferred from the desired old/selected equality. Together with arbitrarily
small integrated residuals, it yields exactly the established Gronwall,
canonical initial overlap, and conditional full-time transverse consequences.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A real function continuous at every strictly positive time up to `b`
and having the specified right limit at zero is continuous on `[0,b]`.
The right limit is the *actual function value* at zero, not an arbitrary
unidentified trace. -/
theorem h3Audit_initialScalarClosedContinuous_of_positiveAndRightTrace
    (e : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hPositive : ContinuousOn e (Set.Ioc (0 : ℝ) b))
    (hRight : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (e 0))) :
    ContinuousOn e (Set.Icc (0 : ℝ) b) := by
  intro t ht
  by_cases htZero : t = 0
  · subst t
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hNear⟩ :=
      (Metric.tendsto_nhdsWithin_nhds.mp hRight) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro s hs hsDist
    by_cases hsZero : s = 0
    · simpa [hsZero] using hε
    · have hsPositive : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
      exact hNear hsPositive hsDist
  · have htPositive : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htZero)
    have hWithin : ContinuousWithinAt e (Set.Ioc (0 : ℝ) b) t :=
      hPositive t ⟨htPositive, ht.2⟩
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hNear⟩ :=
      (Metric.continuousWithinAt_iff.mp hWithin) ε hε
    refine ⟨min δ t, lt_min hδ htPositive, ?_⟩
    intro s hs hsDist
    have hGap : t - s ≤ dist s t := by
      rw [Real.dist_eq]
      linarith [neg_le_abs (s - t)]
    have hsPositive : 0 < s := by
      have hDistance : dist s t < t :=
        lt_of_lt_of_le hsDist (min_le_right δ t)
      linarith
    exact hNear ⟨hsPositive, hs.2⟩
      (lt_of_lt_of_le hsDist (min_le_left δ t))

/-- The squared norm of a strongly right-convergent Hilbert-space
comparison goes to zero. This is an independent sufficient criterion for
the scalar trace assumption, not a proof of such strong matching from NS. -/
theorem h3Audit_initialScalarRightZero_of_strongDifferenceRightZero
    (D : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (hRight : Tendsto D (𝓝[>] (0 : ℝ))
      (𝓝 (0 : H3PhysicalRealFinVectorL2Hilbert))) :
    Tendsto (fun t : ℝ => ‖D t‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hMap : Continuous
      (fun v : H3PhysicalRealFinVectorL2Hilbert => ‖v‖ ^ 2) :=
    continuous_norm.pow 2
  have hLimit := hMap.continuousAt.tendsto.comp hRight
  simpa [Function.comp_def] using hLimit

/-- An epsilon-residual relative-energy interface in which initial scalar
continuity is decomposed into positive-time continuity and right zero trace.
The epsilon-accurate PDE inequality remains an explicit separate input. -/
def H3AuditInitialCanonicalEpsilonResidualRightTraceData
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
    ∃ K : ℝ,
      ContinuousOn
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (Set.Ioc (0 : ℝ) b) ∧
      Tendsto
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ : ℝ) (R : ℝ → ℝ),
          κ ≤ K ∧
          IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (κ * ∫ s in (0 : ℝ)..t,
                ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Positive-time scalar continuity plus the independently supplied zero
right trace recover the closed-interval scalar condition for Gronwall. -/
theorem h3Audit_initialEpsilonResidualRightTrace_implies_epsilonResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEpsilonResidualRightTraceData hH3) :
    H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hPositive, hRight, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, ?_, hEpsilon⟩
  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialCanonicalPhysicalDifference hH3 hFourier0 A hA hU₀
  have hZero : (fun t : ℝ => ‖D t‖ ^ 2) 0 = 0 := by
    simp [D]
  have hRight' : Tendsto (fun t : ℝ => ‖D t‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((fun t : ℝ => ‖D t‖ ^ 2) 0)) := by
    simpa only [hZero] using hRight
  exact h3Audit_initialScalarClosedContinuous_of_positiveAndRightTrace
    (fun t => ‖D t‖ ^ 2) b hb hPositive hRight'

/-- Canonical compact weak-test agreement without postulating closed-interval
scalar-energy continuity as one opaque premise. -/
theorem h3Audit_initialEpsilonResidualRightTrace_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEpsilonResidualRightTraceData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialEpsilonResidual_implies_compactWeakComparisonData
    hH3
    (h3Audit_initialEpsilonResidualRightTrace_implies_epsilonResidualData
      hH3 hData)

/-- Physical initial L² trace and H³ energy upper control follow from
positive-time regularity, independently verified right zero matching and
epsilon-small integrated error estimates. -/
theorem h3Audit_initialEpsilonResidualRightTrace_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEpsilonResidualRightTraceData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialEpsilonResidual_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialEpsilonResidualRightTrace_implies_epsilonResidualData
      hH3 hData)

/-- Full-time two-component conclusion stays conditional on the separate
strong-H³ endpoint of an actual vorticity component. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialEpsilonResidualRightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalEpsilonResidualRightTraceData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialEpsilonResidual
    hH3 hClass i hPhysical
    (h3Audit_initialEpsilonResidualRightTrace_implies_epsilonResidualData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
