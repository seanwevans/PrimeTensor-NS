import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPathSmoothingClosure

/-!
# Initial H³ trace from the actual initial physical L² and H³ energy continuity

A dependency audit of the signed-transport initial trace criterion reveals that
its two *closed initial interval continuity* hypotheses already suffice for
the weak-plus-norm H³ convergence argument. The velocity temporal derivative,
Bochner-integrable source, signed transport upper bound and formal energy-rate
integrability are all unnecessary **once those initial continuities are given**.

This module proves the required right-limit passage directly from continuity
on one genuine initial interval, then reuses the existing raw Fourier / weak
H³ / one-sided energy polarization theorem. It also proves that the previous
signed-transport core implies the reduced continuity-only criterion.

No continuity at time zero is inferred from open-time NS admissibility. In
particular, this is an interface simplification, not a proof that the initial
value problem has the required right continuity. The independent terminal
vorticity endpoint remains explicit in the full-time consequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- Continuity on an actual initial closed interval gives a right limit at
zero. This holds in any pseudometric target, including real physical L². -/
theorem h3Audit_rightTendsto_of_continuousOn_initialIcc
    {X : Type*} [PseudoMetricSpace X]
    (F : ℝ → X) {b : ℝ} (hb : 0 < b)
    (hContinuous : ContinuousOn F (Set.Icc (0 : ℝ) b)) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  have hWithin : ContinuousWithinAt F (Set.Icc (0 : ℝ) b) 0 :=
    hContinuous 0 ⟨le_rfl, hb.le⟩
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.continuousWithinAt_iff.mp hWithin) ε hε
  refine ⟨min δ b, lt_min hδ hb, ?_⟩
  intro s hsPositive hsDist
  have hsPos : (0 : ℝ) < s := hsPositive
  have hsSmall : s < min δ b := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hsPos] using hsDist
  have hsIcc : s ∈ Set.Icc (0 : ℝ) b :=
    ⟨hsPositive.le, (lt_of_lt_of_le hsSmall (min_le_right δ b)).le⟩
  exact hNear hsIcc (lt_of_lt_of_le hsDist (min_le_left δ b))

/-- The remaining initial-data criterion needs only the actual physical
zero-jet L² path and canonical H³ energy to be continuous on the initial
closed intervals. No temporal derivatives or transport estimates appear. -/
def H3AuditInitialPhysicalZeroJetAndEnergyContinuousData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0),
    (∀ (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      ContinuousOn
        (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
        (Set.Icc (0 : ℝ) t)) ∧
    (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      ContinuousOn (velocityH3EnergyAt u) (Set.Icc (0 : ℝ) t))

/-- The assumed initial closed-interval continuity directly supplies the
initial actual L² trace and one-sided H³ energy ceiling. The original
signed-transport and differentiated FTC chains are not required. -/
theorem h3Audit_initialPhysicalContinuity_implies_zeroJetL2Data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetAndEnergyContinuousData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, hVelocity, hEnergy⟩ := hData
  let b : ℝ := T / 2
  have hb : b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]
    constructor <;> linarith
  have hEnergyLimit :
      Tendsto (velocityH3EnergyAt u)
        (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) :=
    h3Audit_rightTendsto_of_continuousOn_initialIcc
      (velocityH3EnergyAt u) hb.1 (hEnergy b hb)
  refine ⟨hInt0, hMeas0, hFourier0, ?_, ?_⟩
  · intro ε hε
    have hOpen :
        Set.Iio (velocityH3EnergyAt u 0 + ε) ∈
          𝓝 (velocityH3EnergyAt u 0) :=
      Iio_mem_nhds (by linarith)
    exact hEnergyLimit.eventually hOpen
  · intro j
    have hAnchored :
        Tendsto
          (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
          (𝓝[>] (0 : ℝ))
          (𝓝 (h3AuditInitialPhysicalZeroJetAnchored
            hH3 hInt0 hMeas0 j 0)) :=
      h3Audit_rightTendsto_of_continuousOn_initialIcc
        (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
        hb.1 (hVelocity j b hb)
    have hInitial :
        Tendsto
          (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
          (𝓝[>] (0 : ℝ))
          (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))) := by
      simpa only [h3AuditInitialPhysicalZeroJetAnchored_eq_zero] using hAnchored
    have hEventually :
        (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
          =ᶠ[𝓝[>] (0 : ℝ)]
        (h3AuditActualPhysicalZeroJetL2Total hH3 j) := by
      filter_upwards [h3Audit_eventually_initialStrictPhysicalTime hT]
        with s hs
      exact h3AuditInitialPhysicalZeroJetAnchored_eq_at
        hH3 hInt0 hMeas0 j s hs
    exact hInitial.congr' hEventually

/-- A strong initial H³ trace requires only these two initial continuities
and an actual initial H³ Fourier encoder; no transport or FTC source is
assumed by this theorem. -/
theorem h3Audit_initialPhysicalContinuity_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetAndEnergyContinuousData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalZeroJetL2AndEnergyUpper_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialPhysicalContinuity_implies_zeroJetL2Data hH3 hT hData)

/-- Audit: the signed-transport core *already contains* the two continuities
that prove the initial strong H³ trace. Its velocity-derivative, source-rate,
energy-rate integrability and signed-transport fields are redundant for that
specific consequence, although useful for independent PDE estimates. -/
theorem h3Audit_initialSignedTransportCore_implies_continuityData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalSignedTransportCoreData hH3) :
    H3AuditInitialPhysicalZeroJetAndEnergyContinuousData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, _V, _Cv, _Ct,
    _hCv, _hCt, hVelocity, hEnergy, _hTransport⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, ?_, ?_⟩
  · intro j t ht
    exact (hVelocity j t ht).1
  · intro t ht
    exact (hEnergy t ht).1

/-- The old signed-transport criterion now has a shorter independent proof
via the actual initial physical and energy continuity fields. -/
theorem h3Audit_initialSignedTransportCore_strongH3Trace_via_continuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalSignedTransportCoreData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalContinuity_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialSignedTransportCore_implies_continuityData hH3 hData)

/-- The full-time transverse Sobolev consequence still assumes the
independent actual terminal strong-H³ vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialContinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalZeroJetAndEnergyContinuousData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  have hT : 0 < T :=
    lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalZeroJetL2
    hH3 hClass i hPhysical
    (h3Audit_initialPhysicalContinuity_implies_zeroJetL2Data hH3 hT hData)

end
end Euclidean
end Bridge
end PrimeTensor
