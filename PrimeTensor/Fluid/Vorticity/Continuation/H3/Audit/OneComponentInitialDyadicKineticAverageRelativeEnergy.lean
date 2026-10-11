import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialKineticEscapeDichotomy

/-!
# Initial kinetic control from positive dyadic time averages

The preceding module isolates initial kinetic escape as the remaining kinetic
alternative to compact weak-test uniqueness, conditional on the actual
old/selected relative-energy estimate.  A direct way to rule out that escape
is to bound the kinetic time average on each interval `[t/2, t]` as `t ↓ 0`.

The physical Navier--Stokes H³ path already has an actual zeroth-order energy
with nonpositive derivative at all strictly positive times.  Hence

  E₀(t) * (t/2) ≤ ∫_{t/2}^t E₀(s) ds.

The whole interval `[t/2,t]` remains in `(0,T)`; no continuity, kinetic
integrability, or energy balance *at zero* is assumed.  This module derives
positive-time interval integrability from the previously closed local H³
energy derivative identities, not from a new measurability hypothesis.

A uniform dyadic average bound therefore supplies the cofinal kinetic anchors
used by the existing conditional initial uniqueness theorem.  The actual
old/selected vanishing-residual comparison remains explicitly assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The genuine physical zeroth-order kinetic energy is continuous throughout
strictly positive preterminal time.  Its derivative at each point follows
from the closed positive-time high-order energy-class covering. -/
theorem h3Audit_initialKineticEnergy_continuousOn_positiveInterval
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ContinuousOn (velocityH3Energy0At u) (Set.Ioo (0 : ℝ) T) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  obtain ⟨a, hClass, htClass⟩ :=
    h3Audit_h3Path_positiveEnergyClassCover hH3 t ht
  have hDerivative :
      HasDerivAt (velocityH3Energy0At u)
        (velocityH3FormalDerivative0At u t) t :=
    (h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3 a hClass t htClass).1
  exact hDerivative.continuousAt

/-- Antitonicity gives a lower bound for the actual kinetic mass on each
strictly positive dyadic interval.  In particular, the average cannot be
smaller than the value at its right endpoint. -/
theorem h3Audit_initialKineticEnergy_dyadicIntegral_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    velocityH3Energy0At u t * (t / 2) ≤
      ∫ s in (t / 2)..t, velocityH3Energy0At u s := by
  have hHalf : 0 < t / 2 := by linarith [ht.1]
  have hHalfLe : t / 2 ≤ t := by linarith [ht.1]
  have hSub : Set.Icc (t / 2) t ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le hHalf hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hCont :
      ContinuousOn (velocityH3Energy0At u) (Set.Icc (t / 2) t) :=
    (h3Audit_initialKineticEnergy_continuousOn_positiveInterval hH3).mono hSub
  have hInt :
      IntervalIntegrable (velocityH3Energy0At u) volume (t / 2) t :=
    hCont.intervalIntegrable_of_Icc hHalfLe
  have hConstInt :
      IntervalIntegrable (fun _ : ℝ => velocityH3Energy0At u t)
        volume (t / 2) t :=
    continuousOn_const.intervalIntegrable_of_Icc hHalfLe
  have hAnti := h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3
  have hPointwise : ∀ s ∈ Set.Icc (t / 2) t,
      velocityH3Energy0At u t ≤ velocityH3Energy0At u s := by
    intro s hs
    exact hAnti (hSub hs) ht hs.2
  have hIntegral :
      (∫ _s in (t / 2)..t, velocityH3Energy0At u t) ≤
        ∫ s in (t / 2)..t, velocityH3Energy0At u s :=
    intervalIntegral.integral_mono_on
      hHalfLe hConstInt hInt hPointwise
  have hConstantValue :
      (∫ _s in (t / 2)..t, velocityH3Energy0At u t) =
        velocityH3Energy0At u t * (t / 2) := by
    simp [show t - t / 2 = t / 2 by ring, mul_comm]
  exact hConstantValue ▸ hIntegral

/-- Bounded dyadic kinetic time averages give a uniform pointwise kinetic
ceiling throughout the same initial interval, without any right-time limit. -/
theorem h3Audit_initialKineticEnergy_ceiling_of_dyadicAverage
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b B : ℝ) (hbT : b ≤ T)
    (hAverage : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      (∫ s in (t / 2)..t, velocityH3Energy0At u s) ≤ B * (t / 2)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤ B := by
  intro t ht
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_of_lt_of_le ht.2 hbT⟩
  have hProduct : velocityH3Energy0At u t * (t / 2) ≤
      B * (t / 2) :=
    (h3Audit_initialKineticEnergy_dyadicIntegral_lower
      hH3 t htT).trans (hAverage t ht)
  have hHalf : 0 < t / 2 := by linarith [ht.1]
  by_contra hNot
  have hStrict : B * (t / 2) < velocityH3Energy0At u t * (t / 2) :=
    mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hHalf
  exact (not_lt_of_ge hProduct) hStrict

/-- A uniform early dyadic average rules out the *actual* kinetic escape
branch of the previously proved initial-endpoint dichotomy. -/
theorem h3Audit_initialKineticEnergy_noEscape_of_dyadicAverage
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b B : ℝ) (hb : 0 < b) (hbT : b ≤ T)
    (hAverage : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      (∫ s in (t / 2)..t, velocityH3Energy0At u s) ≤ B * (t / 2)) :
    ¬ Tendsto (velocityH3Energy0At u) (𝓝[>] (0 : ℝ)) atTop := by
  intro hEscape
  have hCeiling := h3Audit_initialKineticEnergy_ceiling_of_dyadicAverage
    hH3 b B hbT hAverage
  have hLarge : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      B + 1 ≤ velocityH3Energy0At u t :=
    (tendsto_atTop.1 hEscape) (B + 1)
  have hNear : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  obtain ⟨t, htLarge, htNear⟩ := (hLarge.and hNear).exists
  have hBound := hCeiling t htNear
  linarith

/-- PDE-facing initial data: the old/selected comparison residuals are still
required, but a positive-time dyadic average controls the kinetic branch.
The average is on `[t/2,t]`, so no integrability or trace at `t=0` is assumed.
The averaging interval may be smaller than the comparison interval. -/
def H3AuditInitialCanonicalDyadicKineticAverageRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  H3AuditInitialCanonicalKineticEscapeDichotomyData hH3 ∧
    ∃ b B : ℝ, 0 < b ∧ b < T ∧ 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        (∫ s in (t / 2)..t, velocityH3Energy0At u s) ≤ B * (t / 2)

/-- The dyadic kinetic-average assumption resolves the escape-vs-uniqueness
alternative to its compact weak-test uniqueness branch. -/
theorem h3Audit_initialDyadicKineticAverage_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalDyadicKineticAverageRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  obtain ⟨hComparison, b, B, hb, hbT, _hB, hAverage⟩ := hData
  have hNoEscape :=
    h3Audit_initialKineticEnergy_noEscape_of_dyadicAverage
      hH3 b B hb hbT.le hAverage
  exact h3Audit_initialKineticNoEscape_implies_compactWeakComparisonData
    hH3 hComparison hNoEscape

/-- The original physical initial L² trace and upper H³ trace follow from
the independent dyadic average bound and vanishing-residual comparison. -/
theorem h3Audit_initialDyadicKineticAverage_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalDyadicKineticAverageRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  obtain ⟨hComparison, b, B, hb, hbT, _hB, hAverage⟩ := hData
  have hNoEscape :=
    h3Audit_initialKineticEnergy_noEscape_of_dyadicAverage
      hH3 b B hb hbT.le hAverage
  exact h3Audit_initialKineticNoEscape_implies_physicalZeroJetAndEnergyUpper
    hH3 hComparison hNoEscape

/-- The terminal actual-vorticity endpoint is still an independent premise. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialDyadicKineticAverage
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalDyadicKineticAverageRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨hComparison, b, B, hb, hbT, _hB, hAverage⟩ := hData
  have hNoEscape :=
    h3Audit_initialKineticEnergy_noEscape_of_dyadicAverage
      hH3 b B hb hbT.le hAverage
  exact Or.resolve_right
    (h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_or_initialKineticEscape
      hH3 hClass i hPhysical hComparison) hNoEscape

end
end Euclidean
end Bridge
end PrimeTensor
