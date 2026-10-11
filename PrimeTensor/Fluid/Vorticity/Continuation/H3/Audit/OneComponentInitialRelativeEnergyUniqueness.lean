import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalWeakTestComparison
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Initial old/selected overlap from a physical relative-energy inequality

The previous initial-time audit assumed equality of physical old and selected
weak test pairings at all strictly positive early times. That is essentially
an equality assertion. Here the actual old/selected difference is put in the
real three-coordinate physical L² Hilbert space, and equality is instead
DEDUCED from the standard derivative-free relative-energy inequality:

    ‖D(t)‖² ≤ K * integral_0^t ‖D(s)‖² ds.

The integral Grönwall lemma requires only continuity of the difference on the
closed interval, not any strong time derivative. At physical time zero the
difference is explicitly anchored to zero; `ContinuousOn` is a separate,
substantive initial physical L² matching requirement. It is NOT supplied by
open-time Navier--Stokes admissibility and must not be deduced circularly from
the canonical overlap that we are trying to prove.

The scalar relative-energy inequality is also a separate PDE obligation.
Given those two obligations, Grönwall gives actual-old/selected L² equality;
compact weak tests and the repository's realizability/decoder theorem upgrade
this to exact canonical weighted H³ overlap. The independent terminal
vorticity endpoint remains a separate assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Abstract integral Grönwall in the project's real three-component physical
L² Hilbert space. No Hilbert-valued derivative is assumed. -/
theorem h3Audit_initialRelativeEnergy_integralGronwall
    (D : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b K : ℝ) (hb : 0 < b) (hK : 0 ≤ K)
    (hD : ContinuousOn D (Set.Icc (0 : ℝ) b))
    (hEnergy : ∀ t ∈ Set.Icc (0 : ℝ) b,
      ‖D t‖ ^ 2 ≤ K * ∫ s in (0 : ℝ)..t, ‖D s‖ ^ 2)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    D t = 0 := by
  let e : ℝ → ℝ := fun r => ‖D r‖ ^ 2
  let H : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, e r
  have heCont : ContinuousOn e (Set.Icc (0 : ℝ) b) := by
    dsimp only [e]
    exact (continuous_norm.comp_continuousOn hD).pow 2
  have hHDerivIcc :
      ∀ s ∈ Set.Icc (0 : ℝ) b,
        HasDerivWithinAt H (e s) (Set.Icc (0 : ℝ) b) s := by
    intro s hs
    letI : Fact (s ∈ Set.Icc (0 : ℝ) b) := ⟨hs⟩
    have hInt : IntervalIntegrable e volume (0 : ℝ) s := by
      exact (heCont.mono
        (Set.Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    have hMeas :
        StronglyMeasurableAtFilter e
          (𝓝[Set.Icc (0 : ℝ) b] s) := by
      exact heCont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s
    have hCont : ContinuousWithinAt e (Set.Icc (0 : ℝ) b) s :=
      heCont.continuousWithinAt hs
    dsimp only [H]
    exact intervalIntegral.integral_hasDerivWithinAt_right hInt hMeas hCont
  have hHCont : ContinuousOn H (Set.Icc (0 : ℝ) b) := by
    intro s hs
    exact (hHDerivIcc s hs).continuousWithinAt
  have hHDerivRight :
      ∀ s ∈ Set.Ico (0 : ℝ) b,
        HasDerivWithinAt H (e s) (Set.Ici s) s := by
    intro s hs
    have hsClosed : s ∈ Set.Icc (0 : ℝ) b :=
      ⟨hs.1, le_of_lt hs.2⟩
    have hBase := hHDerivIcc s hsClosed
    have hSmall : HasDerivWithinAt H (e s) (Set.Icc s b) s := by
      exact hBase.mono (by
        intro x hx
        exact ⟨hs.1.trans hx.1, hx.2⟩)
    have hLocal : Set.Icc s b =ᶠ[𝓝 s] Set.Ici s := by
      filter_upwards [Iio_mem_nhds hs.2] with x hx
      have hxb : x < b := Set.mem_Iio.mp hx
      apply propext
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, le_of_lt hxb⟩
    exact hSmall.congr_set hLocal
  have hHZero : H 0 = 0 := by simp [H]
  have hHNonneg : ∀ s ∈ Set.Icc (0 : ℝ) b, 0 ≤ H s := by
    intro s hs
    dsimp only [H]
    exact intervalIntegral.integral_nonneg hs.1
      (fun r _hr => sq_nonneg ‖D r‖)
  have hEnergy' : ∀ s ∈ Set.Icc (0 : ℝ) b,
      e s ≤ K * H s := by
    intro s hs
    simpa only [e, H] using hEnergy s hs
  have hDerivBound : ∀ s ∈ Set.Ico (0 : ℝ) b,
      ‖e s‖ ≤ K * ‖H s‖ := by
    intro s hs
    have hsClosed : s ∈ Set.Icc (0 : ℝ) b :=
      ⟨hs.1, le_of_lt hs.2⟩
    have he0 : 0 ≤ e s := sq_nonneg _
    have hH0 : 0 ≤ H s := hHNonneg s hsClosed
    simpa only [Real.norm_eq_abs, abs_of_nonneg he0,
      abs_of_nonneg hH0] using hEnergy' s hsClosed
  have hHVanishing : ∀ s ∈ Set.Icc (0 : ℝ) b, H s = 0 := by
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      hHCont hHDerivRight hHZero hDerivBound
  have heZero : e t = 0 := by
    have hBound := hEnergy' t ht
    rw [hHVanishing t ht, mul_zero] at hBound
    exact le_antisymm hBound (sq_nonneg _)
  have hNormSq : ‖D t‖ ^ 2 = 0 := by
    simpa only [e] using heZero
  have hNorm : ‖D t‖ = 0 := by
    nlinarith [norm_nonneg (D t)]
  exact norm_eq_zero.mp hNorm

/-- Physical old minus canonical selected L² difference on positive times,
with an explicit ZERO endpoint value. Continuity at that artificial endpoint
is a genuine separate initial-data hypothesis, not a consequence of the
open-time H³ admissibility class. -/
noncomputable def h3AuditInitialCanonicalPhysicalDifference
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {hInt0 : VelocityH3IntegrableAt u (0 : ℝ)}
    {hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)}
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (s : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  if s = 0 then 0 else
    WithLp.toLp 2 (fun j : Fin 3 =>
      h3AuditActualPhysicalZeroJetL2Total hH3 j s -
      h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
        ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
          hA hU₀ s) j)))

@[simp]
theorem h3AuditInitialCanonicalPhysicalDifference_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {hInt0 : VelocityH3IntegrableAt u (0 : ℝ)}
    {hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)}
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A) :
    h3AuditInitialCanonicalPhysicalDifference hH3 hFourier0 A hA hU₀ 0 = 0 := by
  simp [h3AuditInitialCanonicalPhysicalDifference]

/-- A PDE-facing uniqueness contract. The two nontrivial obligations are
strong physical L² continuity at the initial endpoint of the ANCHORED
selected-minus-old difference, and the derivative-free relative-energy
inequality. No physical weak-test equality is included as a premise. -/
def H3AuditInitialCanonicalRelativeEnergyData
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
    ∃ K : ℝ, 0 ≤ K ∧
      ContinuousOn
        (h3AuditInitialCanonicalPhysicalDifference hH3 hFourier0 A hA hU₀)
        (Set.Icc (0 : ℝ) b) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) b,
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
        K * ∫ s in (0 : ℝ)..t,
          ‖h3AuditInitialCanonicalPhysicalDifference
            hH3 hFourier0 A hA hU₀ s‖ ^ 2

/-- Genuine scalar relative-energy control gives exact physical compact
weak-test agreement, rather than presupposing that agreement. -/
theorem h3Audit_initialRelativeEnergy_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hK, hDCont, hEnergy⟩ := hData
  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialCanonicalPhysicalDifference hH3 hFourier0 A hA hU₀
  have hZero : ∀ t ∈ Set.Icc (0 : ℝ) b, D t = 0 := by
    intro t ht
    exact h3Audit_initialRelativeEnergy_integralGronwall
      D b K hb hK hDCont hEnergy t ht
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀, b,
    hb, hbT, hbR, ?_⟩
  intro t ht htb j φ
  have htNe : t ≠ 0 := ne_of_gt ht.1
  have hDt : D t = 0 := hZero t ⟨ht.1.le, htb.le⟩
  have hCoord := congrArg
    (fun F : H3PhysicalRealFinVectorL2Hilbert => F j) hDt
  have hPhysical :
      h3AuditActualPhysicalZeroJetL2Total hH3 j t =
        h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
            hA hU₀ t) j)) := by
    change (if t = 0 then
      (0 : H3PhysicalRealFinVectorL2Hilbert)
      else WithLp.toLp 2 (fun k : Fin 3 =>
        h3AuditActualPhysicalZeroJetL2Total hH3 k t -
        h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
            hA hU₀ t) k)))) j = 0 at hCoord
    simpa only [if_neg htNe, PiLp.toLp_apply,
      PiLp.zero_apply, sub_eq_zero] using hCoord
  exact congrArg
    (fun F : H3ScalarL2 => inner ℝ (h3WeakTestFunctionPhysicalL2 φ) F)
    hPhysical

/-- Close actual initial physical L² and H³ energy continuity using the
relative-energy inequality and existing physically realizable decoder bridge.
The terminal-side result is still completely independent. -/
theorem h3Audit_initialRelativeEnergy_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact
    h3Audit_initialCanonicalCompactWeakComparison_implies_physicalZeroJetAndEnergyUpper
      hH3
      (h3Audit_initialRelativeEnergy_implies_compactWeakComparisonData
        hH3 hData)

/-- Conditional full-time transverse intrinsic homogeneous H^(3/2) result.
The physical terminal vorticity strong H³ endpoint remains required. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRelativeEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactWeakComparison
      hH3 hClass i hPhysical
      (h3Audit_initialRelativeEnergy_implies_compactWeakComparisonData
        hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
