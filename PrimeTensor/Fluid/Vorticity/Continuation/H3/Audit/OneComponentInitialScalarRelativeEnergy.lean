import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRelativeEnergyUniqueness

/-!
# Initial canonical overlap from scalar relative-energy continuity

The previous relative-energy proof assumed strong continuity of the entire
old-minus-selected physical L² difference on the closed initial interval.
The integral Grönwall argument actually only differentiates the scalar
primitive of its *squared norm*. Consequently, continuity of the scalar
relative energy suffices, without strong continuity of the vector difference.

Neither the scalar relative-energy inequality nor continuity of the energy at
zero is inferred from the open-time Navier--Stokes admissibility predicate.
Both remain explicit, independently checkable PDE-facing obligations. The
actual initial datum is still the physical u(0) Fourier encoding, and the
terminal actual-vorticity endpoint remains independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Scalar integral Grönwall in the nonnegative-energy form. The energy
function itself, rather than a vector-valued square root, is continuous. -/
theorem h3Audit_initialScalarEnergy_integralGronwall
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heCont : ContinuousOn e (Set.Icc (0 : ℝ) b))
    (hEnergy : ∀ t ∈ Set.Icc (0 : ℝ) b,
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  let H : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, e r
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
    exact intervalIntegral.integral_nonneg hs.1 (fun r _hr => heNonneg r)
  have hEnergy' : ∀ s ∈ Set.Icc (0 : ℝ) b,
      e s ≤ K * H s := by
    intro s hs
    simpa only [H] using hEnergy s hs
  have hDerivBound : ∀ s ∈ Set.Ico (0 : ℝ) b,
      ‖e s‖ ≤ K * ‖H s‖ := by
    intro s hs
    have hsClosed : s ∈ Set.Icc (0 : ℝ) b :=
      ⟨hs.1, le_of_lt hs.2⟩
    have he0 : 0 ≤ e s := heNonneg s
    have hH0 : 0 ≤ H s := hHNonneg s hsClosed
    simpa only [Real.norm_eq_abs, abs_of_nonneg he0,
      abs_of_nonneg hH0] using hEnergy' s hsClosed
  have hHVanishing : ∀ s ∈ Set.Icc (0 : ℝ) b, H s = 0 := by
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      hHCont hHDerivRight hHZero hDerivBound
  have hBound := hEnergy' t ht
  rw [hHVanishing t ht, mul_zero] at hBound
  exact le_antisymm hBound (heNonneg t)

/-- The squared norm can be continuous even when a priori no strong
Hilbert-space continuity hypothesis is furnished for the difference. -/
theorem h3Audit_initialScalarRelativeEnergy_difference_eq_zero
    (D : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b K : ℝ) (hb : 0 < b)
    (hScalar : ContinuousOn (fun s => ‖D s‖ ^ 2)
      (Set.Icc (0 : ℝ) b))
    (hEnergy : ∀ t ∈ Set.Icc (0 : ℝ) b,
      ‖D t‖ ^ 2 ≤ K * ∫ s in (0 : ℝ)..t, ‖D s‖ ^ 2)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    D t = 0 := by
  have hSq : ‖D t‖ ^ 2 = 0 :=
    h3Audit_initialScalarEnergy_integralGronwall
      (fun s => ‖D s‖ ^ 2) b K hb
      (fun s => sq_nonneg ‖D s‖) hScalar hEnergy t ht
  have hNorm : ‖D t‖ = 0 := by
    nlinarith [norm_nonneg (D t)]
  exact norm_eq_zero.mp hNorm

/-- A strictly weaker initial uniqueness contract than the previous one:
only scalar-energy continuity is required. The relative-energy inequality
remains a PDE input; weak-test equality is NOT a premise. -/
def H3AuditInitialCanonicalScalarRelativeEnergyData
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
        (Set.Icc (0 : ℝ) b) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) b,
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
        K * ∫ s in (0 : ℝ)..t,
          ‖h3AuditInitialCanonicalPhysicalDifference
            hH3 hFourier0 A hA hU₀ s‖ ^ 2

/-- The original strong-difference continuity contract implies the new
scalar-energy continuity contract, with exactly the same PDE inequality. -/
theorem h3Audit_initialRelativeEnergy_implies_scalarRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRelativeEnergyData hH3) :
    H3AuditInitialCanonicalScalarRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, _hK, hDCont, hEnergy⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, ?_, hEnergy⟩
  exact (continuous_norm.comp_continuousOn hDCont).pow 2

/-- Scalar relative-energy continuity and the PDE inequality give physical
compact weak-test agreement with no vector-continuity assumption. -/
theorem h3Audit_initialScalarRelativeEnergy_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalScalarRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, hEnergy⟩ := hData
  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialCanonicalPhysicalDifference hH3 hFourier0 A hA hU₀
  have hZero : ∀ t ∈ Set.Icc (0 : ℝ) b, D t = 0 := by
    intro t ht
    exact h3Audit_initialScalarRelativeEnergy_difference_eq_zero
      D b K hb hScalar hEnergy t ht
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

/-- The scalar-energy route recovers genuine physical initial L² and H³
energy right traces through physical realizability and Fourier injection. -/
theorem h3Audit_initialScalarRelativeEnergy_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalScalarRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialCanonicalCompactWeakComparison_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialScalarRelativeEnergy_implies_compactWeakComparisonData
      hH3 hData)

/-- The full-time transverse conclusion is still conditional on the
independent physical terminal vorticity strong-H³ endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarRelativeEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalScalarRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactWeakComparison
    hH3 hClass i hPhysical
    (h3Audit_initialScalarRelativeEnergy_implies_compactWeakComparisonData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
