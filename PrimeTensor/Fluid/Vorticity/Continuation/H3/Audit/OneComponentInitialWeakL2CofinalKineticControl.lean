import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialDyadicKineticAverageRelativeEnergy
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Weak physical L² initial trace forces cofinal bounded kinetic samples

The preceding initial comparison reduced the kinetic obstruction to a
uniform physical L² ceiling on a sequence of positive times descending
to zero. Such a bound follows from genuine weak L² convergence of the
ACTUAL old physical velocity along the sequence, by Banach–Steinhaus.

The weak tests in this module range over the COMPLETE physical Hilbert
space, not merely compact smooth spatial test functions. Convergence of
compact test pairings alone does not rule out high-frequency kinetic escape.

No strong L² initial convergence or kinetic right trace is used. The
separate epsilon-vanishing nonlinear relative-energy comparison is still
required. The strong-H³ terminal vorticity hypothesis is still independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A real scalar sequence converging at infinity has a *global* finite
norm bound, including its finite initial segment. -/
theorem h3Audit_initialScalarSequence_normBounded_of_tendsto
    (g : ℕ → ℝ) (L : ℝ)
    (hLimit : Tendsto g atTop (𝓝 L)) :
    ∃ C : ℝ, ∀ n : ℕ, ‖g n‖ ≤ C := by
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp hLimit) 1 (by norm_num)
  let S : ℝ := ∑ k ∈ Finset.range N, ‖g k‖
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg (fun k _ => norm_nonneg (g k))
  refine ⟨S + ‖L‖ + 1, ?_⟩
  intro n
  by_cases hn : n < N
  · have hTerm : ‖g n‖ ≤ S := by
      dsimp only [S]
      exact Finset.single_le_sum
        (fun k _ => norm_nonneg (g k)) (Finset.mem_range.mpr hn)
    linarith [norm_nonneg L]
  · have hDist : dist (g n) L < 1 := hN n (Nat.le_of_not_gt hn)
    have hNear : ‖g n - L‖ < 1 := by
      simpa only [Real.dist_eq, Real.norm_eq_abs] using hDist
    have hTriangle : ‖g n‖ ≤ ‖g n - L‖ + ‖L‖ := by
      simpa only [sub_add_cancel] using norm_add_le (g n - L) L
    linarith

/-- Banach–Steinhaus converts bounded physical weak pairings along a sequence
into a single norm bound on that sequence. This is the uniform boundedness
principle applied to the real-Hilbert Riesz maps `innerSL ℝ (U n)`. -/
theorem h3Audit_initialWeakPairingBoundedSequence_normBounded
    (U : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (hPointwise : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      ∃ C : ℝ, ∀ n : ℕ,
        ‖((innerSL ℝ) (U n)) ψ‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ‖U n‖ ≤ B := by
  obtain ⟨B, hBound⟩ :=
    banach_steinhaus (g := fun n : ℕ => (innerSL ℝ) (U n)) hPointwise
  have hNorm : ∀ n : ℕ, ‖U n‖ ≤ B := by
    intro n
    calc
      ‖U n‖ = ‖(innerSL ℝ) (U n)‖ :=
        (innerSL_apply_norm ℝ (U n)).symm
      _ ≤ B := hBound n
  have hB : 0 ≤ B := (norm_nonneg (U 0)).trans (hNorm 0)
  exact ⟨B, hB, hNorm⟩

/-- Weak convergence against *every* physical Hilbert test has uniformly
bounded pairings, hence a uniformly bounded sequence of L² velocities.
No strong convergence, compactness or energy estimate is needed. -/
theorem h3Audit_initialWeakL2ConvergentSequence_normBounded
    (U : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (fun n : ℕ => ((innerSL ℝ) (U n)) ψ)
        atTop (𝓝 (((innerSL ℝ) U₀) ψ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ‖U n‖ ≤ B := by
  apply h3Audit_initialWeakPairingBoundedSequence_normBounded U
  intro ψ
  exact h3Audit_initialScalarSequence_normBounded_of_tendsto
    (fun n => ((innerSL ℝ) (U n)) ψ)
    (((innerSL ℝ) U₀) ψ) (hWeak ψ)

/-- The actual time-zero physical L² velocity jet, encoded in the same
three-component real Hilbert space as the positive-time old velocity. -/
noncomputable def h3Audit_initialActualPhysicalHilbertAtZero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp (2 : ℝ≥0∞)
    (fun j : Fin 3 =>
      velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))

/-- A cofinal sequence of genuine positive-time old velocities weakly
converging to the actual physical initial L² jet cannot carry kinetic escape.
The norm bound is produced by the uniform boundedness principle. -/
theorem h3Audit_initialWeakL2CofinalSequence_kineticAnchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hbT : b ≤ T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) b)
    (hCofinal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) t)
    (hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (fun n : ℕ =>
        ((innerSL ℝ) (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ)
        atTop (𝓝 (((innerSL ℝ)
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ψ))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
          velocityH3Energy0At u s ≤ B := by
  obtain ⟨M, hM, hNorm⟩ :=
    h3Audit_initialWeakL2ConvergentSequence_normBounded
      (fun n => h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      hWeak
  have hEnergy : ∀ n : ℕ, velocityH3Energy0At u (τ n) ≤ M ^ 2 := by
    intro n
    have hnT : τ n ∈ Set.Ioo (0 : ℝ) T :=
      ⟨(hτ n).1, lt_of_lt_of_le (hτ n).2 hbT⟩
    have hSq := h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 (τ n) hnT
    calc
      velocityH3Energy0At u (τ n) =
          ‖h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n)‖ ^ 2 := hSq.symm
      _ ≤ M ^ 2 :=
        pow_le_pow_left₀
          (norm_nonneg (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n)))
          (hNorm n) 2
  refine ⟨M ^ 2, sq_nonneg M, ?_⟩
  intro t ht
  obtain ⟨n, hn⟩ := hCofinal t ht
  exact ⟨τ n, hn, hEnergy n⟩

/-- A PDE-facing initial-data contract with a *genuine weak L² sequential
trace* instead of a kinetic energy bound or energy time-average bound.
The weak limit is the actual old initial-time physical L² jet, not an
unrelated spectral datum. The nonlinear comparison remains independent. -/
def H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData
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
    ∃ (τ : ℕ → ℝ) (K : ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) b) ∧
      (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) t) ∧
      (∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
        Tendsto (fun n : ℕ =>
          ((innerSL ℝ) (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ)
          atTop (𝓝 (((innerSL ℝ)
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ψ))) ∧
      ∀ ε : ℝ, 0 < ε →
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
              (∫ s in (0 : ℝ)..t, |R s|)

/-- The weak initial L² trace automatically supplies the previous cofinal
kinetic-anchor contract, without using an initial strong L² trace. -/
theorem h3Audit_initialWeakL2Cofinal_implies_kineticAnchorData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, τ, K, hτ, hCofinal, hWeak, hEpsilon⟩ := hData
  obtain ⟨B, hB, hSamples⟩ :=
    h3Audit_initialWeakL2CofinalSequence_kineticAnchors
      hH3 hInt0 hMeas0 b hbT.le τ hτ hCofinal hWeak
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, B, K, hB, hSamples, hEpsilon⟩

/-- Conditional compact weak-test uniqueness from genuine full-Hilbert
weak sequential convergence of the old physical velocity at zero. -/
theorem h3Audit_initialWeakL2Cofinal_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_compactWeakComparisonData
    hH3 (h3Audit_initialWeakL2Cofinal_implies_kineticAnchorData hH3 hData)

/-- The resulting strong physical L² initial trace and H³ upper trace are
outputs of the comparison argument, not hypotheses of this criterion. -/
theorem h3Audit_initialWeakL2Cofinal_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialWeakL2Cofinal_implies_kineticAnchorData hH3 hData)

/-- Retains the separate terminal actual-vorticity strong-H³ input. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialWeakL2Cofinal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCofinalKineticAnchors
    hH3 hClass i hPhysical
    (h3Audit_initialWeakL2Cofinal_implies_kineticAnchorData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
