import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialBochnerDerivativeKineticControl

/-!
# Initial kinetic control from scalar weak FTC for every physical L² probe

The preceding criterion used a Bochner-integrable, full physical L²-valued
strong temporal derivative to manufacture a finite initial kinetic trace.
That assumption is stronger than the kinetic input needed by the existing
relative-energy comparison.

Instead, for every FIXED probe `ψ` in the complete physical velocity L²
Hilbert space, assume only a real-valued, integrable temporal source `gψ`
and the exact scalar increment identity between two STRICTLY POSITIVE times:

  inner(u(t), ψ) - inner(u(s), ψ) = ∫_s^t gψ(r) dr.

The source is allowed to depend on `ψ`; there is no assumption of a single
L²-valued Bochner source, no prescribed weak initial trace, and no energy
bound at time zero. Scalar absolute continuity on `(0,b)` produces a finite
scalar right limit for each test. Along any positive sequence tending to
zero, all pairings therefore have bounded scalar sequences. Banach–Steinhaus,
the exact physical kinetic identity and positive-time kinetic antitonicity
supply the missing initial old-velocity L² ceiling.

The initial Fourier datum and epsilon-vanishing OLD/SELECTED relative-energy
comparison remain explicit hypotheses. In particular, the scalar FTC for
EVERY physical L² test is not deduced from distributional compact-test
identities alone. A separate terminal actual-vorticity strong-H³ endpoint
is still required for the whole-time transverse conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Scalar `L¹` increments between two positive times have a finite right
limit, whose value is NOT prescribed at the initial endpoint. No
norm-valued derivative or strong trace is used here. -/
theorem h3Audit_initialScalarIntegrableIncrements_exists_rightLimit
    (F g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hG : IntervalIntegrable g volume 0 b)
    (hIncrements : ∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
      F t - F s = ∫ r in s..t, g r) :
    ∃ L : ℝ, Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let q : ℝ := b / 2
  have hq : q ∈ Set.Ioo (0 : ℝ) b := by
    dsimp only [q]
    constructor <;> linarith
  let L : ℝ := F q - ∫ r in (0 : ℝ)..q, g r
  have hLocal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      IntervalIntegrable g volume 0 t := by
    intro t ht
    apply hG.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) t := by
      simpa only [Set.uIcc_of_le ht.1.le] using hx
    have hxb : x ∈ Set.Icc (0 : ℝ) b :=
      ⟨hx'.1, hx'.2.trans ht.2.le⟩
    simpa only [Set.uIcc_of_le hb.le] using hxb
  have hOn (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
      F t = L + ∫ r in (0 : ℝ)..t, g r := by
    have hInc := hIncrements q t hq ht
    have hInt :
        (∫ r in q..t, g r) =
          (∫ r in (0 : ℝ)..t, g r) -
          (∫ r in (0 : ℝ)..q, g r) :=
      (intervalIntegral.integral_interval_sub_left
        (hLocal t ht) (hLocal q hq)).symm
    rw [hInt] at hInc
    calc
      F t = (F t - F q) + F q := by ring
      _ = ((∫ r in (0 : ℝ)..t, g r) -
          (∫ r in (0 : ℝ)..q, g r)) + F q := by rw [hInc]
      _ = L + ∫ r in (0 : ℝ)..t, g r := by dsimp only [L]; ring
  have hContinuousU :
      ContinuousOn (fun t : ℝ => ∫ r in (0 : ℝ)..t, g r)
        (Set.uIcc (0 : ℝ) b) :=
    intervalIntegral.continuousOn_primitive_interval' hG left_mem_uIcc
  have hContinuous :
      ContinuousOn (fun t : ℝ => ∫ r in (0 : ℝ)..t, g r)
        (Set.Icc (0 : ℝ) b) := by
    simpa only [Set.uIcc_of_le hb.le] using hContinuousU
  have hPrimitive :
      Tendsto (fun t : ℝ => ∫ r in (0 : ℝ)..t, g r)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using h3Audit_rightTendsto_of_continuousOn_initialIcc
      (fun t : ℝ => ∫ r in (0 : ℝ)..t, g r) hb hContinuous
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq : F =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, g r) := by
    filter_upwards [hStrict] with t ht
    exact hOn t ht
  have hPlus :
      Tendsto (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, g r)
        (𝓝[>] (0 : ℝ)) (𝓝 (L + (0 : ℝ))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => L)
      (𝓝[>] (0 : ℝ)) (𝓝 L)).add hPrimitive
  refine ⟨L, ?_⟩
  have hPlus' :
      Tendsto (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, g r)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa only [add_zero] using hPlus
  exact hPlus'.congr' hEq.symm

/-- A genuinely right-zero convergent positive-time sample sequence is
cofinal inside every strict initial interval. -/
theorem h3Audit_initialPositiveSequence_cofinal_of_rightTendsto
    (τ : ℕ → ℝ) (b : ℝ)
    (hTime : Tendsto τ atTop (𝓝[>] (0 : ℝ))) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) t := by
  intro t ht
  have hNear : ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
      s ∈ Set.Ioo (0 : ℝ) t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ht.1)] with s hs0 hst
    exact ⟨hs0, hst⟩
  obtain ⟨n, hn⟩ := (hTime.eventually hNear).exists
  exact ⟨n, hn⟩

/-- For each fixed complete-Hilbert test, the scalar positive-time FTC is
allowed to have its own `L¹` source. This is NOT an `L¹_t L²_x` hypothesis. -/
def H3AuditInitialFullL2ScalarWeakFTCOn
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) : Prop :=
  ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
    ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume 0 b ∧
      ∀ (s t : ℝ),
        s ∈ Set.Ioo (0 : ℝ) b →
        t ∈ Set.Ioo (0 : ℝ) b →
        ((innerSL ℝ) (F t)) ψ - ((innerSL ℝ) (F s)) ψ =
          ∫ r in s..t, g r

/-- Scalar-integrable weak FTC for every physical L² test produces
pointwise bounded pairings along a right-zero-convergent sequence. Uniform
control IN THE TEST VARIABLE is manufactured by Banach–Steinhaus later. -/
theorem h3Audit_initialFullL2ScalarWeakFTC_pairingsBoundedOnSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hFTC : H3AuditInitialFullL2ScalarWeakFTCOn F b)
    (τ : ℕ → ℝ)
    (hTime : Tendsto τ atTop (𝓝[>] (0 : ℝ))) :
    ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      ∃ C : ℝ, ∀ n : ℕ,
        ‖((innerSL ℝ) (F (τ n))) ψ‖ ≤ C := by
  intro ψ
  obtain ⟨g, hG, hIncrement⟩ := hFTC ψ
  obtain ⟨L, hRight⟩ :=
    h3Audit_initialScalarIntegrableIncrements_exists_rightLimit
      (fun t : ℝ => ((innerSL ℝ) (F t)) ψ)
      g b hb hG hIncrement
  exact h3Audit_initialScalarSequence_normBounded_of_tendsto
    (fun n : ℕ => ((innerSL ℝ) (F (τ n))) ψ)
    L (hRight.comp hTime)

/-- The actual old velocity's integrable scalar evolution for every L²
test supplies cofinal bounded *physical* kinetic-energy samples. -/
theorem h3Audit_initialFullL2ScalarWeakFTC_kineticAnchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b ≤ T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) b)
    (hTime : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hFTC : H3AuditInitialFullL2ScalarWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3) b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
          velocityH3Energy0At u s ≤ B := by
  exact h3Audit_initialPointwiseWeakPairings_kineticAnchors
    hH3 b hbT τ hτ
    (h3Audit_initialPositiveSequence_cofinal_of_rightTendsto
      τ b hTime)
    (h3Audit_initialFullL2ScalarWeakFTC_pairingsBoundedOnSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      b hb hFTC τ hTime)

/-- PDE-facing initial data with scalar weak time derivatives only, allowing
a different `L¹` source for every test. Neither a weak initial trace nor a
full physical Bochner derivative nor a kinetic right limit is assumed. -/
def H3AuditInitialCanonicalScalarWeakFTCRelativeEnergyData
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
      Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
      H3AuditInitialFullL2ScalarWeakFTCOn
        (h3AuditInitialOldPhysicalHilbertTotal hH3) b ∧
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

/-- Scalar weak temporal FTC removes the separate full-Hilbert pointwise
pairing-bound hypothesis used by the preceding kinetic-control criterion. -/
theorem h3Audit_initialScalarWeakFTC_implies_pointwisePairingData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalScalarWeakFTCRelativeEnergyData hH3) :
    H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, τ, K, hτ, hTime, hFTC, hEpsilon⟩ := hData
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, τ, K, hτ,
    h3Audit_initialPositiveSequence_cofinal_of_rightTendsto τ b hTime,
    h3Audit_initialFullL2ScalarWeakFTC_pairingsBoundedOnSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      b hb hFTC τ hTime,
    hEpsilon⟩

/-- Under the still-explicit relative-energy comparison, scalar weak FTC
forces compact weak-test initial uniqueness without a strong L² derivative. -/
theorem h3Audit_initialScalarWeakFTC_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalScalarWeakFTCRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialPointwiseWeakPairing_implies_compactWeakComparisonData
    hH3 (h3Audit_initialScalarWeakFTC_implies_pointwisePairingData hH3 hData)

/-- Initial physical L² and upper H³ traces follow conditionally from the
same scalar evolution and nonlinear comparison premises. -/
theorem h3Audit_initialScalarWeakFTC_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalScalarWeakFTCRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialPointwiseWeakPairing_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialScalarWeakFTC_implies_pointwisePairingData hH3 hData)

/-- The whole-time two-coordinate intrinsic Sobolev estimate still needs
the independent actual-vorticity strong-H³ terminal condition. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarWeakFTC
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalScalarWeakFTCRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPointwiseWeakPairing
    hH3 hClass i hPhysical
    (h3Audit_initialScalarWeakFTC_implies_pointwisePairingData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
