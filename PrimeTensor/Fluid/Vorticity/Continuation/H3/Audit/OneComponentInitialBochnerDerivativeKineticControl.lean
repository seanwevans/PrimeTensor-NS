import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPointwiseWeakPairingControl
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPositiveStrongDerivative

/-!
# Initial kinetic control from an integrable physical L² time derivative

A strongly integrable temporal velocity derivative on `(0,b)` and genuine
positive-time Bochner evolution produce a finite strong physical L² right
limit *without* presupposing the value of that limit or a weak initial trace.

The exact zeroth-order energy identity then supplies a finite kinetic-energy
right limit, which excludes initial kinetic escape and gives the uniform old
velocity bound needed by the existing old/selected relative-energy comparison.

The full-L² temporal derivative and the vanishing comparison residual are
still independent PDE obligations. In particular the H³ path class alone
only guarantees positive-time regularity, not integrability at the initial
endpoint. We do not infer the value of the right trace from the time-zero
velocity definition; initial identification remains a comparison conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A Bochner `L¹` temporal source on an initial interval has a primitive
vanishing strongly at its right-zero endpoint. This is valid for the entire
three-component *physical* L² Hilbert space. -/
theorem h3Audit_initialHilbertBochnerPrimitive_tendsto_zero
    (V : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hV : IntervalIntegrable V volume 0 b) :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : H3PhysicalRealFinVectorL2Hilbert)) := by
  have hContinuousU :
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s)
        (Set.uIcc (0 : ℝ) b) :=
    intervalIntegral.continuousOn_primitive_interval'
      hV left_mem_uIcc
  have hContinuous :
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s)
        (Set.Icc (0 : ℝ) b) := by
    simpa only [Set.uIcc_of_le hb.le] using hContinuousU
  have hRight := h3Audit_rightTendsto_of_continuousOn_initialIcc
    (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s) hb hContinuous
  simpa using hRight

/-- Positive-time Bochner increments imply a finite strong right L² limit,
without a weak right trace or a prescribed initial endpoint value. -/
theorem h3Audit_initialHilbertBochnerIncrements_exists_strongRightLimit
    (F V : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hV : IntervalIntegrable V volume 0 b)
    (hIncrements : ∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
      F t - F s = ∫ r in s..t, V r) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let q : ℝ := b / 2
  have hq : q ∈ Set.Ioo (0 : ℝ) b := by
    dsimp only [q]
    constructor <;> linarith
  let L : H3PhysicalRealFinVectorL2Hilbert :=
    F q - ∫ r in (0 : ℝ)..q, V r
  have hLocal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      IntervalIntegrable V volume 0 t := by
    intro t ht
    apply hV.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) t := by
      simpa only [Set.uIcc_of_le ht.1.le] using hx
    have hxb : x ∈ Set.Icc (0 : ℝ) b :=
      ⟨hx'.1, hx'.2.trans ht.2.le⟩
    simpa only [Set.uIcc_of_le hb.le] using hxb
  have hOn (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
      F t = L + ∫ r in (0 : ℝ)..t, V r := by
    have hInc := hIncrements q t hq ht
    have hInt :
        (∫ r in q..t, V r) =
          (∫ r in (0 : ℝ)..t, V r) -
          (∫ r in (0 : ℝ)..q, V r) :=
      (intervalIntegral.integral_interval_sub_left
        (hLocal t ht) (hLocal q hq)).symm
    rw [hInt] at hInc
    calc
      F t = (F t - F q) + F q := by abel
      _ = ((∫ r in (0 : ℝ)..t, V r) -
          (∫ r in (0 : ℝ)..q, V r)) + F q := by rw [hInc]
      _ = L + ∫ r in (0 : ℝ)..t, V r := by dsimp only [L]; abel
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq : F =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, V r) := by
    filter_upwards [hStrict] with t ht
    exact hOn t ht
  have hPrim :=
    h3Audit_initialHilbertBochnerPrimitive_tendsto_zero V b hb hV
  have hPlus :
      Tendsto (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, V r)
        (𝓝[>] (0 : ℝ))
        (𝓝 (L + (0 : H3PhysicalRealFinVectorL2Hilbert))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => L)
      (𝓝[>] (0 : ℝ)) (𝓝 L)).add hPrim
  refine ⟨L, ?_⟩
  have hPlus' :
      Tendsto (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, V r)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa only [add_zero] using hPlus
  exact hPlus'.congr' hEq.symm

/-- A single initial Bochner integral and the actual strong interior
physical-velocity derivative give the two-time increment identities. -/
theorem h3Audit_initialHilbertStrongDerivative_implies_increments
    (F V : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hV : IntervalIntegrable V volume 0 b)
    (hDeriv : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt F (V t) t)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    F t - F s = ∫ r in s..t, V r := by
  have hSub : Set.uIcc s t ⊆ Set.uIcc (0 : ℝ) b := by
    intro x hx
    have hxb :=
      h3Audit_positiveUnorderedInterval_subset_initial b s t hs ht hx
    simpa only [Set.uIcc_of_le hb.le] using hxb
  have hIntegrable : IntervalIntegrable V volume s t :=
    hV.mono_set hSub
  have hFTC : (∫ r in s..t, V r) = F t - F s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hDeriv x
        (h3Audit_positiveUnorderedInterval_strict b s t hs ht hx))
      hIntegrable
  exact hFTC.symm

/-- The genuine positive-time old physical velocity acquires a finite
strong right L² limit without assuming any initial weak convergence. -/
theorem h3Audit_initialOldHilbertStrongDerivative_exists_rightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b)
    (V : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (hV : IntervalIntegrable V volume 0 b)
    (hDeriv : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (V t) t) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  apply h3Audit_initialHilbertBochnerIncrements_exists_strongRightLimit
    (h3AuditInitialOldPhysicalHilbertTotal hH3) V b hb hV
  intro s t hs ht
  exact h3Audit_initialHilbertStrongDerivative_implies_increments
    (h3AuditInitialOldPhysicalHilbertTotal hH3) V
    b hb hV hDeriv s t hs ht

/-- The exact physical kinetic norm identity transfers that strong initial
L² limit to a finite right limit of the ACTUAL kinetic energy. The limit is
not identified with `velocityH3Energy0At u 0` here. -/
theorem h3Audit_initialOldHilbertStrongDerivative_kineticRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b ≤ T)
    (V : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (hV : IntervalIntegrable V volume 0 b)
    (hDeriv : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (V t) t) :
    ∃ E : ℝ,
      Tendsto (velocityH3Energy0At u)
        (𝓝[>] (0 : ℝ)) (𝓝 E) := by
  obtain ⟨L, hL⟩ :=
    h3Audit_initialOldHilbertStrongDerivative_exists_rightLimit
      hH3 b hb V hV hDeriv
  have hNorm :
      Tendsto (fun t : ℝ =>
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖L‖ ^ 2)) :=
    (continuous_norm.pow 2).continuousAt.tendsto.comp hL
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq : (velocityH3Energy0At u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2) := by
    filter_upwards [hStrict] with t ht
    have htT : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨ht.1, lt_of_lt_of_le ht.2 hbT⟩
    exact (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t htT).symm
  exact ⟨‖L‖ ^ 2, hNorm.congr' hEq.symm⟩

/-- Concrete derivative-side sufficient initial data. An integrable
physical L² derivative replaces *both* the assumed weak sequential test
bounds and the kinetic-energy initial trace. The relative-energy residual
remains independent. -/
def H3AuditInitialCanonicalBochnerDerivativeRelativeEnergyData
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
    ∃ (V : ℝ → H3PhysicalRealFinVectorL2Hilbert) (K : ℝ),
      IntervalIntegrable V volume 0 b ∧
      (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
          (V t) t) ∧
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

/-- Produce the earlier right-kinetic-trace comparison data from a genuine
physical L²-valued time derivative, without identifying its right endpoint. -/
theorem h3Audit_initialBochnerDerivative_implies_rightKineticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalBochnerDerivativeRelativeEnergyData hH3) :
    H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, V, K, hV, hDeriv, hEpsilon⟩ := hData
  obtain ⟨E, hRight⟩ :=
    h3Audit_initialOldHilbertStrongDerivative_kineticRightLimit
      hH3 b hb hbT.le V hV hDeriv
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, E, K, hRight, hEpsilon⟩

/-- Initial compact weak-test uniqueness follows from the physical
integrable-derivative criterion and the independent nonlinear comparison. -/
theorem h3Audit_initialBochnerDerivative_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalBochnerDerivativeRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialRightKineticTrace_implies_compactWeakComparisonData
    hH3 (h3Audit_initialBochnerDerivative_implies_rightKineticData hH3 hData)

/-- Initial physical L² and upper H³ right traces are *consequences* of the
comparison. Neither was assumed to identify the Bochner right limit. -/
theorem h3Audit_initialBochnerDerivative_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalBochnerDerivativeRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialRightKineticTrace_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialBochnerDerivative_implies_rightKineticData hH3 hData)

/-- The transverse whole-time Sobolev result retains the independent
actual-vorticity strong-H³ terminal endpoint assumption. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialBochnerDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalBochnerDerivativeRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightKineticTrace
    hH3 hClass i hPhysical
    (h3Audit_initialBochnerDerivative_implies_rightKineticData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
