import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialWeakL2CofinalKineticControl

/-!
# Pointwise bounded weak tests replace sequential weak convergence

The preceding initial comparison assumed convergence of every physical L²
pairing along one cofinal positive-time sequence. That is stronger than the
input consumed by the uniform boundedness principle. Here we retain only

  ∀ ψ ∈ L²(ℝ³)^3, ∃ Cψ < ∞, ∀ n, |⟪u(τ n), ψ⟫| ≤ Cψ.

Banach–Steinhaus bounds the whole Hilbert norm on that sequence. The *actual*
zeroth-order kinetic norm identity and positive-time kinetic antitonicity then
bound the old physical velocity throughout the initial interval. No weak
limit (not even an unspecified one) is required for this kinetic step.

Conversely, if the actual kinetic energy tends to +∞ at t = 0+, then every
cofinal positive-time sequence has a fixed physical L² test against which its
pairings are unbounded. This does NOT say that a compact Schwartz test must
see the escape: the witness is in the complete physical Hilbert space.

The vanishing old/selected relative-energy residual remains a separate PDE
hypothesis. The terminal actual-vorticity strong-H³ endpoint is separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Pointwise bounded *full-Hilbert* weak pairings along one cofinal sequence
imply cofinally bounded actual kinetic-energy samples. No pairing limit is
assumed, and the velocity is the genuine positive-time physical old field. -/
theorem h3Audit_initialPointwiseWeakPairings_kineticAnchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hbT : b ≤ T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) b)
    (hCofinal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) t)
    (hPairBound : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      ∃ C : ℝ, ∀ n : ℕ,
        ‖((innerSL ℝ)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧
          velocityH3Energy0At u s ≤ B := by
  obtain ⟨M, _hM, hNorm⟩ :=
    h3Audit_initialWeakPairingBoundedSequence_normBounded
      (fun n => h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
      hPairBound
  refine ⟨M ^ 2, sq_nonneg M, ?_⟩
  intro t ht
  obtain ⟨n, hn⟩ := hCofinal t ht
  refine ⟨τ n, hn, ?_⟩
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

/-- Once the weak pairings are pointwise bounded on a cofinal sequence,
positive-time kinetic antitonicity yields the old physical L² ceiling at
*every* time of the initial interval, not merely along the sequence. -/
theorem h3Audit_initialPointwiseWeakPairings_uniformOldL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hbT : b ≤ T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) b)
    (hCofinal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) t)
    (hPairBound : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      ∃ C : ℝ, ∀ n : ℕ,
        ‖((innerSL ℝ)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ Real.sqrt B := by
  obtain ⟨B, hB, hSamples⟩ :=
    h3Audit_initialPointwiseWeakPairings_kineticAnchors
      hH3 b hbT τ hτ hCofinal hPairBound
  exact ⟨B, hB,
    h3Audit_initialOldPhysicalHilbert_norm_le_of_cofinalKineticAnchors
      hH3 b B hbT hSamples⟩

/-- A genuinely diverging initial kinetic energy forces an unbounded weak
pairing with ONE fixed full-Hilbert test along ANY cofinal positive-time
sequence. This is the contrapositive of Banach–Steinhaus plus antitonicity. -/
theorem h3Audit_initialKineticEscape_fixedUnboundedWeakProbe
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b ≤ T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) b)
    (hCofinal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ∃ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) t)
    (hEscape : Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ)) atTop) :
    ∃ ψ : H3PhysicalRealFinVectorL2Hilbert,
      ∀ C : ℝ, ∃ n : ℕ,
        C < ‖((innerSL ℝ)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ‖ := by
  classical
  by_contra hNoProbe
  push_neg at hNoProbe
  have hPairBound : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      ∃ C : ℝ, ∀ n : ℕ,
        ‖((innerSL ℝ)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ‖ ≤ C := by
    simpa only [not_lt] using hNoProbe
  obtain ⟨B, _hB, hSamples⟩ :=
    h3Audit_initialPointwiseWeakPairings_kineticAnchors
      hH3 b hbT τ hτ hCofinal hPairBound
  have hCeiling := h3Audit_initialKineticEnergy_le_of_cofinalAnchors
    hH3 b B hbT hSamples
  have hLarge : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      B + 1 ≤ velocityH3Energy0At u t :=
    (tendsto_atTop.1 hEscape) (B + 1)
  have hNear : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  obtain ⟨t, htLarge, htNear⟩ := (hLarge.and hNear).exists
  linarith [hCeiling t htNear]

/-- Initial-value comparison data requiring merely pointwise bounded weak
pairings on one cofinal sequence. Neither a weak limit nor an explicit
kinetic-energy ceiling or time-average is supplied. The genuinely separate
vanishing PDE residual remains a hypothesis. -/
def H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData
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
        ∃ C : ℝ, ∀ n : ℕ,
          ‖((innerSL ℝ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ‖ ≤ C) ∧
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

/-- The new, weaker pointwise-weak-boundedness data imply the cofinal kinetic
anchor data of the already-proved initial comparison theorem. -/
theorem h3Audit_initialPointwiseWeakPairing_implies_kineticAnchorData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCofinalKineticAnchorsRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, τ, K, hτ, hCofinal, hPairBound, hEpsilon⟩ := hData
  obtain ⟨B, hB, hSamples⟩ :=
    h3Audit_initialPointwiseWeakPairings_kineticAnchors
      hH3 b hbT.le τ hτ hCofinal hPairBound
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, B, K, hB, hSamples, hEpsilon⟩

/-- Recover the weaker data from the previous strong assumption of a genuine
weak L² limit. This proves the new criterion really is a hypothesis reduction. -/
theorem h3Audit_initialWeakL2Cofinal_implies_pointwiseWeakPairingData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData hH3) :
    H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, τ, K, hτ, hCofinal, hWeak, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, τ, K, hτ, hCofinal, ?_, hEpsilon⟩
  intro ψ
  exact h3Audit_initialScalarSequence_normBounded_of_tendsto
    (fun n =>
      ((innerSL ℝ) (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))) ψ)
    (((innerSL ℝ)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ψ)
    (hWeak ψ)

/-- The same compact initial weak uniqueness conclusion as before, now under
pointwise boundedness of weak pairings instead of convergence of pairings. -/
theorem h3Audit_initialPointwiseWeakPairing_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_compactWeakComparisonData
    hH3 (h3Audit_initialPointwiseWeakPairing_implies_kineticAnchorData
      hH3 hData)

/-- Initial physical L² and H³ upper traces are conclusions, not weak
pairing convergence hypotheses. -/
theorem h3Audit_initialPointwiseWeakPairing_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialCofinalKineticAnchors_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialPointwiseWeakPairing_implies_kineticAnchorData
      hH3 hData)

/-- The terminal actual-vorticity strong-H³ endpoint is still an independent
premise; this initial hypothesis reduction does not modify it. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPointwiseWeakPairing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData hH3) :
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
    (h3Audit_initialPointwiseWeakPairing_implies_kineticAnchorData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
