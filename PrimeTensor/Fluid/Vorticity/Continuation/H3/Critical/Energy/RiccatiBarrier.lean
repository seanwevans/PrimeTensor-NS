import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.LogRateBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Sqrt
import Mathlib.Tactic

/-!
# Exact physical H³ Riccati and gradient barriers forced by canonical logarithmic radii

The existing conditional logarithmic-radius lower bound requires an actual
normalized signed full-dissipation transport rate at an intermediate time.
The already-closed physical H³ energy estimate independently provides

  g(s) = max(0, E'(s)/E(s)) <= K sqrt(E(s)),
  K = h3PathSqrtEnergyRiccatiCoefficient.

The exact H³ transport commutator also bounds this rate by
4422*(1+|h(s)|), with h the canonical H³ spectral C¹ gradient envelope.
Combining those genuine PDE bounds with the critical radius gate forces a
logarithmic radial cost on the intermediate physical H³ energy, and excludes
an eventual uniformly subcritical square-root-energy ceiling on the intervals.

All original higher-order radial, source, cutoff and clock hypotheses remain
explicit. The canonical gradient ENVELOPE is an upper majorant of actual
pointwise gradients, so its necessary growth is not asserted to be a lower
bound on the actual gradient itself.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The positive full-dissipation signed transport rate is bounded by the
actual closed Riccati-scale H³ PDE estimate, with no new hypotheses. -/
theorem h3Path_fullSignedExcess_le_physicalRiccatiSqrtEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    h3PathFullDissipationTransportExcessRate u s ≤
      h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) := by
  have hCoeff : 0 ≤ h3PathSqrtEnergyRiccatiCoefficient *
      Real.sqrt (velocityH3EnergyAt u s) :=
    mul_nonneg h3PathSqrtEnergyRiccatiCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hGrowth := deriv_velocityH3EnergyAt_le_sqrtEnergy_mul_energy
    hH3 hClass hs
  calc
    h3PathFullDissipationTransportExcessRate u s =
        h3PathPositiveEnergyGrowthRate u s :=
      h3PathFullDissipationTransportExcessRate_eq_positiveEnergyGrowthRate
        hH3 hClass hs
    _ ≤ h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) :=
      h3PathPositiveEnergyGrowthRate_le_of_deriv_bound
        (c := fun _ : ℝ => h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u s))
        hCoeff hGrowth

/-- The same exact rate is bounded by the established complete physical
H³ transport commutator with the concrete spectral C¹ gradient envelope.
This is a bound on the envelope, not a converse pointwise gradient estimate. -/
theorem h3Path_fullSignedExcess_le_physicalGradientEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    h3PathFullDissipationTransportExcessRate u s ≤
      4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|) := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hTransport : H3TransportCommutatorBoundAt u h 4422 s :=
    (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass
      (fun t ht => h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht)
      s hs).2
  have hNeg : -velocityH3TransportDerivativeAt u s ≤
      4422 * (1 + |h s|) * velocityH3EnergyAt u s :=
    neg_transport_le_of_commutatorBound hTransport
  have hD : 0 ≤ velocityH3DissipationAt u s :=
    velocityH3DissipationAt_nonneg u s
  have hE : 0 < velocityH3EnergyAt u s :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  have hRaw : -velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s ≤
      (4422 * (1 + |h s|)) * velocityH3EnergyAt u s := by
    linarith only [hNeg, hD]
  have hDiv : (-velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s) / velocityH3EnergyAt u s ≤
      4422 * (1 + |h s|) :=
    (div_le_iff₀ hE).2 hRaw
  have hCoef : 0 ≤ 4422 * (1 + |h s|) := by positivity
  change max 0 ((-velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s) / velocityH3EnergyAt u s) ≤
      4422 * (1 + |h s|)
  exact max_le hCoef hDiv

/-- The identical conditional canonical first-crossing witnesses force the
actual intermediate H³ energy to carry a logarithmic radius cost. A matching
bound on the C¹ gradient ENVELOPE is supplied by the complete nonlinear PDE
commutator. The sharp proposed sqrt-energy ceiling is excluded using the
unhalved logarithmic rate barrier from the committed parent. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_physicalRiccatiLogBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
    ∃ hτ : (∀ n, τ n ∈ Set.Ioo a T),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S D η ε : ℝ,
          0 ≤ S → 0 ≤ D → 0 < η → 0 < ε → ε < η →
          16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1 →
          (∀ᶠ k : ℕ in atTop, C (v k) ≤ S) →
          (∀ᶠ k : ℕ in atTop,
            ((N (v k) : ℝ) + 2) ^ 8 ≤ D * ((v k : ℝ) + 1) ^ 9) →
          (∀ᶠ k : ℕ in atTop,
            η ≤ ((v k : ℝ) + 1) ^ (2 * m + 3) * ((T - τ (v k)) / 4)) →
          ∀ b : ℝ, b ∈ Set.Ioo a T →
            (∀ᶠ k : ℕ in atTop,
              ∃ s : ℝ, s ∈ Set.Ioo b (τ (v k)) ∧
                ((16 * m + 3 : ℕ) : ℝ) *
                  Real.log ((v k : ℝ) + 1) ≤
                  8 * (T - b) *
                    (h3PathSqrtEnergyRiccatiCoefficient *
                      Real.sqrt (velocityH3EnergyAt u s)) ∧
                ((16 * m + 3 : ℕ) : ℝ) *
                  Real.log ((v k : ℝ) + 1) ≤
                  8 * (T - b) *
                    (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|))) ∧
            (∀ c : ℝ,
              4 * (T - b) *
                (h3PathSqrtEnergyRiccatiCoefficient * c) <
                  ((16 * m + 3 : ℕ) : ℝ) →
              ¬ (∀ᶠ k : ℕ in atTop,
                ∀ s : ℝ, s ∈ Set.Ioo b (τ (v k)) →
                  Real.sqrt (velocityH3EnergyAt u s) ≤
                    c * Real.log ((v k : ℝ) + 1)))) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRateBarrier244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb
  obtain ⟨hRateLate, hForbidden⟩ :=
    hHigher m F hF hFInt hUpper S D η ε hS hD hη hε
      hεη hSmall hCeil hCap hGeom b hb
  have hGapNonneg : 0 ≤ 8 * (T - b) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hb.2.le)
  constructor
  · filter_upwards [hRateLate] with k hk
    obtain ⟨s, hs, hRateLower⟩ := hk
    have hsClass : s ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hs.1, lt_trans hs.2 (hτ (v k)).2⟩
    have hPDE := h3Path_fullSignedExcess_le_physicalRiccatiSqrtEnergy244
      hH3 hClass hsClass
    have hGradient := h3Path_fullSignedExcess_le_physicalGradientEnvelope244
      hH3 hClass hsClass
    have hScaledPDE := mul_le_mul_of_nonneg_left hPDE hGapNonneg
    have hScaledGradient := mul_le_mul_of_nonneg_left hGradient hGapNonneg
    exact ⟨s, hs, hRateLower.trans hScaledPDE,
      hRateLower.trans hScaledGradient⟩
  · intro c hc hCap
    have hRateCap : ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Ioo b (τ (v k)) →
          h3PathFullDissipationTransportExcessRate u s ≤
            (h3PathSqrtEnergyRiccatiCoefficient * c) *
              Real.log ((v k : ℝ) + 1) := by
      filter_upwards [hCap] with k hk s hs
      have hsClass : s ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 hs.1, lt_trans hs.2 (hτ (v k)).2⟩
      have hPDE := h3Path_fullSignedExcess_le_physicalRiccatiSqrtEnergy244
        hH3 hClass hsClass
      have hScaled := mul_le_mul_of_nonneg_left (hk s hs)
        h3PathSqrtEnergyRiccatiCoefficient_nonneg
      calc
        h3PathFullDissipationTransportExcessRate u s ≤
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) := hPDE
        _ ≤ h3PathSqrtEnergyRiccatiCoefficient *
              (c * Real.log ((v k : ℝ) + 1)) := hScaled
        _ = (h3PathSqrtEnergyRiccatiCoefficient * c) *
              Real.log ((v k : ℝ) + 1) := by ring
    exact (hForbidden (h3PathSqrtEnergyRiccatiCoefficient * c) hc)
      hRateCap

end
end PrimeTensor.FirstMonomialTriad
