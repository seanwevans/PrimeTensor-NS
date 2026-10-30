import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetPhysicalViscousGradientBudget244
import Mathlib.Tactic

/-!
# Physical gradient spikes forced by the critical all-orders logarithmic annular gate

A canonical spectral C¹ gradient envelope is only an upper bound on actual
velocity gradients. This file removes that gap. The complete PDE commutator
estimate works with ANY pointwise velocity-gradient envelope, once it is
spliced into the canonical envelope at a single physical time. Therefore
an assumed cap on all actual first spatial velocity derivatives at a
selected time also caps the exact positive normalized signed transport.

The unhalved fourth-power logarithmic radius gate, with coefficient
4(T-b), then forces at the SAME selected intermediate physical time a
real coordinate derivative to exceed c log(v(k)+1), for every fixed
c >= 0 with 4(T-b) * 4422 * c < 16m+3.

All higher-moment, source, cutoff, small-tolerance, and noncompressed-clock
requirements remain explicit; none is obtained from the physical PDE here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- At a SINGLE physical time, any actual pointwise upper bound for all
velocity-gradient components bounds the exact positive full-dissipation
transport growth. It need not agree with the canonical square-root-energy
envelope at any other time. -/
theorem h3Path_fullSignedExcess_le_arbitraryOneTimeActualGradientBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s H : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hAt : VelocityGradientEnvelope u (fun _ : ℝ => H) s) :
    h3PathFullDissipationTransportExcessRate u s ≤
      4422 * (1 + |H|) := by
  let h : ℝ → ℝ := fun q =>
    if q = s then H else h3PathCanonicalSqrtEnergyGradientEnvelope u q
  have hTail : ∀ q : ℝ, q ∈ Set.Ioo a T →
      VelocityGradientEnvelope u h q := by
    intro q hq i j x
    by_cases heq : q = s
    · subst q
      have hLocal := hAt i j x
      change abs (spatial3.d i (fun y =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u s y).component j) x) ≤ h s
      have hEval : h s = H := by
        simp only [h, if_pos rfl]
      rw [hEval]
      exact hLocal
    · have hCanonical :=
        (h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hq) i j x
      change abs (spatial3.d i (fun y =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u q y).component j) x) ≤ h q
      have hEval : h q = h3PathCanonicalSqrtEnergyGradientEnvelope u q := by
        simp only [h, if_neg heq]
      rw [hEval]
      exact hCanonical
  have hTransport : H3TransportCommutatorBoundAt u h 4422 s :=
    (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass hTail s hs).2
  have hNegative : -velocityH3TransportDerivativeAt u s ≤
      (4422 * (1 + |H|)) * velocityH3EnergyAt u s := by
    have hBound := neg_transport_le_of_commutatorBound hTransport
    simpa only [h, if_pos rfl] using hBound
  have hD : 0 ≤ velocityH3DissipationAt u s :=
    velocityH3DissipationAt_nonneg u s
  have hE : 0 < velocityH3EnergyAt u s :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  have hRaw : -velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s ≤
      (4422 * (1 + |H|)) * velocityH3EnergyAt u s := by
    linarith only [hNegative, hD]
  have hDiv : (-velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s) /
      velocityH3EnergyAt u s ≤ 4422 * (1 + |H|) :=
    (div_le_iff₀ hE).2 hRaw
  have hCoeff : 0 ≤ 4422 * (1 + |H|) := by positivity
  change max 0 ((-velocityH3TransportDerivativeAt u s -
    2 * velocityH3DissipationAt u s) /
      velocityH3EnergyAt u s) ≤ 4422 * (1 + |H|)
  exact max_le hCoeff hDiv

/-- With strictly positive signed excess, the same arbitrary local gradient
cap must pay both the growth rate and TWO viscous dissipation copies. -/
theorem h3Path_positiveFullExcess_add_viscousShare_le_actualGradientBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s H : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hPositive : 0 < h3PathFullDissipationTransportExcessRate u s)
    (hAt : VelocityGradientEnvelope u (fun _ : ℝ => H) s) :
    h3PathFullDissipationTransportExcessRate u s +
      2 * velocityH3DissipationAt u s /
        velocityH3EnergyAt u s ≤ 4422 * (1 + |H|) := by
  let z : ℝ := (-velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s) /
        velocityH3EnergyAt u s
  have hz : 0 < z := by
    by_contra hn
    have hzNonpos : z ≤ 0 := le_of_not_gt hn
    have hZero : h3PathFullDissipationTransportExcessRate u s = 0 := by
      change max 0 z = 0
      exact max_eq_left hzNonpos
    rw [hZero] at hPositive
    exact (not_lt_of_ge (le_refl (0 : ℝ))) hPositive
  have hRateEq : h3PathFullDissipationTransportExcessRate u s = z := by
    change max 0 z = z
    exact max_eq_right hz.le
  have hEPos : 0 < velocityH3EnergyAt u s :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  have hE : velocityH3EnergyAt u s ≠ 0 := ne_of_gt hEPos
  have hIdentity : h3PathFullDissipationTransportExcessRate u s +
      2 * velocityH3DissipationAt u s /
        velocityH3EnergyAt u s =
      (-velocityH3TransportDerivativeAt u s) /
        velocityH3EnergyAt u s := by
    rw [hRateEq]
    dsimp only [z]
    field_simp [hE]
    ring
  have hNonnegD : 0 ≤ velocityH3DissipationAt u s :=
    velocityH3DissipationAt_nonneg u s
  have hPDE : -velocityH3TransportDerivativeAt u s ≤
      (4422 * (1 + |H|)) * velocityH3EnergyAt u s := by
    let h : ℝ → ℝ := fun q =>
      if q = s then H else h3PathCanonicalSqrtEnergyGradientEnvelope u q
    have hTail : ∀ q : ℝ, q ∈ Set.Ioo a T →
        VelocityGradientEnvelope u h q := by
      intro q hq i j x
      by_cases heq : q = s
      · subst q
        have hLocal := hAt i j x
        change abs (spatial3.d i (fun y =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u s y).component j) x) ≤ h s
        have hEval : h s = H := by
          simp only [h, if_pos rfl]
        rw [hEval]
        exact hLocal
      · have hCanonical :=
          (h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hq) i j x
        change abs (spatial3.d i (fun y =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u q y).component j) x) ≤ h q
        have hEval : h q = h3PathCanonicalSqrtEnergyGradientEnvelope u q := by
          simp only [h, if_neg heq]
        rw [hEval]
        exact hCanonical
    have hBound := neg_transport_le_of_commutatorBound
      ((h3TransportControlledOnTail_of_h3Path_exactPDEPairing
        h3PathEnergyClassProducesPDEPairingIntegrability_closed
        hH3 hClass hTail s hs).2)
    simpa only [h, if_pos rfl] using hBound
  have hDiv : (-velocityH3TransportDerivativeAt u s) /
      velocityH3EnergyAt u s ≤ 4422 * (1 + |H|) :=
    (div_le_iff₀ hEPos).2 hPDE
  rw [hIdentity]
  exact hDiv

/-- Same conditional higher-budget canonical anchors now produce REAL
first-spatial-velocity-derivative spikes, not merely growth of a canonical
C¹ envelope. The coefficient uses the sharp UNHALVED logarithmic budget. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_actualGradientLogSpikes244
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
          ∀ c : ℝ, 0 ≤ c →
            4 * (T - b) * 4422 * c < ((16 * m + 3 : ℕ) : ℝ) →
          ∀ᶠ k : ℕ in atTop,
            ∃ s : ℝ, s ∈ Set.Ioo b (τ (v k)) ∧
              ∃ i j : Axis Depth.three, ∃ x : Point3,
                c * Real.log ((v k : ℝ) + 1) <
                  abs (spatial3.d i (loggedVelocityComponent u s j) x)) := by
  classical
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRadiusGate244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb c hc hcSmall
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let p : ℝ := ((16 * m + 3 : ℕ) : ℝ)
  let d : ℝ := T - b
  let Cb : ℝ := ((512 * ε ^ 2) ^ 4 * D ^ 5) *
    (2304 * velocityH3EnergyAt u b * S ^ 2 + 1) ^ 4
  let G : ℝ → ℝ := h3PathFullDissipationTransportExcessRate u
  have hδ : 0 < p - 4 * d * 4422 * c := by
    have hStrict : 4 * d * 4422 * c < p := by
      simpa only [p, d] using hcSmall
    linarith only [hStrict]
  have hd : 0 ≤ d := sub_nonneg.mpr hb.2.le
  have hLogTop : Tendsto (fun k : ℕ => Real.log (R k)) atTop atTop := by
    simpa only [R] using h3Path_strictMono_canonicalLogRadius_escape244 v hv
  have hRadialLarge : ∀ᶠ k : ℕ in atTop,
      (Real.log Cb + 4 * d * 4422 + 1) /
        (p - 4 * d * 4422 * c) ≤ Real.log (R k) :=
    hLogTop.eventually (eventually_ge_atTop _)
  have hLate := hHigher m F hF hFInt hUpper
    S D η ε hS hD hη hε hεη hSmall hCeil hCap hGeom b hb
  filter_upwards [hLate, hRadialLarge] with k hk hkLarge
  obtain ⟨s, hs, _hExactClock, hBudget⟩ := hk
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, lt_trans hs.2 (hτ (v k)).2⟩
  have hROne : 1 ≤ R k := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hLogNonneg : 0 ≤ Real.log (R k) := Real.log_nonneg hROne
  have hThresholdNonneg : 0 ≤ c * Real.log (R k) :=
    mul_nonneg hc hLogNonneg
  have hRadialStrict : Real.log Cb + 4 * d * 4422 <
      (p - 4 * d * 4422 * c) * Real.log (R k) := by
    have hScaled : Real.log Cb + 4 * d * 4422 + 1 ≤
        Real.log (R k) * (p - 4 * d * 4422 * c) :=
      (div_le_iff₀ hδ).1 hkLarge
    nlinarith only [hScaled]
  have hBudget' : p * Real.log (R k) ≤ Real.log Cb + 4 * d * G s := by
    simpa only [p, R, Cb, d, G] using hBudget
  refine ⟨s, hs, ?_⟩
  by_contra hNoGradient
  have hAt : VelocityGradientEnvelope u
      (fun _ : ℝ => c * Real.log (R k)) s := by
    intro i j x
    have hNot : ¬ c * Real.log (R k) <
        abs (spatial3.d i (loggedVelocityComponent u s j) x) := by
      intro hGreater
      exact hNoGradient ⟨i, j, x, hGreater⟩
    exact le_of_not_gt hNot
  have hPDE := h3Path_fullSignedExcess_le_arbitraryOneTimeActualGradientBound244
    hH3 hClass hsClass hAt
  have hPDE' : G s ≤ 4422 * (1 + c * Real.log (R k)) := by
    simpa only [G, abs_of_nonneg hThresholdNonneg] using hPDE
  have hCoefficient : 0 ≤ 4 * d := mul_nonneg (by norm_num) hd
  have hScaled := mul_le_mul_of_nonneg_left hPDE' hCoefficient
  nlinarith only [hBudget', hScaled, hRadialStrict]

end
end PrimeTensor.FirstMonomialTriad
