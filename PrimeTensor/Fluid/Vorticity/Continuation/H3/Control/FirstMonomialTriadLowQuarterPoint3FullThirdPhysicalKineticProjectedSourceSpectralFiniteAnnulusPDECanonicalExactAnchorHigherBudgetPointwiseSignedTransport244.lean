import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetSignedGrowthGate244
import Mathlib.Tactic

/-!
# Canonical higher-budget energy escape forces pointwise signed transport excess

The previous theorem transferred conditional all-orders spectral escape to
nonintegrability of the positive normalized H³ transport excess.  A more
pointwise statement follows directly from the exact H³ energy balance:

  E₃'(s) + 2 D₃(s) = -Transport₃(s).

An escaping physical H³ energy along a cofinal sequence cannot be
nonincreasing throughout any terminal subinterval.  Therefore every such
subinterval contains an actual physical time with

  2 D₃(s) < -Transport₃(s),

and thus strictly positive *full-dissipation* normalized transport excess.
The higher-moment, source ceiling, critical outer radius and terminal-clock
conditions remain explicit, and no positivity at a prescribed canonical
anchor or integrability estimate is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A differentiable scalar energy escaping at a sequence converging to the
terminal time must have a strictly positive derivative somewhere on EVERY
terminal subinterval.  No measurability of its derivative is needed. -/
theorem h3Path_scalar_cofinalEscape_forces_positiveDerivativeEveryTail244
    {E : ℝ → ℝ} {a T : ℝ} (t : ℕ → ℝ)
    (hDiff : DifferentiableOn ℝ E (Set.Ioo a T))
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hCofinal : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => E (t k)) atTop atTop) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ s : ℝ, s ∈ Set.Ioo b T ∧ 0 < deriv E s := by
  intro b hb
  by_contra hNone
  have hDerivNonpos (s : ℝ) (hs : s ∈ Set.Ioo b T) :
      deriv E s ≤ 0 := by
    apply le_of_not_gt
    intro hPositive
    exact hNone ⟨s, hs, hPositive⟩
  have hSub : Set.Ioo b T ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hDiffTail : DifferentiableOn ℝ E (Set.Ioo b T) :=
    hDiff.mono hSub
  have hAntitone : AntitoneOn E (Set.Ioo b T) := by
    refine antitoneOn_of_deriv_nonpos
      (convex_Ioo b T)
      hDiffTail.continuousOn
      (hDiffTail.mono interior_subset)
      ?_
    intro s hsInterior
    exact hDerivNonpos s (interior_subset hsInterior)
  let s₀ : ℝ := (b + T) / 2
  have hs₀ : s₀ ∈ Set.Ioo b T := by
    dsimp only [s₀]
    constructor <;> linarith only [hb.2]
  have hLate : ∀ᶠ k : ℕ in atTop, s₀ < t k :=
    hCofinal.eventually (Ioi_mem_nhds hs₀.2)
  have hLarge : ∀ᶠ k : ℕ in atTop, E s₀ + 1 ≤ E (t k) :=
    hEscape.eventually (eventually_ge_atTop (E s₀ + 1))
  obtain ⟨k, hkLate, hkLarge⟩ := (hLate.and hLarge).exists
  have hkTail : t k ∈ Set.Ioo b T :=
    ⟨lt_trans hs₀.1 hkLate, (ht k).2⟩
  have hUpper : E (t k) ≤ E s₀ :=
    hAntitone hs₀ hkTail (le_of_lt hkLate)
  linarith only [hkLarge, hUpper]

/-- Physical cofinal H³ energy escape forces actual transport to pay more
than both copies of H³ dissipation at a time on every terminal subinterval.
This does not say that the signed excess is positive at every time. -/
theorem h3Path_cofinalPhysicalEnergyEscape_forces_pointwiseSignedTransport244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hCofinal : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => velocityH3EnergyAt u (t k)) atTop atTop) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ s : ℝ, s ∈ Set.Ioo b T ∧
        2 * velocityH3DissipationAt u s <
          - velocityH3TransportDerivativeAt u s := by
  have hDiff : DifferentiableOn ℝ
      (velocityH3EnergyAt u) (Set.Ioo a T) := by
    intro s hs
    have hIds : H3OrderEnergyDerivativeIdentities u s :=
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3 a hClass s hs
    have hDeriv : HasDerivAt (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) s) s := by
      rw [deriv_velocityH3EnergyAt hIds]
      exact hasDerivAt_velocityH3EnergyAt hIds
    exact hDeriv.differentiableAt.differentiableWithinAt
  have hPositive :=
    h3Path_scalar_cofinalEscape_forces_positiveDerivativeEveryTail244
      t hDiff ht hCofinal hEscape
  intro b hb
  obtain ⟨s, hs, hDerivPos⟩ := hPositive b hb
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hsClass
  refine ⟨s, hs, ?_⟩
  linarith only [hBalance, hDerivPos]

/-- The pointwise transport overshoot above is a genuinely positive
full-dissipation normalized growth rate, with the exact physical energy in
the denominator. -/
theorem h3Path_signedTransportOvershoot_forces_positiveFullExcess244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s : ℝ)
    (hTransport : 2 * velocityH3DissipationAt u s <
      - velocityH3TransportDerivativeAt u s) :
    0 < h3PathFullDissipationTransportExcessRate u s := by
  have hEnergy : 0 < velocityH3EnergyAt u s :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  have hNumerator : 0 <
      - velocityH3TransportDerivativeAt u s -
        2 * velocityH3DissipationAt u s := by
    linarith only [hTransport]
  have hQuot : 0 <
      (- velocityH3TransportDerivativeAt u s -
          2 * velocityH3DissipationAt u s) /
        velocityH3EnergyAt u s :=
    div_pos hNumerator hEnergy
  unfold h3PathFullDissipationTransportExcessRate
  exact lt_of_lt_of_le hQuot (le_max_right _ _)

/-- The SAME first-crossing canonical windows from the all-orders
higher-budget spectral theorem now force pointwise signed transport
overshoots on every terminal subinterval. The original q^(4+m) moment
majorant, actual source ceiling, eighth-power critical cutoff, noncompressed
terminal clock and small tolerance are ALL still explicit premises. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_pointwiseSignedTransport244
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
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
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
            ∃ s : ℝ, s ∈ Set.Ioo b T ∧
              2 * velocityH3DissipationAt u s <
                - velocityH3TransportDerivativeAt u s ∧
              0 < h3PathFullDissipationTransportExcessRate u s) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_allOrdersCriticalBudget_spectralEnergyGate244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal,
    hτ, hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb
  obtain ⟨_hCost, hEnergyEscape, _hSpectralEscape⟩ :=
    hHigher m F hF hFInt hUpper S D η ε hS hD hη hε
      hεη hSmall hCeil hCap hGeom
  obtain ⟨s, hs, hTransport⟩ :=
    (h3Path_cofinalPhysicalEnergyEscape_forces_pointwiseSignedTransport244
      hH3 hClass (fun k => τ (v k))
      (fun k => hτ (v k)) hCofinal hEnergyEscape) b hb
  refine ⟨s, hs, hTransport, ?_⟩
  exact h3Path_signedTransportOvershoot_forces_positiveFullExcess244
    u s hTransport

end
end PrimeTensor.FirstMonomialTriad
