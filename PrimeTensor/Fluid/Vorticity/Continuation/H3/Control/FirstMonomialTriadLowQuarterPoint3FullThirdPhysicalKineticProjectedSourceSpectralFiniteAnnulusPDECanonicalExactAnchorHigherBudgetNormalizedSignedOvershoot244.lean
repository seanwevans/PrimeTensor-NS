import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetRawSignedOvershoot244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Log
import Mathlib.Tactic

/-!
# Higher-budget canonical energy escape forces unbounded normalized signed H³ transport

The committed raw margin theorem proves -Transport₃ - 2 D₃ is unbounded
on each terminal tail under the canonical all-orders higher-budget assumptions.
The stronger normalized assertion follows from cofinal escape of log E₃.
For each finite M ≥ 0, a late logarithmic-energy secant has slope > M.
The mean-value theorem supplies a time where E₃'/E₃ > M. The exact signed
Navier–Stokes balance identifies this as (-Transport₃ - 2 D₃)/E₃ > M.

This is a pointwise tail-unboundedness theorem, not an L¹ estimate.
It retains every optional higher-moment, projected-source, outer-cutoff,
small-epsilon and noncompressed terminal-clock assumption of its parent.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Positive scalar energy with a cofinal escape sequence forces its
LOGARITHMIC derivative to exceed every fixed nonnegative M somewhere on
every terminal subinterval. The proof applies the committed raw-derivative
secant theorem to log E and adds no derivative-measurability assumption. -/
theorem h3Path_scalar_cofinalEscape_forces_unboundedLogDerivativeEveryTail244
    {E : ℝ → ℝ} {a T : ℝ} (t : ℕ → ℝ)
    (hDeriv : ∀ s : ℝ, s ∈ Set.Ioo a T →
      HasDerivAt E (deriv E s) s)
    (hPositive : ∀ s : ℝ, s ∈ Set.Ioo a T → 0 < E s)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hCofinal : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => E (t k)) atTop atTop) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ M : ℝ, 0 ≤ M →
        ∃ s : ℝ, s ∈ Set.Ioo b T ∧
          M < deriv (fun x : ℝ => Real.log (E x)) s := by
  have hLogDeriv (s : ℝ) (hs : s ∈ Set.Ioo a T) :
      HasDerivAt (fun x : ℝ => Real.log (E x))
        (deriv (fun x : ℝ => Real.log (E x)) s) s := by
    have hHas : HasDerivAt (fun x : ℝ => Real.log (E x))
        (deriv E s / E s) s :=
      (hDeriv s hs).log (ne_of_gt (hPositive s hs))
    rw [hHas.deriv]
    exact hHas
  have hLogEscape : Tendsto (fun k : ℕ => Real.log (E (t k)))
      atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro L
    have hLarge : ∀ᶠ k : ℕ in atTop,
        Real.exp L ≤ E (t k) :=
      hEscape.eventually (eventually_ge_atTop (Real.exp L))
    filter_upwards [hLarge] with k hk
    rw [← Real.log_exp L]
    exact Real.log_le_log (Real.exp_pos L) hk
  exact h3Path_scalar_cofinalEscape_forces_unboundedDerivativeEveryTail244
    (E := fun x : ℝ => Real.log (E x)) t
    hLogDeriv ht hCofinal hLogEscape

/-- The exact signed physical balance converts unbounded logarithmic
growth into an unbounded NORMALIZED full-dissipation transport margin:
-Transport₃(s) > 2 D₃(s) + M E₃(s). -/
theorem h3Path_cofinalPhysicalEnergyEscape_forces_unboundedNormalizedSignedMargin244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hCofinal : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => velocityH3EnergyAt u (t k)) atTop atTop) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ M : ℝ, 0 ≤ M →
        ∃ s : ℝ, s ∈ Set.Ioo b T ∧
          M * velocityH3EnergyAt u s +
            2 * velocityH3DissipationAt u s <
              - velocityH3TransportDerivativeAt u s ∧
          M < h3PathFullDissipationTransportExcessRate u s := by
  have hDeriv (s : ℝ) (hs : s ∈ Set.Ioo a T) :
      HasDerivAt (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) s) s :=
    h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3 a hClass s hs
  have hPositive (s : ℝ) (_hs : s ∈ Set.Ioo a T) :
      0 < velocityH3EnergyAt u s :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  intro b hb M hM
  obtain ⟨s, hs, hLogLarge⟩ :=
    (h3Path_scalar_cofinalEscape_forces_unboundedLogDerivativeEveryTail244
      (E := velocityH3EnergyAt u) t hDeriv hPositive
      ht hCofinal hEscape) b hb M hM
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hLogEq := deriv_log_velocityH3EnergyAt_eq_div
    hH3 hClass hsClass
  have hRatio : M < deriv (velocityH3EnergyAt u) s /
      velocityH3EnergyAt u s := by
    rw [← hLogEq]
    exact hLogLarge
  have hScale : M * velocityH3EnergyAt u s <
      deriv (velocityH3EnergyAt u) s :=
    (lt_div_iff₀ (hPositive s hsClass)).1 hRatio
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hsClass
  have hMargin : M * velocityH3EnergyAt u s +
      2 * velocityH3DissipationAt u s <
        - velocityH3TransportDerivativeAt u s := by
    linarith only [hScale, hBalance]
  have hRateEq :=
    h3PathFullDissipationTransportExcessRate_eq_positiveLogEnergyGrowthRate
      hH3 hClass hsClass
  have hRate : M < h3PathFullDissipationTransportExcessRate u s := by
    rw [hRateEq]
    unfold h3PathPositiveLogEnergyGrowthRate
    exact lt_of_lt_of_le hLogLarge (le_max_right _ _)
  exact ⟨s, hs, hMargin, hRate⟩

/-- Every terminal subinterval has NO finite pointwise upper bound for
the normalized positive full-dissipation transport excess. -/
theorem h3Path_cofinalPhysicalEnergyEscape_excludes_normalizedTransportTailCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hCofinal : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => velocityH3EnergyAt u (t k)) atTop atTop) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ¬ ∃ M : ℝ, ∀ s : ℝ, s ∈ Set.Ioo b T →
        h3PathFullDissipationTransportExcessRate u s ≤ M := by
  intro b hb hCeiling
  obtain ⟨M, hBound⟩ := hCeiling
  have hM : 0 ≤ max M 0 := le_max_right _ _
  obtain ⟨s, hs, _hMargin, hLarge⟩ :=
    (h3Path_cofinalPhysicalEnergyEscape_forces_unboundedNormalizedSignedMargin244
      hH3 hClass t ht hCofinal hEscape) b hb (max M 0) hM
  have hUpper := hBound s hs
  have hContradiction : M < h3PathFullDissipationTransportExcessRate u s :=
    lt_of_le_of_lt (le_max_left M 0) hLarge
  exact (not_lt_of_ge hUpper) hContradiction

/-- The original canonical exact first-crossing PDE anchors transfer the
all-orders conditional energy escape to unbounded normalized signed
transport growth on EVERY strict terminal subinterval. No new radial,
source, moment, clock or epsilon premise is inserted. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_unboundedNormalizedSignedTransport244
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
            ∀ M : ℝ, 0 ≤ M →
              ∃ s : ℝ, s ∈ Set.Ioo b T ∧
                M * velocityH3EnergyAt u s +
                  2 * velocityH3DissipationAt u s <
                    - velocityH3TransportDerivativeAt u s ∧
                M < h3PathFullDissipationTransportExcessRate u s) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_allOrdersCriticalBudget_spectralEnergyGate244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal,
    hτ, hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb M hM
  obtain ⟨_hCost, hEnergyEscape, _hSpectralEscape⟩ :=
    hHigher m F hF hFInt hUpper S D η ε hS hD hη hε
      hεη hSmall hCeil hCap hGeom
  exact (h3Path_cofinalPhysicalEnergyEscape_forces_unboundedNormalizedSignedMargin244
    hH3 hClass (fun k => τ (v k))
    (fun k => hτ (v k)) hCofinal hEnergyEscape) b hb M hM

end
end PrimeTensor.FirstMonomialTriad
