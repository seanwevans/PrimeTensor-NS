import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedCofinalBranch244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalCanonicalSignedRate244
import Mathlib.Tactic

/-!
# Fixed cofinal signed physical H³ witnesses and the canonical third cubic

The no-strong-kinetic-L²-trace branch has a fixed cofinal physical signed
channel: either arbitrarily fast negative H³ energy slopes, or arbitrarily
large adverse signed H³ transport, on every strict terminal subtail.

We diagonalize the selected ONE channel into a single actual-time sequence
with `dist (τ n) T < 1/(n+1)`. In the adverse-transport branch the existing
physical PDE balance, lower-order 24*C₁*sqrt(E)*E estimate, and exact
972-gradient + 3*243-interpolation physical/spectral bridge yield

  (R - 24 C₁ sqrt(E(t))) E(t) < -C₃(U(t)),

where `R=n+1` and `C₃` is the genuine weighted canonical full-third
commutator. No claim is made that `C₃` is negative, because the physical
lower-order allowance can itself exceed R*E. The result does not infer
kinetic-trace failure from nonextension and does not use a static
unconditional cubic estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Convert every-subtail cofinal normalized witnesses into one strict
terminal sequence at successively increasing thresholds. This lemma does
not require continuity or boundedness of the scalar channel functions. -/
theorem h3Path_cofinalSignedRate_diagonalSequence244
    {a T : ℝ} (ha : a < T)
    (E Q : ℝ → ℝ)
    (hCofinal : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ B * E t < Q t) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) * E (τ n) < Q (τ n)) := by
  have hChoice (n : ℕ) :
      ∃ t : ℝ, t ∈ Set.Ioo a T ∧
        dist t T < (1 : ℝ) / ((n : ℝ) + 1) ∧
        ((n : ℝ) + 1) * E t < Q t := by
    let ε : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
    let c : ℝ := max ((a + T) / 2) (T - ε)
    have hε : 0 < ε := by
      dsimp only [ε]
      positivity
    have hMidLower : a < (a + T) / 2 := by
      linarith only [ha]
    have hMidUpper : (a + T) / 2 < T := by
      linarith only [ha]
    have hc : c ∈ Set.Ioo a T := by
      dsimp only [c]
      exact ⟨lt_of_lt_of_le hMidLower (le_max_left _ _),
        (max_lt_iff).2 ⟨hMidUpper, by linarith only [hε]⟩⟩
    obtain ⟨t, ht, hLarge⟩ := hCofinal c hc ((n : ℝ) + 1)
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hc.1 ht.1, ht.2⟩
    have hNear : T - ε < t :=
      lt_of_le_of_lt (le_max_right _ _) ht.1
    have hDist : dist t T < (1 : ℝ) / ((n : ℝ) + 1) := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
      dsimp only [ε] at hNear
      linarith only [hNear]
    exact ⟨t, htClass, hDist, hLarge⟩
  choose τ hτ using hChoice
  have hInv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hNormBound : ∀ n : ℕ,
      ‖τ n - T‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    simpa only [Real.norm_eq_abs, Real.dist_eq] using
      (le_of_lt (hτ n).2.1)
  have hTendsto : Tendsto τ atTop (𝓝 T) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (τ n - T)))
        (Filter.Eventually.of_forall hNormBound)
        hInv)
  exact ⟨τ, (fun n => (hτ n).1), (fun n => (hτ n).2.1),
    hTendsto, (fun n => (hτ n).2.2)⟩

/-- The signed *full* physical transport at an actual strict time transfers
to the EXACT weighted canonical third-order cubic with only the previously
proved lower-order `24*C₁*sqrt(E)*E` allowance. This inequality preserves
transport orientation; it does not take the cubic's absolute value. -/
theorem h3Path_adverseFullTransport_forces_weightedThirdDeficit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (B : ℝ)
    (hAdverse : B * velocityH3EnergyAt u t <
      -velocityH3TransportDerivativeAt u t) :
    (B - 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) *
      velocityH3EnergyAt u t <
    -weightedH3CanonicalFullThirdCommutator244
      (h3PathWeightedSpectralState244 u T hH3 t) := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hTop := h3Path_deriv_add_dissipation_le_weightedFullThird244
    hH3 hClass ht
  have hIntermediate :
      B * velocityH3EnergyAt u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
        weightedH3CanonicalFullThirdCommutator244
          (h3PathWeightedSpectralState244 u T hH3 t) := by
    linarith only [hBalance, hTop, hAdverse]
  calc
    (B - 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3EnergyAt u t =
        B * velocityH3EnergyAt u t -
          24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
          ring
    _ < -weightedH3CanonicalFullThirdCommutator244
          (h3PathWeightedSpectralState244 u T hH3 t) := by
          linarith only [hIntermediate]

/-- One FIXED signed channel has one terminal sequence on which its
normalized magnitude exceeds n+1. If the selected channel is adverse
transport, the SAME snapshots obey the actual canonical signed third-cubic
inequality, not an inequality about an unrelated spectral representative. -/
theorem h3Path_physicalNoL2Trace_forces_fixedSignedCanonicalSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
          -deriv (velocityH3EnergyAt u) (τ n))) ∨
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
          -velocityH3TransportDerivativeAt u (τ n) ∧
        (((n : ℝ) + 1) - 24 *
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n)))) *
          velocityH3EnergyAt u (τ n) <
            -weightedH3CanonicalFullThirdCommutator244
              (h3PathWeightedSpectralState244 u T hH3 (τ n)))) := by
  rcases h3Path_physicalNoL2Trace_forces_fixedCofinalSignedChannel244
      hH3 hClass hL hNoTrace with hFast | hAdverse
  · have hCofinal : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          B * velocityH3EnergyAt u t <
            -deriv (velocityH3EnergyAt u) t := by
      intro b hb B
      obtain ⟨t, ht, hFastAt⟩ := hFast b hb B
      exact ⟨t, ht, by linarith only [hFastAt]⟩
    obtain ⟨τ, hτ, hNear, hTendsto, hRate⟩ :=
      h3Path_cofinalSignedRate_diagonalSequence244
        hClass.terminal_start.2
        (velocityH3EnergyAt u)
        (fun t => -deriv (velocityH3EnergyAt u) t)
        hCofinal
    exact Or.inl ⟨τ, hτ, hNear, hTendsto, hRate⟩
  · obtain ⟨τ, hτ, hNear, hTendsto, hRate⟩ :=
      h3Path_cofinalSignedRate_diagonalSequence244
        hClass.terminal_start.2
        (velocityH3EnergyAt u)
        (fun t => -velocityH3TransportDerivativeAt u t)
        hAdverse
    refine Or.inr ⟨τ, hτ, hNear, hTendsto, ?_⟩
    intro n
    exact ⟨hRate n,
      h3Path_adverseFullTransport_forces_weightedThirdDeficit244
        hH3 hClass (hτ n) ((n : ℝ) + 1) (hRate n)⟩

/-- If a physical logarithmic energy-slope floor has already ruled out the
fast-decay branch, the canonical adverse-cubic witness can be selected
unconditionally *within the remaining no-L²-trace hypothesis* on one
strict terminal sequence after that fixed slope anchor. -/
theorem h3Path_physicalSlopeFloor_forces_canonicalAdverseTerminalSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (B : ℝ)
    (hSlope : ∀ t : ℝ, t ∈ Set.Ioo b T →
      -(B * velocityH3EnergyAt u t) ≤
        deriv (velocityH3EnergyAt u) t) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo b T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
          -velocityH3TransportDerivativeAt u (τ n) ∧
        (((n : ℝ) + 1) - 24 *
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u (τ n)))) *
          velocityH3EnergyAt u (τ n) <
            -weightedH3CanonicalFullThirdCommutator244
              (h3PathWeightedSpectralState244 u T hH3 (τ n))) := by
  have hCofinal : ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ C : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        C * velocityH3EnergyAt u t <
          -velocityH3TransportDerivativeAt u t :=
    h3Path_physicalSlopeFloor_forces_cofinalAdverseTransport244
      hH3 hClass hL hNoTrace b hb B hSlope
  obtain ⟨τ, hτ, hNear, hTendsto, hRate⟩ :=
    h3Path_cofinalSignedRate_diagonalSequence244
      hb.2 (velocityH3EnergyAt u)
      (fun t => -velocityH3TransportDerivativeAt u t) hCofinal
  refine ⟨τ, hτ, hNear, hTendsto, ?_⟩
  intro n
  have htClass : τ n ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩
  exact ⟨hRate n,
    h3Path_adverseFullTransport_forces_weightedThirdDeficit244
      hH3 hClass htClass ((n : ℝ) + 1) (hRate n)⟩

end
end PrimeTensor.FirstMonomialTriad
