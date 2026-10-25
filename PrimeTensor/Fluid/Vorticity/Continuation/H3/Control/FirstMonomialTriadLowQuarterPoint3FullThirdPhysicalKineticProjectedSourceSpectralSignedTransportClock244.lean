import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralNormalizedDissipationClock244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact
import Mathlib.Tactic

/-!
# Signed transport versus fast H³ energy decay on the physical radial witness

The already proved no-physical-L²-trace alternative produces a single terminal
sequence on which the ACTUAL normalized physical H³ dissipation D/E exceeds
n+1. The exact preterminal Navier--Stokes energy balance is

  E'(t) + 2 D(t) = - Transport(t).

Consequently, at every sufficiently advanced point of that SAME sequence,
either E'(t) < -(n+1) E(t), or -Transport(t) > (n+1) E(t).
This is an exhaustive, signed physical PDE obstruction. It does not assert
that nonextension implies failure of the kinetic L² terminal trace.

Conversely, when the negative H³ derivative is bounded below by -B E and
adverse signed transport is bounded above by B E on a terminal subtail,
the no-L²-trace branch is excluded. The resulting strong trace has precisely
the canonical terminal kinetic square mass, including the zero-mass case.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact signed H³ energy balance and `D > R E` force either fast energy
loss or an adverse nonlinear transport input exceeding `R E`. -/
theorem h3Path_signedBalance_fastDecay_or_adverseTransport244
    (E D F W R : ℝ)
    (hBalance : F + 2 * D = -W)
    (hD : R * E < D) :
    F < -(R * E) ∨ R * E < -W := by
  by_cases hFast : F < -(R * E)
  · exact Or.inl hFast
  · right
    have hSlow : -(R * E) ≤ F := le_of_not_gt hFast
    linarith only [hSlow, hD, hBalance]

/-- The identical moving-radial normalized-dissipation witness must pass
through one of two physical signed-energy channels at each `n ≥ 1`. -/
theorem h3Path_physicalNoL2Trace_forces_signedBalanceSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, 1 ≤ n →
        deriv (velocityH3EnergyAt u) (τ n) <
            -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n)) ∨
        ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
            -velocityH3TransportDerivativeAt u (τ n)) := by
  obtain ⟨τ, hτ, hNear, hTendsto, hClock⟩ :=
    h3Path_physicalNoL2Trace_forces_normalizedDissipationClockSequence244
      hH3 hClass hL hNoTrace
  refine ⟨τ, hτ, hNear, hTendsto, ?_⟩
  intro n hn
  let R : ℝ := (n : ℝ) + 1
  let E : ℝ := velocityH3EnergyAt u (τ n)
  let D : ℝ := velocityH3DissipationAt u (τ n)
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hR : 2 ≤ R := by dsimp only [R]; linarith
  have hE : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u (τ n))
  have hClock' : R ^ 3 * E < (R + 2) * D := by
    dsimp only [R, E, D]
    simpa only [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
      using hClock n
  have hRatio : R < D / E :=
    h3Path_cubicDissipationEnergyClock_forces_ratio_gt_radius244
      E D R hR hE hClock'
  have hD : R * E < D := (lt_div_iff₀ hE).mp hRatio
  have hBalance :
      deriv (velocityH3EnergyAt u) (τ n) + 2 * D =
        -velocityH3TransportDerivativeAt u (τ n) := by
    dsimp only [D]
    exact deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass (hτ n)
  exact h3Path_signedBalance_fastDecay_or_adverseTransport244
    E D (deriv (velocityH3EnergyAt u) (τ n))
    (velocityH3TransportDerivativeAt u (τ n)) R hBalance hD

/-- On every strict terminal subtail and at every prescribed rate, failure
of the strong kinetic trace forces either rapidly negative H³ energy slope
or adverse signed nonlinear transport. No fixed branch is claimed. -/
theorem h3Path_physicalNoL2Trace_forces_cofinalSignedTransport_or_fastDecay244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ B : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧
        (deriv (velocityH3EnergyAt u) t <
            -(B * velocityH3EnergyAt u t) ∨
          B * velocityH3EnergyAt u t <
            -velocityH3TransportDerivativeAt u t) := by
  obtain ⟨τ, hτ, _hNear, hTendsto, hSigned⟩ :=
    h3Path_physicalNoL2Trace_forces_signedBalanceSequence244
      hH3 hClass hL hNoTrace
  intro b hb B
  obtain ⟨N, hN⟩ := exists_nat_gt B
  have hAbove : ∀ᶠ n : ℕ in atTop, b < τ n :=
    hTendsto.eventually (Ioi_mem_nhds hb.2)
  have hNat : ∀ᶠ n : ℕ in atTop, max N 1 ≤ n :=
    eventually_ge_atTop (max N 1)
  obtain ⟨n, hnAbove, hnLarge⟩ := (hAbove.and hNat).exists
  have hnN : N ≤ n := (le_max_left N 1).trans hnLarge
  have hnOne : 1 ≤ n := (le_max_right N 1).trans hnLarge
  have hB : B < (n : ℝ) + 1 := by
    have hN' : B < (n : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hnN)
    linarith only [hN']
  have hE : 0 < velocityH3EnergyAt u (τ n) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u (τ n))
  have hScaled :
      B * velocityH3EnergyAt u (τ n) <
        ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) :=
    mul_lt_mul_of_pos_right hB hE
  refine ⟨τ n, ⟨hnAbove, (hτ n).2⟩, ?_⟩
  rcases hSigned n hnOne with hFast | hTransport
  · left
    linarith only [hFast, hScaled]
  · right
    linarith only [hTransport, hScaled]

/-- A uniformly noncatastrophic physical H³ energy slope, together with a
uniform ceiling on adverse signed physical transport, gives a strong kinetic
L² terminal trace with the correct canonical square mass. The two estimates
are imposed on the same strict subtail, without a separate positivity
hypothesis on the terminal kinetic mass. -/
theorem h3Path_physicalL2Trace_of_signedSlopeFloor_and_transportCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (B : ℝ)
    (hSlope : ∀ t : ℝ, t ∈ Set.Ioo b T →
      -(B * velocityH3EnergyAt u t) ≤
        deriv (velocityH3EnergyAt u) t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      -velocityH3TransportDerivativeAt u t ≤
        B * velocityH3EnergyAt u t) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · have hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T := by
      rcases h3Path_physicalL2Trace_or_fixedSpectralCoordinateEscape_allKinetic244
        hH3 hClass with hStrong | hEscape
      · obtain ⟨U, hU, _⟩ := hStrong
        exact False.elim (hTrace ⟨U, hU⟩)
      · exact hEscape.1
    obtain ⟨t, ht, hBad⟩ :=
      h3Path_physicalNoL2Trace_forces_cofinalSignedTransport_or_fastDecay244
        hH3 hClass hL hTrace b hb B
    rcases hBad with hFast | hAdverse
    · exact False.elim ((not_lt_of_ge (hSlope t ht)) hFast)
    · exact False.elim ((not_lt_of_ge (hTransport t ht)) hAdverse)

end
end PrimeTensor.FirstMonomialTriad
