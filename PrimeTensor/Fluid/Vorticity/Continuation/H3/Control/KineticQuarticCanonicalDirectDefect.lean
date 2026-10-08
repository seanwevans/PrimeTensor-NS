import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalEventuallyDirect
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Absorption.Defect.Sequence

/-!
# Synchronize eventual direct selection with the exact full-dissipation transport defect

The existing Riccati terminal clock forces every positive-mass kinetic anchor
into the exact selected direct regime at all sufficiently late times under
hypothetical nonextension. Independently, the closed physical PDE balance
supplies a terminal sequence along which

    - transportH3(t) - 2 * dissipationH3(t) = E_H3'(t) -> +infinity.

These two statements can be synchronized on *the same* terminal sequence.
This proves a precise continuation test: if the signed full-dissipation
transport defect were bounded above at all sufficiently late direct-selected
times for even one positive-mass anchor, a smooth continuation would follow.

No such upper bound is assumed to hold for arbitrary Navier--Stokes paths.
The assertions are conditional and do not establish global regularity or
finite-time blowup.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Eventual direct selection holds along *any* sequence converging to the
terminal time from strictly below. -/
theorem h3PathCanonical_eventually_direct_on_terminal_sequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {σ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hσT : Tendsto σ atTop (𝓝 T))
    (hσBelow : ∀ n : ℕ, σ n < T) :
    ∀ᶠ n : ℕ in atTop,
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
          h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0 := by
  obtain ⟨c, hc, hDirect⟩ :=
    h3PathCanonical_eventually_direct_of_noExtension_positive_mass
      hH3 hNoExtension hClass hMass
  have hAbove : ∀ᶠ n : ℕ in atTop, c < σ n :=
    (tendsto_order.1 hσT).1 c hc.2
  filter_upwards [hAbove] with n hn
  exact hDirect (σ n) ⟨hn, hσBelow n⟩

/-- One terminal sequence simultaneously has divergent positive energy
slope, divergent exact transport-after-full-dissipation excess, divergent
canonical analytic excess, and eventual *exact* direct selection. -/
theorem h3PathCanonical_exists_direct_transport_defect_blowupSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ,
      (∀ n : ℕ, σ n ∈ Set.Ioo a T) ∧
      Tendsto σ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => deriv (velocityH3EnergyAt u) (σ n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        - velocityH3TransportDerivativeAt u (σ n) -
          2 * velocityH3DissipationAt u (σ n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u (σ n)) *
            velocityH3EnergyAt u (σ n) -
          2 * velocityH3DissipationAt u (σ n)) atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
            h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0) := by
  obtain ⟨σ, hσ, hσT, hDerivative, hDefect, hAnalytic⟩ :=
    exists_terminal_h3_absorptionDefect_blowupSequence_of_noH3PathExtension
      hH3 hNoExtension hClass
  refine ⟨σ, hσ, hσT, hDerivative, hDefect, hAnalytic, ?_⟩
  exact h3PathCanonical_eventually_direct_on_terminal_sequence
    hH3 hNoExtension hClass hMass hσT (fun n => (hσ n).2)

/-- The exact signed transport defect exceeds every prescribed finite bound
arbitrarily close to T, at a time when the selected direct share is the full
canonical coefficient and the selected absorbed share is zero. -/
theorem h3PathCanonical_arbitrarily_large_transport_defect_in_direct_regime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        M < - velocityH3TransportDerivativeAt u t -
          2 * velocityH3DissipationAt u t ∧
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t =
            h3PathCanonicalKineticTransportCoefficient u t ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t = 0 := by
  intro c hc M
  obtain ⟨σ, hσ, hσT, _hDerivative, hDefect, _hAnalytic, hDirect⟩ :=
    h3PathCanonical_exists_direct_transport_defect_blowupSequence
      hH3 hNoExtension hClass hMass
  have hLate : ∀ᶠ n : ℕ in atTop, c < σ n :=
    (tendsto_order.1 hσT).1 c hc.2
  have hLarge : ∀ᶠ n : ℕ in atTop,
      M < - velocityH3TransportDerivativeAt u (σ n) -
        2 * velocityH3DissipationAt u (σ n) :=
    hDefect.eventually (eventually_gt_atTop M)
  obtain ⟨n, hnLate, hnLarge, hnDirect⟩ :=
    (hLate.and (hLarge.and hDirect)).exists
  exact ⟨σ n, ⟨hnLate, (hσ n).2⟩,
    hnLarge, hnDirect.1, hnDirect.2⟩

/-- A tail-uniform upper bound on the signed exact transport-after-full-
dissipation excess, restricted only to direct-selected times, is sufficient
for continuation when one kinetic anchor has positive mass. -/
theorem h3PathCanonical_extension_of_direct_transport_defect_ceiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hCeiling : ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo c T →
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t =
            h3PathCanonicalKineticTransportCoefficient u t →
        - velocityH3TransportDerivativeAt u t -
          2 * velocityH3DissipationAt u t ≤ M) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨c, hc, M, hBound⟩ := hCeiling
  obtain ⟨t, ht, hGreater, hDirect, _hAbsorbed⟩ :=
    h3PathCanonical_arbitrarily_large_transport_defect_in_direct_regime
      hH3 hNoExtension hClass hMass c hc M
  exact (not_lt_of_ge (hBound t ht hDirect)) hGreater

/-- Neutral conditional alternative: continuation, or the signed full-
dissipation transport excess is arbitrarily large at late *direct-selected*
times of every positive-mass kinetic anchor. -/
theorem h3PathCanonical_extension_or_unbounded_direct_transport_defect
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo c T ∧
          M < - velocityH3TransportDerivativeAt u t -
            2 * velocityH3DissipationAt u t ∧
          h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t =
              h3PathCanonicalKineticTransportCoefficient u t ∧
          h3ExactAdaptiveSelectedAbsorbedCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t = 0 := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    exact h3PathCanonical_arbitrarily_large_transport_defect_in_direct_regime
      hH3 hExt hClass hMass

end Euclidean
end Bridge
end PrimeTensor
