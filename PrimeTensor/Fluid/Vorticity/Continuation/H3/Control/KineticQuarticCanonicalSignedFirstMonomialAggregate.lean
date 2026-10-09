import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedMonomialCyclicSymmetry

/-!
# The entire signed H³ interpolation commutator is three copies of one family

The preceding two physical mixed-partial identities show that each of the
three signed `D³u · (D²u D²u)` interpolation monomial families is a permutation
of the first. Here we reindex the *complete finite sums*, rather than merely
reorienting selected negative monomial witnesses. The result is the exact,
physical, signed identity

    I₃(t) = 3 * Σ_{j,r,i,k,l} P₀(j,i,k,l,r;t).

This is a multiplicity identity, not vanishing, cancellation, or a favorable
sign. The remaining canonical sum contains 3⁵=243 formal coordinate slots.
The existing top-order gradient estimate and signed nonextension witness are
then rewritten through this single signed family. No new PDE analytic
hypotheses, negative-sign assumptions, or continuation claims are introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable local instance axisFintypeH3SignedFirstMonomialAggregate
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Signed aggregate of the canonical first `D³u · (D²u D²u)` monomial
across all five ordered coordinate indices. -/
noncomputable def h3PathCanonicalFirstMonomialAggregateAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ r : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0

/-- Reordering three 3-axis sums leaves their values unchanged under
interchange of the first two arguments. -/
private theorem h3PathCanonical_threeDerivativeSum_swap
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ) :
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three, f k i l) =
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three, f i k l := by
  simp only [axis_sum_three]
  ring

/-- Reordering three 3-axis sums leaves their values unchanged under
cyclic permutation of the three arguments. -/
private theorem h3PathCanonical_threeDerivativeSum_cycle
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ) :
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three, f l i k) =
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three, f i k l := by
  simp only [axis_sum_three]
  ring

/-- The first two physical monomial families have the same *signed* total
for every fixed velocity component and contracted velocity axis. -/
theorem h3PathCanonical_first_secondMonomial_derivativeSums_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j r : PrimeTensor.Axis Depth.three) :
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1) =
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 := by
  calc
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1) =
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            h3PathCanonicalInterpolationMonomialPairing u t j k i l r 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      exact (h3PathCanonical_firstMonomial_eq_secondMonomial_swapped
        hClass ht j k i l r).symm
    _ = _ :=
      h3PathCanonical_threeDerivativeSum_swap
        (fun i k l =>
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0)

/-- The third physical monomial family also has exactly the same *signed*
three-derivative-index sum, by the already-proved cyclic mixed partials. -/
theorem h3PathCanonical_first_thirdMonomial_derivativeSums_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j r : PrimeTensor.Axis Depth.three) :
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2) =
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 := by
  calc
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2) =
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            h3PathCanonicalInterpolationMonomialPairing u t j l i k r 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      exact h3PathCanonical_thirdMonomial_eq_firstMonomial_cyclic
        hClass ht j i k l r
    _ = _ :=
      h3PathCanonical_threeDerivativeSum_cycle
        (fun i k l =>
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0)

/-- A physical 81-coordinate interpolation pairing sums its nine signed
monomials along the three velocity axes. Integrability is supplied by the
already established Landau analytic data, not assumed axiomatically. -/
theorem h3PathCanonical_coordinatePairing_eq_axisSum_threeMonomials
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : H3OrderThreeInterpolationMonomialPairingIntegrableAt u t)
    (j i k l : PrimeTensor.Axis Depth.three) :
    h3PathCanonicalInterpolationCoordinatePairing u t j i k l =
      ∑ r : PrimeTensor.Axis Depth.three,
        (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 +
          (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 +
            h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2)) := by
  rw [h3PathCanonical_coordinatePairing_eq_threeAxes hInt j i k l,
      h3PathCanonical_axisPairing_eq_threeMonomials hInt j i k l xAxis,
      h3PathCanonical_axisPairing_eq_threeMonomials hInt j i k l yAxis,
      h3PathCanonical_axisPairing_eq_threeMonomials hInt j i k l zAxis,
      axis_sum_three]

/-- Move the final velocity-axis sum before the three differentiated indices.
This is just four applications of Fubini for finite sums. -/
private theorem h3PathCanonical_reorder_fiveAxis_sum
    (f : PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → ℝ) :
    (∑ j : PrimeTensor.Axis Depth.three,
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            ∑ r : PrimeTensor.Axis Depth.three, f j i k l r) =
    ∑ j : PrimeTensor.Axis Depth.three,
      ∑ r : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three, f j i k l r := by
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          ∑ r : PrimeTensor.Axis Depth.three, f j i k l r) =
      ∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ r : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three, f j i k l r := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = (∑ i : PrimeTensor.Axis Depth.three,
          ∑ r : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three, f j i k l r) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ r : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three, f j i k l r := by
      exact Finset.sum_comm

/-- The full signed physical interpolation commutator is EXACTLY three copies
of the canonical type-0 monomial aggregate. This does not assert that the
aggregate vanishes or has a favorable sign. -/
theorem h3PathCanonical_interpolation_eq_three_firstMonomialAggregate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    thirdOrderInterpolationTransportSum u t =
      3 * h3PathCanonicalFirstMonomialAggregateAt u t := by
  have hInt : H3OrderThreeInterpolationMonomialPairingIntegrableAt u t :=
    h3PathCanonical_monomialIntegrable_on_h3Slice hH3 hClass ht
  have hExpanded : thirdOrderInterpolationTransportSum u t =
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              ∑ r : PrimeTensor.Axis Depth.three,
                (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 +
                  (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 +
                    h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2)) := by
    rw [h3PathCanonical_interpolation_eq_sum_coordinatePairings]
    simp_rw [h3PathCanonical_coordinatePairing_eq_axisSum_threeMonomials hInt]
  have hReordered := h3PathCanonical_reorder_fiveAxis_sum
    (fun j i k l r =>
      h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 +
        (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 +
          h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2))
  have hLocal (j r : PrimeTensor.Axis Depth.three) :
      (∑ i : PrimeTensor.Axis Depth.three,
        ∑ k : PrimeTensor.Axis Depth.three,
          ∑ l : PrimeTensor.Axis Depth.three,
            (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 +
              (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 +
                h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2))) =
        3 * (∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0) := by
    calc
      _ = (∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0) +
          ((∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1) +
            (∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2)) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by
        rw [h3PathCanonical_first_secondMonomial_derivativeSums_eq hClass ht j r,
          h3PathCanonical_first_thirdMonomial_derivativeSums_eq hClass ht j r]
        ring
  calc
    thirdOrderInterpolationTransportSum u t =
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ r : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 +
                  (h3PathCanonicalInterpolationMonomialPairing u t j i k l r 1 +
                    h3PathCanonicalInterpolationMonomialPairing u t j i k l r 2)) :=
      hExpanded.trans hReordered
    _ = ∑ j : PrimeTensor.Axis Depth.three,
          ∑ r : PrimeTensor.Axis Depth.three,
            3 * (∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro r _
      exact hLocal j r
    _ = 3 * h3PathCanonicalFirstMonomialAggregateAt u t := by
      unfold h3PathCanonicalFirstMonomialAggregateAt
      simp only [Finset.mul_sum]

/-- A single exact signed monomial family now represents the whole physical
top nonlinear transport after separately retaining the gradient block. -/
theorem h3PathCanonical_thirdTransport_eq_gradient_add_three_firstMonomialAggregate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3TransportDerivative3At u t =
      thirdOrderGradientTransportSum u t +
        3 * h3PathCanonicalFirstMonomialAggregateAt u t := by
  rw [h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    hH3 hClass ht,
    h3PathCanonical_interpolation_eq_three_firstMonomialAggregate
      hH3 hClass ht]

/-- The signed terminal adversity can be stated against one concrete
symmetrized triple-product family, with exact multiplicity three. -/
theorem h3PathCanonical_signedAdversity_forces_firstMonomialAggregateDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
        3 * h3PathCanonicalFirstMonomialAggregateAt u t := by
  have hDeficit := h3PathCanonical_signedAdversity_forces_interpolationDeficit
    hH3 hClass ht hAdverse
  rw [h3PathCanonical_interpolation_eq_three_firstMonomialAggregate
    hH3 hClass ht] at hDeficit
  exact hDeficit

/-- Hypothetical nonextension forces an actual signed aggregate deficit on
every strict terminal subtail, without imposing gradient absorption. -/
theorem h3PathCanonical_firstMonomialAggregateDeficit_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          3 * h3PathCanonicalFirstMonomialAggregateAt u t := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  exact ⟨t, ht,
    h3PathCanonical_signedAdversity_forces_firstMonomialAggregateDeficit
      hH3 hClass htClass hAdverse⟩

/-- Conditional continuation from a tail-wide physical compensation bound on
one symmetrized signed monomial family. This is not an automatic estimate. -/
theorem h3PathCanonical_extension_of_eventual_firstMonomialAggregateCompensation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hCompensation : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t +
            3 * h3PathCanonicalFirstMonomialAggregateAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hDeficit⟩ :=
    h3PathCanonical_firstMonomialAggregateDeficit_on_every_subtail
      hH3 hNoExtension hClass hb hd (by norm_num : (0 : ℝ) ≤ 0)
  have hBound := hCompensation t ht
  simp only [zero_mul, zero_add] at hDeficit
  linarith only [hDeficit, hBound]

end Euclidean
end Bridge
end PrimeTensor
