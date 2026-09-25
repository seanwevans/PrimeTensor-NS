import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Integrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.TransportDichotomy

/-!
# Terminal integrability dichotomy for energy decay and transport

The pointwise exact-balance dichotomy proves

    E'(t) ≤ -D₃(t)
      or
    D₃(t) ≤ -T_H3(t).

Equivalently, after taking positive parts,

    D₃(t)
      ≤
    max(0, -E'(t)) + max(0, -T_H3(t)).

The preceding terminal dissipation theorem proves that hypothetical
nonextension forces `D₃` to dominate the nonintegrable harmonic profile
`1 / (T-t)` on a sufficiently late terminal interval.

Therefore the two positive parts above cannot both be integrable on a terminal
H³ energy-class tail.  In particular, hypothetical nonextension forces at
least one of the following two integral pathologies:

* nonintegrable negative H³-energy variation;
* nonintegrable adverse H³ transport.

This is a tail-level strengthening of the pointwise decay/transport
alternative.  It remains neutral about which branch occurs and does not assert
existence of a nonextendible path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Positive parts of the two exact-balance sinks -/

/-- Positive part of the negative canonical H³-energy derivative. -/
noncomputable def h3PathEnergyDecayPart
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (- deriv (velocityH3EnergyAt u) t)

/-- Positive part of the adverse full H³ transport derivative. -/
noncomputable def h3PathNegativeTransportPart
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    max
      0
      (- velocityH3TransportDerivativeAt u t)

theorem h3PathEnergyDecayPart_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathEnergyDecayPart u t := by
  unfold h3PathEnergyDecayPart
  exact le_max_left _ _

theorem h3PathNegativeTransportPart_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    0 ≤ h3PathNegativeTransportPart u t := by
  unfold h3PathNegativeTransportPart
  exact le_max_left _ _

/-! ## Exact-balance domination of the top dissipation -/

/--
At every strict H³ energy-class time, the top dissipation is bounded by the
sum of the negative-energy-derivative and adverse-transport positive parts.
-/
theorem velocityH3Dissipation3At_le_energyDecayPart_add_negativeTransportPart
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Dissipation3At u t
      ≤
    h3PathEnergyDecayPart u t
      +
    h3PathNegativeTransportPart u t := by

  rcases
    deriv_energy_le_neg_dissipation3_or_dissipation3_le_neg_transport
      hH3
      hClass
      ht
    with hDecay | hTransport

  · have hDDecay :
        velocityH3Dissipation3At u t
          ≤
        - deriv (velocityH3EnergyAt u) t := by
      linarith

    have hDecayMax :
        - deriv (velocityH3EnergyAt u) t
          ≤
        h3PathEnergyDecayPart u t := by
      unfold h3PathEnergyDecayPart
      exact
        le_max_right
          0
          (- deriv (velocityH3EnergyAt u) t)

    have hTransportNonneg :
        0 ≤ h3PathNegativeTransportPart u t :=
      h3PathNegativeTransportPart_nonneg
        u t

    linarith

  · have hTransportMax :
        - velocityH3TransportDerivativeAt u t
          ≤
        h3PathNegativeTransportPart u t := by
      unfold h3PathNegativeTransportPart
      exact
        le_max_right
          0
          (- velocityH3TransportDerivativeAt u t)

    have hDecayNonneg :
        0 ≤ h3PathEnergyDecayPart u t :=
      h3PathEnergyDecayPart_nonneg
        u t

    linarith

/-! ## The two positive parts cannot both be integrable -/

/--
On every strict subtail of an H³ energy-class tail, hypothetical nonextension
precludes simultaneous integrability of the negative-energy-variation part
and the adverse-transport part.
-/
theorem not_both_integrableOn_energyDecayPart_and_negativeTransportPart_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ¬
      (
        MeasureTheory.IntegrableOn
          (h3PathEnergyDecayPart u)
          (Set.Ioo b T)
          ∧
        MeasureTheory.IntegrableOn
          (h3PathNegativeTransportPart u)
          (Set.Ioo b T)
      ) := by

  obtain
    ⟨c, hc, hHarmonic⟩ :=
    exists_terminalTail_one_div_terminalDistance_le_dissipation3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  rintro
    ⟨
      hDecayIntegrable,
      hTransportIntegrable
    ⟩

  have hDecayTail :
      MeasureTheory.IntegrableOn
        (h3PathEnergyDecayPart u)
        (Set.Ioo c T) := by

    apply hDecayIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hc.1 ht.1,
        ht.2
      ⟩

  have hTransportTail :
      MeasureTheory.IntegrableOn
        (h3PathNegativeTransportPart u)
        (Set.Ioo c T) := by

    apply hTransportIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hc.1 ht.1,
        ht.2
      ⟩

  have hSumIntegrable :
      MeasureTheory.IntegrableOn
        (
          h3PathEnergyDecayPart u
            +
          h3PathNegativeTransportPart u
        )
        (Set.Ioo c T) :=
    hDecayTail.add hTransportTail

  have hReciprocal :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => 1 / (T - t))
        (Set.Ioo c T) := by

    apply
      Integrable.mono'
        hSumIntegrable

    · exact
        (
          show
            Measurable
              (fun t : ℝ => 1 / (T - t))
          by
            fun_prop
        ).aestronglyMeasurable

    · filter_upwards
        [
          ae_restrict_mem
            measurableSet_Ioo
        ]
        with t ht

      have htClass :
          t ∈ Set.Ioo a T :=
        ⟨
          lt_trans
            hb.1
            (lt_trans hc.1 ht.1),
          ht.2
        ⟩

      have hPoint :
          1 / (T - t)
            ≤
          h3PathEnergyDecayPart u t
            +
          h3PathNegativeTransportPart u t := by

        exact
          le_trans
            (hHarmonic t ht)
            (velocityH3Dissipation3At_le_energyDecayPart_add_negativeTransportPart
              hH3
              hClass
              htClass)

      have hDist :
          0 < T - t := by
        linarith [ht.2]

      rw [
        Real.norm_eq_abs,
        abs_of_pos
          (one_div_pos.mpr hDist)
      ]

      simpa only [Pi.add_apply] using
        hPoint

  exact
    not_integrableOn_one_div_terminalDistance
      hc.2
      hReciprocal

/--
Equivalent disjunctive form on every strict terminal subtail: at least one of
the two exact-balance positive parts is nonintegrable.
-/
theorem energyDecayPart_nonintegrable_or_negativeTransportPart_nonintegrable_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ¬ MeasureTheory.IntegrableOn
          (h3PathEnergyDecayPart u)
          (Set.Ioo b T)
    )
      ∨
    (
      ¬ MeasureTheory.IntegrableOn
          (h3PathNegativeTransportPart u)
          (Set.Ioo b T)
    ) := by

  classical

  by_cases hDecay :
      MeasureTheory.IntegrableOn
        (h3PathEnergyDecayPart u)
        (Set.Ioo b T)

  · right

    intro hTransport

    exact
      not_both_integrableOn_energyDecayPart_and_negativeTransportPart_on_strictSubtail_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb
        ⟨hDecay, hTransport⟩

  · exact Or.inl hDecay

/--
The same integral alternative on the original H³ energy-class tail.
-/
theorem energyDecayPart_nonintegrable_or_negativeTransportPart_nonintegrable_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ¬ MeasureTheory.IntegrableOn
          (h3PathEnergyDecayPart u)
          (Set.Ioo a T)
    )
      ∨
    (
      ¬ MeasureTheory.IntegrableOn
          (h3PathNegativeTransportPart u)
          (Set.Ioo a T)
    ) := by

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hAlternative :=
    energyDecayPart_nonintegrable_or_negativeTransportPart_nonintegrable_on_strictSubtail_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  rcases hAlternative with hDecay | hTransport

  · left

    intro hDecayFull

    apply hDecay

    apply hDecayFull.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hb.1 ht.1,
        ht.2
      ⟩

  · right

    intro hTransportFull

    apply hTransport

    apply hTransportFull.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hb.1 ht.1,
        ht.2
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
