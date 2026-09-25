import PrimeTensor.Fluid.Vorticity.Continuation.H3.Gradient.TailIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.TailIntegrability

/-!
# Actual terminal component amplitudes forced by nonextension

The tail-local continuation criteria immediately rule out every finite constant
envelope on a hypothetical nonextension branch.

Because a constant scalar function is integrable on every finite interval,
nonextension implies the following concrete cofinal amplitude statements.

For every strict terminal restart `c < T` and every finite threshold `M`:

* some later time, spatial point, and velocity-gradient component satisfies
  `M < |∂ᵢ uⱼ|`;

* some later time and spatial point has at least one vorticity component with
  magnitude greater than `M`.

Thus the actual first velocity derivatives and actual vorticity components are
cofinally unbounded toward the terminal time, in a componentwise formulation
that does not introduce spatial supremum norms.

All statements remain conditional consequences of hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Velocity-gradient component amplitudes -/

/--
Under hypothetical nonextension, every finite componentwise first-derivative
bound fails arbitrarily late on every strict H³ energy-class tail.
-/
theorem exists_velocityGradientComponent_gt_on_every_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀
      c : ℝ,
        c ∈ Set.Ioo a T →
        ∀ M : ℝ,
          ∃
            t : ℝ,
              t ∈ Set.Ioo c T
                ∧
              ∃
                i j : PrimeTensor.Axis Depth.three,
                ∃ x : Point3,
                  M
                    <
                  abs
                    (
                      spatial3.d
                        i
                        (
                          fun y =>
                            (
                              PrimeTensor.Bridge.logSpaceTimeVectorField
                                u t y
                            ).component j
                        )
                        x
                    ) := by

  intro c hc M

  have hClassC :
      PreterminalH3EnergyClass u c T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hc.1)
      hc.2

  by_contra hNoWitness

  have hEnvelope :
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
          VelocityGradientEnvelope
            u
            (fun _ : ℝ => M)
            t := by

    intro t ht

    unfold VelocityGradientEnvelope

    intro i j x

    by_contra hNotLe

    have hGt :
        M
          <
        abs
          (
            spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component j
              )
              x
          ) :=
      lt_of_not_ge
        hNotLe

    exact
      hNoWitness
        ⟨
          t,
          ht,
          i,
          j,
          x,
          hGt
        ⟩

  have hNonintegrable :
      ¬ MeasureTheory.IntegrableOn
          (fun _ : ℝ => M)
          (Set.Ioo c T) :=
    not_integrableOn_velocityGradientEnvelope_on_energyClassTail_of_noH3PathExtension
      hH3
      hNoExtension
      hClassC
      hEnvelope

  have hConstantIntegrable :
      MeasureTheory.IntegrableOn
        (fun _ : ℝ => M)
        (Set.Ioo c T) := by

    exact
      integrableOn_const
        measure_Ioo_lt_top.ne

  exact
    hNonintegrable
      hConstantIntegrable

/-! ## Vorticity component amplitudes -/

/--
Under hypothetical nonextension, every finite common bound on the three
vorticity components fails arbitrarily late on every strict H³ energy-class
tail.
-/
theorem exists_vorticityComponent_gt_on_every_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀
      c : ℝ,
        c ∈ Set.Ioo a T →
        ∀ M : ℝ,
          ∃
            t : ℝ,
              t ∈ Set.Ioo c T
                ∧
              ∃ x : Point3,
                (
                  M
                    <
                  abs
                    (
                      realVorticityX
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        t x
                    )
                )
                  ∨
                (
                  M
                    <
                  abs
                    (
                      realVorticityY
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        t x
                    )
                )
                  ∨
                (
                  M
                    <
                  abs
                    (
                      realVorticityZ
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        t x
                    )
                ) := by

  intro c hc M

  have hClassC :
      PreterminalH3EnergyClass u c T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hc.1)
      hc.2

  by_contra hNoWitness

  have hEnvelope :
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
          VorticityEnvelope
            u
            (fun _ : ℝ => M)
            t := by

    intro t ht

    unfold VorticityEnvelope

    intro x

    constructor

    · by_contra hNotLe

      have hGt :
          M
            <
          abs
            (
              realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            ) :=
        lt_of_not_ge
          hNotLe

      exact
        hNoWitness
          ⟨
            t,
            ht,
            x,
            Or.inl hGt
          ⟩

    · constructor

      · by_contra hNotLe

        have hGt :
            M
              <
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              ) :=
          lt_of_not_ge
            hNotLe

        exact
          hNoWitness
            ⟨
              t,
              ht,
              x,
              Or.inr (Or.inl hGt)
            ⟩

      · by_contra hNotLe

        have hGt :
            M
              <
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              ) :=
          lt_of_not_ge
            hNotLe

        exact
          hNoWitness
            ⟨
              t,
              ht,
              x,
              Or.inr (Or.inr hGt)
            ⟩

  have hNonintegrable :
      ¬ MeasureTheory.IntegrableOn
          (fun _ : ℝ => M)
          (Set.Ioo c T) :=
    not_integrableOn_vorticityEnvelope_on_energyClassTail_of_noH3PathExtension
      hH3
      hNoExtension
      hClassC
      hEnvelope

  have hConstantIntegrable :
      MeasureTheory.IntegrableOn
        (fun _ : ℝ => M)
        (Set.Ioo c T) := by

    exact
      integrableOn_const
        measure_Ioo_lt_top.ne

  exact
    hNonintegrable
      hConstantIntegrable

/-! ## Neutral joint package -/

/--
Neutral terminal amplitude alternative.

Either the H³ path extends smoothly through `T`, or both actual first velocity
derivatives and actual vorticity components exceed every finite threshold
arbitrarily late on every strict terminal energy-class subtail.
-/
theorem smoothContinuationExtension_or_terminalGradientAndVorticityComponents_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      (
        ∀
          c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃
                t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  ∃
                    i j : PrimeTensor.Axis Depth.three,
                    ∃ x : Point3,
                      M
                        <
                      abs
                        (
                          spatial3.d
                            i
                            (
                              fun y =>
                                (
                                  PrimeTensor.Bridge.logSpaceTimeVectorField
                                    u t y
                                ).component j
                            )
                            x
                        )
      )
        ∧
      (
        ∀
          c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃
                t : ℝ,
                  t ∈ Set.Ioo c T
                    ∧
                  ∃ x : Point3,
                    (
                      M
                        <
                      abs
                        (
                          realVorticityX
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            t x
                        )
                    )
                      ∨
                    (
                      M
                        <
                      abs
                        (
                          realVorticityY
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            t x
                        )
                    )
                      ∨
                    (
                      M
                        <
                      abs
                        (
                          realVorticityZ
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            t x
                        )
                    )
      )
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        ⟨
          exists_velocityGradientComponent_gt_on_every_strictSubtail_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          exists_vorticityComponent_gt_on_every_strictSubtail_of_noH3PathExtension
            hH3
            hExtension
            hClass
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
