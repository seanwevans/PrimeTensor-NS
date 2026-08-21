import PrimeTensor.Fluid.Vorticity.Continuation.Frontier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.Gronwall

/-!
# BKM growth frontier on a terminal tail

The continuation frontier now carries the function-space datum explicitly:

    one finite H³-type seed at a ∈ (0,T).

The BKM estimate only needs to propagate that seed forward toward `T`.
Accordingly every object in this file lives on a terminal tail `[a,T)`.

A second correction is made here as well: the scalar Osgood/Grönwall step is
stated with local `C¹` regularity of the energy profile.  Pointwise
differentiability alone is too weak for a direct Lebesgue fundamental-theorem
argument.  A smooth Navier--Stokes energy profile is expected to satisfy this
regularity, and stating it explicitly keeps the scalar theorem honest.

The remaining known-analysis statement splits into:

1. PDE/harmonic analysis:
   vorticity control + an H³ seed produces a locally-C¹ H³ energy profile with
   BKM logarithmic growth.

2. scalar Osgood/Grönwall:
   such a profile stays bounded on `[a,T)` when the vorticity envelope is
   integrable.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/--
`E` is a normalized H³-energy envelope for `u` on `[a,T)`.
-/
def H3EnergyProfileFrom
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (E : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ico a T →
      1 ≤ E t
        ∧
      VelocityH3BoundAt
        u t (E t)

/--
Local `C¹` regularity of an energy profile on every compact subinterval of the
terminal tail.
-/
def EnergyLocallyC1OnTail
    (a T : ℝ)
    (E : ℝ → ℝ) : Prop :=
  ∀ b : ℝ,
    b ∈ Set.Ico a T →
      ContDiffOn
        ℝ 1 E
        (Set.Icc a b)

/--
The logarithmic differential inequality on the open part of the terminal tail.
-/
def BKMLogGrowthInequalityFrom
    (a T : ℝ)
    (g E : ℝ → ℝ)
    (C : ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      deriv E t
        ≤
      C
        * (1 + |g t|)
        * E t
        * (1 + Real.log (E t))

/--
PDE/harmonic-analysis frontier.

Starting from one finite H³ seed and an integrable common vorticity envelope,
construct an energy profile on a terminal tail with local `C¹` regularity and
the BKM logarithmic growth inequality.
-/
def VorticityEnvelopeProducesBKMH3Growth : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (g : ℝ → ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      PreterminalH3Seed
          u T
        →
      MeasureTheory.IntegrableOn
          g
          (Set.Ioo (0 : ℝ) T)
        →
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo (0 : ℝ) T →
            VorticityEnvelope
              u g t
      )
        →
      ∃
        (a : ℝ)
        (E : ℝ → ℝ)
        (C : ℝ),
          a ∈ Set.Ioo (0 : ℝ) T
            ∧
          0 ≤ C
            ∧
          H3EnergyProfileFrom
            u a T E
            ∧
          EnergyLocallyC1OnTail
            a T E
            ∧
          BKMLogGrowthInequalityFrom
            a T g E C

/--
Pure scalar Osgood/Grönwall frontier.

Because the profile is anchored at `a > 0`, the one-sided growth inequality is
now asked to control only forward growth toward `T`; no false bound near
`t = 0` is demanded.
-/
def LogarithmicGronwallClosesEnergy : Prop :=
  ∀
    (a T : ℝ)
    (g E : ℝ → ℝ)
    (C : ℝ),
      a < T
        →
      MeasureTheory.IntegrableOn
          g
          (Set.Ioo a T)
        →
      0 ≤ C
        →
      (
        ∀ t : ℝ,
          t ∈ Set.Ico a T →
            1 ≤ E t
      )
        →
      EnergyLocallyC1OnTail
          a T E
        →
      BKMLogGrowthInequalityFrom
          a T g E C
        →
      ∃ M : ℝ,
        0 ≤ M
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ico a T →
            E t ≤ M

/--
The BKM growth estimate plus the scalar logarithmic Grönwall theorem gives the
uniform terminal-tail H³ control required by the continuation frontier.
-/
theorem vorticityL1LinfProducesH3Control_of_BKMGrowth
    (
      hGrowth :
        VorticityEnvelopeProducesBKMH3Growth
    )
    (
      hLogGronwall :
        LogarithmicGronwallClosesEnergy
    ) :
    VorticityL1LinfProducesH3Control := by

  intro u T hAdmissible hSeed hControl

  obtain ⟨g, hgIntegrable, hgEnvelope⟩ :=
    hControl

  obtain
    ⟨
      a,
      E,
      C,
      ha,
      hC,
      hEnergy,
      hC1,
      hGrowthIneq
    ⟩ :=
    hGrowth
      u T g
      hAdmissible
      hSeed
      hgIntegrable
      hgEnvelope

  have haT :
      a < T :=
    ha.2

  have hgTail :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo a T) := by
    apply
      hgIntegrable.mono_set
    intro t ht
    exact
      ⟨
        lt_trans ha.1 ht.1,
        ht.2
      ⟩

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          1 ≤ E t := by
    intro t ht
    exact (hEnergy t ht).1

  obtain ⟨M, hM, hEM⟩ :=
    hLogGronwall
      a T g E C
      haT
      hgTail
      hC
      hEOne
      hC1
      hGrowthIneq

  refine
    ⟨
      a,
      M,
      ha,
      hM,
      ?_
    ⟩

  intro t ht

  have hAt :
      VelocityH3BoundAt
        u t (E t) :=
    (hEnergy t ht).2

  have hBound :
      E t ≤ M :=
    hEM t ht

  unfold VelocityH3BoundAt at hAt ⊢

  intro j

  dsimp only at hAt ⊢

  have hAtj :=
    hAt j

  rcases hAtj with
    ⟨
      h0,
      h1,
      h2,
      h3
    ⟩

  refine
    ⟨
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        h0.1,
        h0.2.trans hBound
      ⟩

  · intro i
    have hi := h1 i
    exact
      ⟨
        hi.1,
        hi.2.trans hBound
      ⟩

  · intro i k
    have hik := h2 i k
    exact
      ⟨
        hik.1,
        hik.2.trans hBound
      ⟩

  · intro i k l
    have hikl := h3 i k l
    exact
      ⟨
        hikl.1,
        hikl.2.trans hBound
      ⟩

/--
Combining the BKM growth factorization with the tail-H³ continuation theorem
reconstructs the honest seeded continuation criterion.
-/
theorem seededVorticityL1LinfProducesExtension_of_BKMGrowth
    (
      hGrowth :
        VorticityEnvelopeProducesBKMH3Growth
    )
    (
      hLogGronwall :
        LogarithmicGronwallClosesEnergy
    )
    (
      hH3ToExtension :
        H3ControlProducesExtension
    ) :
    SeededVorticityL1LinfProducesExtension := by

  apply
    seededVorticityL1LinfProducesExtension_of_H3Factorization
      (
        vorticityL1LinfProducesH3Control_of_BKMGrowth
          hGrowth
          hLogGronwall
      )
      hH3ToExtension

end Euclidean
end Bridge
end PrimeTensor
