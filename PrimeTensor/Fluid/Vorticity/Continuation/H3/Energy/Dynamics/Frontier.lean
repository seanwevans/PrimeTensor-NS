import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Frontier

/-!
# Factor H³-path BKM through the exact scalar energy dynamics

`H3PathExactEnergyFrontier` removed the implementation-level mixed-time and
majorant records from the public BKM statement.  Its remaining analytic
interfaces are still finer than the BKM/Osgood argument itself consumes.

After the logarithmic gradient envelope has been constructed, the continuation
argument uses only two scalar H³-energy facts:

1. the canonical H³ energy is genuinely differentiable at every strict tail
   time, with derivative equal to `deriv`;
2. every supplied velocity-gradient envelope drives the canonical H³ growth
   inequality with the already-closed transport constant `4422`.

The detailed derivative identities, PDE pairing integrability, pressure
cancellation, and diffusion sign are one sufficient route to those two facts,
but they need not appear in the final BKM theorem.

This file isolates that exact scalar dynamics boundary.

The final continuation theorem below therefore has only three independent
public inputs:

* a uniform zeroth-order physical `L²` radius on each strict later tail;
* scalar differentiability of the canonical H³ energy;
* the canonical H³ gradient-growth inequality.

Compatibility theorems show that the exact-energy frontier from the preceding
file implies both scalar-dynamics interfaces.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

/-! ## Exact scalar dynamics interfaces -/

/--
The canonical scalar H³ energy is differentiable at every strict
H³-path energy-class time.
-/
def H3PathEnergyClassProducesCanonicalEnergyDifferentiability : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              HasDerivAt
                (velocityH3EnergyAt u)
                (deriv (velocityH3EnergyAt u) t)
                t

/--
Every velocity-gradient envelope drives the canonical H³ growth inequality on
an H³-path energy-class tail.
-/
def H3PathEnergyClassProducesCanonicalGradientGrowth : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          ∀ h : ℝ → ℝ,
            (
              ∀ t : ℝ,
                t ∈ Set.Ioo a T →
                  VelocityGradientEnvelope u h t
            ) →
            H3GradientGrowthInequalityFrom
              a T h
              (velocityH3EnergyAt u)
              4422

/-! ## Compatibility with the exact-energy frontier -/

/--
Orderwise H³ energy derivative identities imply the exact scalar
differentiability interface.
-/
theorem h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities) :
    H3PathEnergyClassProducesCanonicalEnergyDifferentiability := by

  intro u T hH3 a hClass t ht

  have hIds :
      H3OrderEnergyDerivativeIdentities u t :=
    hDerivative
      u T hH3
      a hClass
      t ht

  have hDeriv :
      deriv (velocityH3EnergyAt u) t
        =
      velocityH3FormalDerivativeAt u t :=
    deriv_velocityH3EnergyAt
      hIds

  rw [hDeriv]

  exact
    hasDerivAt_velocityH3EnergyAt
      hIds

/--
The exact derivative/pairing/sign frontier implies the canonical scalar
gradient-growth interface.
-/
theorem h3PathEnergyClassProducesCanonicalGradientGrowth_of_exactEnergy
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability)
    (hSigns :
      H3PathEnergyClassProducesFullScalarSigns) :
    H3PathEnergyClassProducesCanonicalGradientGrowth := by

  intro u T hH3 a hClass h hGradient

  exact
    h3GradientGrowthInequalityFrom_h3Path_exactEnergy
      hDerivative
      hPairing
      hSigns
      hH3
      hClass
      hGradient

/-! ## BKM closure from scalar dynamics -/

/--
Terminal H³ control from exactly the low-frequency input and the two scalar
H³-energy dynamics facts consumed by the logarithmic Osgood argument.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_lowTail_of_energyDynamics
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDifferentiable :
      H3PathEnergyClassProducesCanonicalEnergyDifferentiability)
    (hGrowthClosure :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesH3Control := by

  intro u T hH3 hControl

  rcases hControl with
    ⟨g, hgIntegrable, hgEnvelope⟩

  obtain
    ⟨a, hClass⟩ :=
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hbOld :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        ha.2

  have hb :
      b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo_zero
        ha

  have hClassB :
      PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hbOld.1)
      hbOld.2

  obtain
    ⟨L, hLowB⟩ :=
    hLow
      u T hH3
      a hClass
      b hbOld

  have hgTail :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VorticityEnvelope u g t := by

    intro t ht

    exact
      hgEnvelope
        t
        ⟨
          lt_trans hb.1 ht.1,
          ht.2
        ⟩

  have hProfile :
      H3EnergyProfileFrom
        u b T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3 hb

  have hActual :
      ActualVelocityGradientLogBoundFrom
        u b T g
        (velocityH3EnergyAt u)
        (h3BKMCanonicalSelectedLogGradientConstant L) :=
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_lowTail
      hH3.navier_stokes
      hb
      hgTail
      hProfile
      hLowB

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant L

  have hB :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3BKMCanonicalSelectedLogGradientConstant_nonneg_of_lowTail
        hLowB

  let h : ℝ → ℝ :=
    h3BKMLogarithmicGradientEnvelope
      g
      (velocityH3EnergyAt u)
      B

  have hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VelocityGradientEnvelope u h t := by

    intro t ht

    dsimp only [h, B]

    exact
      velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
        hActual
        ht

  have hEndpointBound :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          1 + |h t|
            ≤
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t)) := by

    intro t ht

    have hEt :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    dsimp only [h]

    exact
      one_add_abs_h3BKMLogarithmicGradientEnvelope_le
        hB
        hEt

  have hEnergyGrowth :
      H3GradientGrowthInequalityFrom
        b T h
        (velocityH3EnergyAt u)
        4422 :=
    hGrowthClosure
      u T hH3
      b hClassB
      h
      hGradient

  let C : ℝ :=
    4422 * (B + 1)

  have hC :
      0 ≤ C := by
    dsimp only [C]
    exact
      mul_nonneg
        (by norm_num)
        (by linarith)

  have hGrowth :
      BKMLogGrowthInequalityFrom
        b T g
        (velocityH3EnergyAt u)
        C := by

    intro t ht

    have hEtOne :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    have hEtNonneg :
        0 ≤ velocityH3EnergyAt u t :=
      le_trans
        (by norm_num)
        hEtOne

    have hEndpointAt :
        1 + |h t|
          ≤
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)) :=
      hEndpointBound t ht

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
        hEnergyGrowth t ht

      _ ≤
        4422
          *
        ((B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)))
          * velocityH3EnergyAt u t := by

        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              hEndpointAt
              (by norm_num))
            hEtNonneg

      _ =
        C
          * (1 + |g t|)
          * velocityH3EnergyAt u t
          * (1 + Real.log (velocityH3EnergyAt u t)) := by

        dsimp only [C]
        ring

  have hgTailIntegrable :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo b T) := by

    apply
      hgIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hb.1 ht.1,
        ht.2
      ⟩

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico b T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  have hContinuous :
      ∀ q : ℝ,
        q ∈ Set.Ico b T →
          ContinuousOn
            (velocityH3EnergyAt u)
            (Set.Icc b q) :=
    hH3.canonicalH3EnergyContinuousOnTail
      hb

  have hDerivativeAt :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    intro s hs

    exact
      hDifferentiable
        u T hH3
        b hClassB
        s hs

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      hb.2
      hgTailIntegrable
      hC
      hEOne
      hContinuous
      hDerivativeAt
      hGrowth

  refine
    ⟨
      b,
      M,
      hb,
      hM,
      ?_
    ⟩

  intro t ht

  exact
    velocityH3BoundAt_mono
      (hProfile t ht).2
      (hEM t ht)

/--
H³-path BKM continuation factored at the exact scalar-energy dynamics boundary.

No derivative-order decomposition, PDE pairing package, pressure term, or
diffusion term occurs in this statement.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_energyDynamics
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDifferentiable :
      H3PathEnergyClassProducesCanonicalEnergyDifferentiability)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    h3PathVorticityL1LinfProducesH3Control_of_lowTail_of_energyDynamics
      hLow
      hDifferentiable
      hGrowth
      u T
      hH3
      hControl

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

/--
Compatibility with `H3PathExactEnergyFrontier`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_exactEnergy_via_energyDynamics
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability)
    (hSigns :
      H3PathEnergyClassProducesFullScalarSigns) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_energyDynamics
      hLow
      (h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
        hDerivative)
      (h3PathEnergyClassProducesCanonicalGradientGrowth_of_exactEnergy
        hDerivative
        hPairing
        hSigns)

end

end Euclidean
end Bridge
end PrimeTensor
