import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.IntegrabilityDichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Absorption.Continuation

/-!
# Terminal nonintegrability of adverse H³ transport

The preceding decay/transport integrability dichotomy was deliberately neutral:

    max(0, -E') ∉ L¹
      or
    max(0, -T_H3) ∉ L¹.

However, the exact balance contains a stronger one-sided fact:

    E'(t) + 2 D(t) = -T_H3(t),

hence

    E'(t) ≤ -T_H3(t).

Therefore the adverse transport positive part

    c(t) = max(0, -T_H3(t))

is itself a valid scalar growth majorant.  More directly, since `E_H3 ≥ 1`
and `D ≥ 0`,

    -T_H3(t) ≤ D(t) + c(t) E_H3(t).

Thus if `c` were integrable on one terminal H³ energy-class tail, the existing
transport/dissipation absorption Grönwall argument would give uniform terminal
H³ control and the closed restart theorem would extend the path.

Consequently hypothetical nonextension forces

    max(0, -T_H3) ∉ L¹(a,T)

on every terminal H³ energy-class tail.

This does not rule out simultaneous nonintegrability of the negative energy
variation.  It only shows that adverse transport is an unavoidable pathology
on the nonextension branch, rather than merely one side of an alternative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Path-specific one-tail absorption continuation -/

/--
A single terminal H³ energy-class tail carrying an integrable absorption
coefficient is already enough to continue the given path.

This is the path-specific version of the universal absorption theorem.
-/
theorem h3PathExtension_of_transportDissipationAbsorptionOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    {c : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hcIntegrable :
      MeasureTheory.IntegrableOn
        c
        (Set.Ioo a T))
    (hAbsorb :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          H3TransportDissipationAbsorptionAt
            u c t) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hProfile :
      H3EnergyProfileFrom
        u a T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3 ha

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  have hContinuous :
      ∀ q : ℝ,
        q ∈ Set.Ico a T →
          ContinuousOn
            (velocityH3EnergyAt u)
            (Set.Icc a q) :=
    hH3.canonicalH3EnergyContinuousOnTail
      ha

  have hDerivativeAt :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    intro s hs

    have hIds :
        H3OrderEnergyDerivativeIdentities u s :=
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3
        a hClass
        s hs

    have hDeriv :
        deriv (velocityH3EnergyAt u) s
          =
        velocityH3FormalDerivativeAt u s :=
      deriv_velocityH3EnergyAt
        hIds

    rw [hDeriv]

    exact
      hasDerivAt_velocityH3EnergyAt
        hIds

  have hLinearGrowth :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          deriv (velocityH3EnergyAt u) s
            ≤
          c s * velocityH3EnergyAt u s := by

    intro s hs

    exact
      deriv_velocityH3EnergyAt_le_of_transportAbsorption
        hH3
        hClass
        hs
        (hAbsorb s hs)

  have hGrowth :
      BKMLogGrowthInequalityFrom
        a T
        c
        (velocityH3EnergyAt u)
        1 := by

    intro s hs

    have hEsOne :
        1 ≤ velocityH3EnergyAt u s :=
      hEOne
        s
        ⟨
          le_of_lt hs.1,
          hs.2
        ⟩

    have hEsNonneg :
        0 ≤ velocityH3EnergyAt u s := by
      linarith

    have hLogNonneg :
        0 ≤ Real.log (velocityH3EnergyAt u s) :=
      Real.log_nonneg
        hEsOne

    have hcUpper :
        c s ≤ 1 + |c s| := by
      have hle :
          c s ≤ |c s| :=
        le_abs_self (c s)
      linarith

    have hFirst :
        c s * velocityH3EnergyAt u s
          ≤
        (1 + |c s|)
          * velocityH3EnergyAt u s :=
      mul_le_mul_of_nonneg_right
        hcUpper
        hEsNonneg

    have hCoeffNonneg :
        0 ≤
          (1 + |c s|)
            * velocityH3EnergyAt u s :=
      mul_nonneg
        (by positivity)
        hEsNonneg

    have hLogFactor :
        1 ≤ 1 + Real.log (velocityH3EnergyAt u s) := by
      linarith

    calc
      deriv (velocityH3EnergyAt u) s
          ≤
        c s * velocityH3EnergyAt u s :=
        hLinearGrowth s hs

      _ ≤
        (1 + |c s|)
          * velocityH3EnergyAt u s :=
        hFirst

      _ ≤
        ((1 + |c s|)
          * velocityH3EnergyAt u s)
          *
        (1 + Real.log (velocityH3EnergyAt u s)) := by

        exact
          le_mul_of_one_le_right
            hCoeffNonneg
            hLogFactor

      _ =
        (1 : ℝ)
          * (1 + |c s|)
          * velocityH3EnergyAt u s
          * (1 + Real.log (velocityH3EnergyAt u s)) := by
        ring

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      ha.2
      hcIntegrable
      (by norm_num)
      hEOne
      hContinuous
      hDerivativeAt
      hGrowth

  have hTail :
      TerminalTailH3Control u T := by

    refine
      ⟨
        a,
        M,
        ha,
        hM,
        ?_
      ⟩

    intro t ht

    exact
      velocityH3BoundAt_mono
        (hProfile t ht).2
        (hEM t ht)

  exact
    h3PathH3ControlProducesExtension
      u T hH3 hTail

/-! ## Adverse transport is itself an absorption coefficient -/

/--
The positive part of `-T_H3` always supplies a valid one-copy
transport/dissipation absorption coefficient.
-/
theorem h3TransportDissipationAbsorptionAt_negativeTransportPart
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    H3TransportDissipationAbsorptionAt
      u
      (h3PathNegativeTransportPart u)
      t := by

  have hTransport :
      - velocityH3TransportDerivativeAt u t
        ≤
      h3PathNegativeTransportPart u t := by

    unfold h3PathNegativeTransportPart

    exact
      le_max_right
        0
        (- velocityH3TransportDerivativeAt u t)

  have hCNonneg :
      0 ≤ h3PathNegativeTransportPart u t :=
    h3PathNegativeTransportPart_nonneg
      u t

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hScaled :
      h3PathNegativeTransportPart u t
        ≤
      h3PathNegativeTransportPart u t
        * velocityH3EnergyAt u t := by

    calc
      h3PathNegativeTransportPart u t
          =
        h3PathNegativeTransportPart u t * 1 := by
        ring

      _ ≤
        h3PathNegativeTransportPart u t
          * velocityH3EnergyAt u t :=
        mul_le_mul_of_nonneg_left
          hEOne
          hCNonneg

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg
      u t

  unfold H3TransportDissipationAbsorptionAt

  linarith

/-! ## One-tail adverse-transport continuation -/

/--
If the adverse H³ transport positive part is integrable on one terminal
energy-class tail, the path extends smoothly through the terminal time.
-/
theorem h3PathExtension_of_integrableNegativeTransportPartOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTransport :
      MeasureTheory.IntegrableOn
        (h3PathNegativeTransportPart u)
        (Set.Ioo a T)) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  exact
    h3PathExtension_of_transportDissipationAbsorptionOnTail
      hH3
      hClass
      hTransport
      (fun t _ =>
        h3TransportDissipationAbsorptionAt_negativeTransportPart
          u t)

/--
Therefore hypothetical nonextension forces adverse H³ transport to have
infinite positive-part mass on every terminal H³ energy-class tail.
-/
theorem not_integrableOn_negativeTransportPart_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (h3PathNegativeTransportPart u)
        (Set.Ioo a T) := by

  intro hTransport

  exact
    hNoExtension
      (h3PathExtension_of_integrableNegativeTransportPartOnTail
        hH3
        hClass
        hTransport)


end

end Euclidean
end Bridge
end PrimeTensor
