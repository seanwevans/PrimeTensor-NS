import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile

/-!
# Local integrability of the cubic forcing obstruction

The cubic forcing profile is continuous on the whole strict physical interval
`(a,T)`.  Therefore it is locally integrable there, and in particular
integrable on every compact interval lying strictly inside `(a,T)`.

This separates the already-proved infinite total mass on a nonextension branch
from any interior singularity: no compact strict subinterval can carry an
integrability obstruction.  Any remaining infinite mass must accumulate at an
endpoint of the open interval.

A later checkpoint can isolate the left endpoint `a`; once that side is shown
finite, the obstruction becomes genuinely terminal at `T`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingProfileLocal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 600000

/--
The continuous full cubic forcing mass profile is locally integrable throughout
the strict physical interval.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_locallyIntegrableOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    LocallyIntegrableOn
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass
      )
      (Set.Ioo a T)
      volume := by

  exact
    ContinuousOn.locallyIntegrableOn
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
          hH3 hClass
      )
      measurableSet_Ioo

/--
Every compact interval `[b,c]` strictly contained in `(a,T)` carries finite
cubic forcing mass.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_integrableOn_Icc
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hc : c ∈ Set.Ioo a T) :
    IntegrableOn
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass
      )
      (Set.Icc b c)
      volume := by

  have hCont :
      ContinuousOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Icc b c) := by

    apply
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
          hH3 hClass
      ).mono

    intro t ht

    exact
      ⟨
        lt_of_lt_of_le
          hb.1
          ht.1,
        lt_of_le_of_lt
          ht.2
          hc.2
      ⟩

  exact
    hCont.integrableOn_Icc

/--
Equivalently, the cubic forcing profile is interval-integrable between any two
strict physical times.
-/
theorem h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_intervalIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hc : c ∈ Set.Ioo a T) :
    IntervalIntegrable
      (
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass
      )
      volume
      b
      c := by

  apply
    ContinuousOn.intervalIntegrable

  have hCont :
      ContinuousOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T) :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
      hH3 hClass

  exact
    hCont.mono
      (by
        intro t ht

        have htIcc :
            t ∈ Set.Icc (min b c) (max b c) := by
          simpa [uIcc] using ht

        constructor

        · have hmin :
              a < min b c :=
            lt_min
              hb.1
              hc.1

          exact
            lt_of_lt_of_le
              hmin
              htIcc.1

        · have hmax :
              max b c < T :=
            max_lt
              hb.2
              hc.2

          exact
            lt_of_le_of_lt
              htIcc.2
              hmax)

end

end Euclidean
end Bridge
end PrimeTensor
