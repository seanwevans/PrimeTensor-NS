import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Overlap.Witness
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Preterminal.Canonical.Energy.Restart.Closure

/-!
# Classicalization: canonical preterminal spectral slices

`PreterminalOverlapWitness` isolates the remaining overlap problem as the
construction of a bounded physical spectral path representing the old
preterminal solution.

Before building a path, one must be able to encode each individual old
solution slice into the concrete weighted spectral H³ state space.

For an interior preterminal time `s`, spatial `C³` regularity is already part
of `LoggedPreterminalNavierStokesAdmissible`.  Therefore, once H³
integrability at `s` is supplied,

* H³ measurability is automatic;
* Fourier derivative compatibility is automatic;
* the canonical spectral state has norm bounded by any normalized H³ energy
  ceiling;
* its real `L²` decoder agrees almost everywhere with the old logged velocity.

This file packages exactly that slice-level statement.  It deliberately does
not assume or prove H³ persistence in time.  Consequently the remaining
analytic obstruction is now explicit: propagate `VelocityH3IntegrableAt` (and
a suitable energy bound) from the anchor slice to the short preterminal
overlap.  Once that is available, every later slice has the canonical spectral
realization proved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPreterminalSpectralSlice
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3SchwartzClassicalizationPreterminalSpectralSlice :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A canonical spectral realization of one H³-integrable interior slice of
the old preterminal classical solution.

The existential proof objects are exactly the automatically generated
measurability and Fourier-compatibility witnesses.  The actual mathematical
output is the weighted spectral state, its norm bound, and its a.e. real
decoder identity. -/
theorem h3PreterminalSpectralSlice_exists
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s B : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hB : 1 ≤ B)
    (hInt : VelocityH3IntegrableAt u s)
    (hEnergy : velocityH3EnergyAt u s ≤ B) :
    ∃
      (hMeas : VelocityH3MeasurableAt u s)
      (hFourier : VelocityH3FourierCompatibleAt u s hInt hMeas),
      let U : H3SpectralVelocityState :=
        velocityH3SpectralStateAt u s hInt hMeas hFourier
      ‖U‖ ≤ B
        ∧
      ∀ j : Fin 3,
        ∀ᵐ x : Point3 ∂volume,
          h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2 U j)
              x
            =
          (logSpaceTimeVectorField u s x).component
            (h3AxisOfFin3 j) := by
  let hMeas : VelocityH3MeasurableAt u s :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  let hFourier : VelocityH3FourierCompatibleAt u s hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS hs hInt

  refine
    ⟨
      hMeas,
      hFourier,
      ?_,
      ?_
    ⟩

  · exact
      norm_velocityH3SpectralStateAt_le_energyCeiling
        hFourier hB hEnergy

  · intro j

    have hDecode :
        h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2
              (velocityH3SpectralStateAt
                u s hInt hMeas hFourier)
              j)
          =
        velocityH3L2JetAt
          u s hInt hMeas
          (h3JetSlot0 j) :=
      h3FromFourierRealL2_h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_eq
        hFourier j

    have hAE :
        ((velocityH3L2JetAt
            u s hInt hMeas
            (h3JetSlot0 j) : H3ScalarL2) :
          Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        loggedVelocityComponent
          u s (h3AxisOfFin3 j) :=
      velocityH3L2JetAt_slot0_ae_eq_loggedVelocityComponent
        hInt hMeas j

    filter_upwards [hAE] with x hx

    rw [hDecode]

    change
      ((velocityH3L2JetAt
          u s hInt hMeas
          (h3JetSlot0 j) : H3ScalarL2) :
        Point3 → ℝ) x
        =
      loggedVelocityComponent
        u s (h3AxisOfFin3 j) x

    exact hx

/-- The same slice package with the norm bound stated directly at the
canonical normalized energy of the slice itself.

This is the form most convenient after an H³-persistence theorem produces
integrability but no separately chosen scalar ceiling. -/
theorem h3PreterminalSpectralSlice_at_canonicalEnergy_exists
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u s) :
    ∃
      (hMeas : VelocityH3MeasurableAt u s)
      (hFourier : VelocityH3FourierCompatibleAt u s hInt hMeas),
      let U : H3SpectralVelocityState :=
        velocityH3SpectralStateAt u s hInt hMeas hFourier
      ‖U‖ ≤ velocityH3EnergyAt u s
        ∧
      ∀ j : Fin 3,
        ∀ᵐ x : Point3 ∂volume,
          h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2 U j)
              x
            =
          (logSpaceTimeVectorField u s x).component
            (h3AxisOfFin3 j) := by
  apply
    h3PreterminalSpectralSlice_exists
      hNS
      hs
      (one_le_velocityH3EnergyAt u s)
      hInt
      le_rfl

end
end Euclidean
end Bridge
end PrimeTensor
