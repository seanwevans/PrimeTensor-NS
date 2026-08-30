import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalSeedBridge

/-!
# Classicalization: canonical spectral path of the preterminal solution

The seed bridge identifies the classicalization H³ anchor with the older BKM
seed interface.  The next overlap requirement is path-level rather than
snapshot-level.

Fix an anchor time `t` and an elapsed interval `[0,τ]` lying strictly before
the old terminal time `T`.  If every old solution slice `t + q` on this
interval is H³-integrable, then preterminal spatial `C³` regularity
automatically supplies measurability and Fourier compatibility at every slice.
Hence there is a canonical weighted spectral H³ state at every elapsed time.

This file packages those states into an actual
`H3SpectralPhysicalVelocityPath τ` under exactly one additional topological
hypothesis: continuity of the canonical spectral-state map.

A uniform canonical H³-energy bound by `2A` gives the Picard-ball bound
automatically.  The real decoder of every path slice, in particular the right
endpoint, agrees almost everywhere with the old logged velocity.

Consequently construction of `H3PreterminalSpectralOverlapWitnessAt` is reduced
to two genuinely analytic time-evolution statements:

1. H³ persistence/energy control plus continuity of the canonical spectral
   path;
2. the restarted heat--Leray mild identity for that path.

No Fourier or endpoint-decoder bookkeeping remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPreterminalCanonicalPath
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3SchwartzClassicalizationPreterminalCanonicalPath :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every elapsed time in `[0,τ]` remains strictly preterminal provided the
right endpoint `t + τ` is strictly before `T`. -/
theorem h3PreterminalElapsedTime_mem_Ioo
    {T t τ : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (q : Set.Icc (0 : ℝ) τ) :
    t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
  constructor
  · linarith [ht.1, q.property.1]
  · linarith [hEnd, q.property.2]

/-- Canonical weighted spectral H³ state of the old preterminal solution at
elapsed time `q` from anchor `t`.

The measurability and Fourier-compatibility witnesses are generated
canonically from the preterminal `C³` structure. -/
noncomputable def h3PreterminalCanonicalSpectralStateOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (q : Set.Icc (0 : ℝ) τ) :
    H3SpectralVelocityState :=
  let hs : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q
  let hIq : VelocityH3IntegrableAt u (t + (q : ℝ)) :=
    hInt q
  let hMeas : VelocityH3MeasurableAt u (t + (q : ℝ)) :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs
  let hFourier :
      VelocityH3FourierCompatibleAt
        u (t + (q : ℝ)) hIq hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS hs hIq
  velocityH3SpectralStateAt
    u (t + (q : ℝ)) hIq hMeas hFourier

/-- Canonical spectral state at the restart anchor itself. -/
noncomputable def h3PreterminalCanonicalAnchorSpectralState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t) :
    H3SpectralVelocityState :=
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht
  let hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt
  velocityH3SpectralStateAt
    u t hInt hMeas hFourier

/-- A `2A` canonical-energy bound gives the same `2A` norm bound for every
canonical spectral slice. -/
theorem norm_h3PreterminalCanonicalSpectralStateOnElapsed_le_twoA
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ A : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hA : 1 ≤ A)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (hEnergy :
      ∀ q : Set.Icc (0 : ℝ) τ,
        velocityH3EnergyAt u (t + (q : ℝ)) ≤ 2 * A)
    (q : Set.Icc (0 : ℝ) τ) :
    ‖h3PreterminalCanonicalSpectralStateOnElapsed
        hNS ht hEnd hInt q‖
      ≤
    2 * A := by
  let hs : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  let hIq : VelocityH3IntegrableAt u (t + (q : ℝ)) :=
    hInt q

  let hMeas : VelocityH3MeasurableAt u (t + (q : ℝ)) :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u (t + (q : ℝ)) hIq hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS hs hIq

  have hTwoA : 1 ≤ 2 * A := by
    linarith

  change
    ‖velocityH3SpectralStateAt
        u (t + (q : ℝ)) hIq hMeas hFourier‖
      ≤
    2 * A

  exact
    norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier hTwoA (hEnergy q)

/-- The canonical spectral slice decodes almost everywhere to the old logged
velocity at the corresponding elapsed time. -/
theorem h3PreterminalCanonicalSpectralStateOnElapsed_decode_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (q : Set.Icc (0 : ℝ) τ)
    (j : Fin 3) :
    ∀ᵐ x : Point3 ∂volume,
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3PreterminalCanonicalSpectralStateOnElapsed
              hNS ht hEnd hInt q)
            j)
          x
        =
      (logSpaceTimeVectorField
          u
          (t + (q : ℝ))
          x).component
        (h3AxisOfFin3 j) := by
  let hs : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  let hIq : VelocityH3IntegrableAt u (t + (q : ℝ)) :=
    hInt q

  let hMeas : VelocityH3MeasurableAt u (t + (q : ℝ)) :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u (t + (q : ℝ)) hIq hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS hs hIq

  have hDecode :
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (velocityH3SpectralStateAt
              u (t + (q : ℝ)) hIq hMeas hFourier)
            j)
        =
      velocityH3L2JetAt
        u (t + (q : ℝ)) hIq hMeas
        (h3JetSlot0 j) :=
    h3FromFourierRealL2_h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_eq
      hFourier j

  have hAE :
      ((velocityH3L2JetAt
          u (t + (q : ℝ)) hIq hMeas
          (h3JetSlot0 j) : H3ScalarL2) :
        Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u (t + (q : ℝ))
        (h3AxisOfFin3 j) :=
    velocityH3L2JetAt_slot0_ae_eq_loggedVelocityComponent
      hIq hMeas j

  filter_upwards [hAE] with x hx

  change
    h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (velocityH3SpectralStateAt
            u (t + (q : ℝ)) hIq hMeas hFourier)
          j)
        x
      =
    (logSpaceTimeVectorField
        u
        (t + (q : ℝ))
        x).component
      (h3AxisOfFin3 j)

  rw [hDecode]

  change
    ((velocityH3L2JetAt
        u (t + (q : ℝ)) hIq hMeas
        (h3JetSlot0 j) : H3ScalarL2) :
      Point3 → ℝ) x
      =
    loggedVelocityComponent
      u (t + (q : ℝ))
      (h3AxisOfFin3 j) x

  exact hx

/-- Package the canonical preterminal spectral-state map into a bounded
continuous physical path.

All boundedness is derived from the canonical H³ energy.  Continuity of the
state map is the only additional hypothesis. -/
noncomputable def h3PreterminalCanonicalSpectralPhysicalPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ A : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hA : 1 ≤ A)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (hEnergy :
      ∀ q : Set.Icc (0 : ℝ) τ,
        velocityH3EnergyAt u (t + (q : ℝ)) ≤ 2 * A)
    (hCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3PreterminalCanonicalSpectralStateOnElapsed
            hNS ht hEnd hInt q)) :
    H3SpectralPhysicalVelocityPath τ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q : Set.Icc (0 : ℝ) τ =>
      h3PreterminalCanonicalSpectralStateOnElapsed
        hNS ht hEnd hInt q)
    hCont
    (2 * A)
    (fun q =>
      norm_h3PreterminalCanonicalSpectralStateOnElapsed_le_twoA
        hNS ht hEnd hA hInt hEnergy q)

@[simp]
theorem h3PreterminalCanonicalSpectralPhysicalPath_apply
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ A : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hA : 1 ≤ A)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (hEnergy :
      ∀ q : Set.Icc (0 : ℝ) τ,
        velocityH3EnergyAt u (t + (q : ℝ)) ≤ 2 * A)
    (hCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3PreterminalCanonicalSpectralStateOnElapsed
            hNS ht hEnd hInt q))
    (q : Set.Icc (0 : ℝ) τ) :
    h3PreterminalCanonicalSpectralPhysicalPath
        hNS ht hEnd hA hInt hEnergy hCont q
      =
    h3PreterminalCanonicalSpectralStateOnElapsed
      hNS ht hEnd hInt q :=
  rfl

/-- Every slice of the packaged canonical preterminal path lies in the `2A`
Picard ball. -/
theorem norm_h3PreterminalCanonicalSpectralPhysicalPath_apply_le_twoA
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ A : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hA : 1 ≤ A)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (hEnergy :
      ∀ q : Set.Icc (0 : ℝ) τ,
        velocityH3EnergyAt u (t + (q : ℝ)) ≤ 2 * A)
    (hCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3PreterminalCanonicalSpectralStateOnElapsed
            hNS ht hEnd hInt q))
    (q : Set.Icc (0 : ℝ) τ) :
    ‖h3PreterminalCanonicalSpectralPhysicalPath
        hNS ht hEnd hA hInt hEnergy hCont q‖
      ≤
    2 * A := by
  rw [h3PreterminalCanonicalSpectralPhysicalPath_apply]
  exact
    norm_h3PreterminalCanonicalSpectralStateOnElapsed_le_twoA
      hNS ht hEnd hA hInt hEnergy q

/-- The packaged canonical preterminal path decodes almost everywhere to the
old logged velocity at every elapsed time. -/
theorem h3PreterminalCanonicalSpectralPhysicalPath_decode_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ A : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hA : 1 ≤ A)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (hEnergy :
      ∀ q : Set.Icc (0 : ℝ) τ,
        velocityH3EnergyAt u (t + (q : ℝ)) ≤ 2 * A)
    (hCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3PreterminalCanonicalSpectralStateOnElapsed
            hNS ht hEnd hInt q))
    (q : Set.Icc (0 : ℝ) τ)
    (j : Fin 3) :
    ∀ᵐ x : Point3 ∂volume,
      h3FromFourierRealL2
          (h3SpectralVelocityDecodeRealL2
            (h3PreterminalCanonicalSpectralPhysicalPath
              hNS ht hEnd hA hInt hEnergy hCont q)
            j)
          x
        =
      (logSpaceTimeVectorField
          u
          (t + (q : ℝ))
          x).component
        (h3AxisOfFin3 j) := by
  simpa only [
    h3PreterminalCanonicalSpectralPhysicalPath_apply
  ] using
    h3PreterminalCanonicalSpectralStateOnElapsed_decode_ae
      hNS ht hEnd hInt q j

/-- Once the canonical preterminal spectral path is known to satisfy the
restarted heat--Leray mild equation, it is exactly the local overlap witness
required by the uniqueness/gluing stack.

The endpoint decoder and the `2A` path bound are supplied automatically by the
canonical path construction. -/
theorem h3PreterminalSpectralOverlapWitnessAt_of_canonicalPath
    {ν A : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 ≤ τ)
    (hEnd : t + τ < T)
    (hA : 1 ≤ A)
    (hInt0 : VelocityH3IntegrableAt u t)
    (hInt :
      ∀ q : Set.Icc (0 : ℝ) τ,
        VelocityH3IntegrableAt u (t + (q : ℝ)))
    (hEnergy :
      ∀ q : Set.Icc (0 : ℝ) τ,
        velocityH3EnergyAt u (t + (q : ℝ)) ≤ 2 * A)
    (hCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3PreterminalCanonicalSpectralStateOnElapsed
            hNS ht hEnd hInt q))
    (hMild :
      ∀ s : H3UnitTime,
        h3SpectralVelocityHeatApplyNN
            ν hν.le
            (h3PhysicalTimeNN τ hτ s)
            (h3PreterminalCanonicalAnchorSpectralState
              hNS ht hInt0)
          +
        h3SpectralFinHeatLerayDuhamel
            ν
            (h3PhysicalTime τ s)
            hν
            (h3PathPhysicalRealExtension
              τ
              (h3SpectralNormalizedPathOfPhysical
                hτ
                (h3PreterminalCanonicalSpectralPhysicalPath
                  hNS ht hEnd hA hInt hEnergy hCont)))
            (h3PathPhysicalRealExtension
              τ
              (h3SpectralNormalizedPathOfPhysical
                hτ
                (h3PreterminalCanonicalSpectralPhysicalPath
                  hNS ht hEnd hA hInt hEnergy hCont)))
          =
        h3PreterminalCanonicalSpectralPhysicalPath
          hNS ht hEnd hA hInt hEnergy hCont
          (h3PhysicalTimeMap τ hτ s)) :
    H3PreterminalSpectralOverlapWitnessAt
      ν A hν
      (h3PreterminalCanonicalAnchorSpectralState
        hNS ht hInt0)
      u t τ hτ := by
  let P : H3SpectralPhysicalVelocityPath τ :=
    h3PreterminalCanonicalSpectralPhysicalPath
      hNS ht hEnd hA hInt hEnergy hCont

  refine
    ⟨
      P,
      ?_,
      ?_,
      ?_
    ⟩

  · intro q

    exact
      norm_h3PreterminalCanonicalSpectralPhysicalPath_apply_le_twoA
        hNS ht hEnd hA hInt hEnergy hCont q

  · intro s

    exact hMild s

  · intro j

    let qEnd : Set.Icc (0 : ℝ) τ :=
      h3PhysicalTimeMap τ hτ h3UnitTimeOne

    have hAE :
        ∀ᵐ x : Point3 ∂volume,
          h3FromFourierRealL2
              (h3SpectralVelocityDecodeRealL2
                (P qEnd)
                j)
              x
            =
          (logSpaceTimeVectorField
              u
              (t + (qEnd : ℝ))
              x).component
            (h3AxisOfFin3 j) := by
      exact
        h3PreterminalCanonicalSpectralPhysicalPath_decode_ae
          hNS ht hEnd hA hInt hEnergy hCont qEnd j

    have hEndTime :
        (qEnd : ℝ) = τ := by
      change h3PhysicalTime τ h3UnitTimeOne = τ
      exact h3PhysicalTime_one τ

    rw [hEndTime] at hAE

    exact hAE

end
end Euclidean
end Bridge
end PrimeTensor
