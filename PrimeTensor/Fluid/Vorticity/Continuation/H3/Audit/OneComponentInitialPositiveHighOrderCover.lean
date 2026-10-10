import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSignedTransportFTC

/-!
# Initial H³ energy-class coverage from positive-time classical smoothing

The signed transport FTC result used a covering hypothesis, requiring a
`PreterminalH3EnergyClass u a T` with `a < s` for every `0 < s < T`.

Here the cover is derived from concrete high-order spatial regularity of the
*actual* old Navier--Stokes velocity and one genuine pressure witness at every
strictly positive time.  The proof uses `a = s / 2` and the existing
`PreterminalH3EnergyClass` constructor; no properties of the velocity at
zero, and no terminal regularity, are inferred.

The high-order velocity/pressure smoothing is still an explicit analytic
hypothesis. It must not be confused with the weaker open-time admissibility
class, which alone does not furnish fifth-order spatial velocity regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3AuditInitialPositiveHighOrderCover
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At EVERY strict positive preterminal time, the actual logged velocity
has the twice-differentiated spatial C³ regularity needed for the physical
H³ energy balance.  No uniform spatial derivative bound is required. -/
def H3AuditInitialPositiveVelocitySpatialC5
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
    ∀ j i k : PrimeTensor.Axis Depth.three,
      SpatialC3
        (spatial3.d i
          (spatial3.d k (loggedVelocityComponent u s j)))

/-- The same positive-time high-order spatial test for one genuine pressure
of the original Navier--Stokes solution. -/
def H3AuditInitialPositivePressureSpatialC4
    (p : ℝ → ScalarField3)
    (T : ℝ) : Prop :=
  ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
    ∀ i : PrimeTensor.Axis Depth.three,
      SpatialC3 (spatial3.d i (p s))

/-- A concrete high-order *positive-time* smoothness contract for the genuine
old velocity and one genuine Navier--Stokes pressure.  This is stronger than
open-time Navier--Stokes admissibility; parabolic smoothing must supply it. -/
def H3AuditInitialPositiveHighOrderClassicalNavierStokes
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  H3AuditInitialPositiveVelocitySpatialC5 u T ∧
    ∃ p : ℝ → ScalarField3,
      PreterminalNavierStokes3 (logSpaceTimeVectorField u) p T ∧
      H3AuditInitialPositivePressureSpatialC4 p T

/-- From high-order regularity at ALL strict positive times, construct an
actual physical H³ energy class beginning at any earlier positive anchor.
This is a constructor proof, not an extra H³ energy estimate. -/
theorem h3Audit_initialPositiveHighOrderClassicalNS_energyClass_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hSmooth : H3AuditInitialPositiveHighOrderClassicalNavierStokes u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T) :
    PreterminalH3EnergyClass u a T := by
  obtain ⟨hVelocity, p, hPDE, hPressure⟩ := hSmooth
  refine {
    terminal_start := ha
    velocity_spatial_five := ?_
    pressure_witness := ?_
  }
  · intro t ht j i k
    have htPositive : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le ha.1 ht.1, ht.2⟩
    change SpatialC3
      (spatial3.d i (spatial3.d k (loggedVelocityComponent u t j)))
    exact hVelocity t htPositive j i k
  · refine ⟨p, hPDE, ?_⟩
    intro t ht i
    exact hPressure t ⟨lt_of_lt_of_le ha.1 ht.1, ht.2⟩ i

/-- The midpoint choice `a = s/2` closes the abstract initial energy-class
cover from genuine strictly-positive-time high-order spatial regularity. -/
theorem h3Audit_initialPositiveHighOrderClassicalNS_energyClass_cover
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hSmooth : H3AuditInitialPositiveHighOrderClassicalNavierStokes u T) :
    H3AuditInitialPositiveEnergyClassCover (u := u) (T := T) := by
  intro s hs
  let a : ℝ := s / 2
  have haPositive : 0 < a := by
    dsimp only [a]
    linarith [hs.1]
  have haBefore : a < s := by
    dsimp only [a]
    linarith [hs.1]
  have haT : a < T := lt_trans haBefore hs.2
  exact ⟨a,
    h3Audit_initialPositiveHighOrderClassicalNS_energyClass_at
      hSmooth ⟨haPositive, haT⟩,
    ⟨haBefore, hs.2⟩⟩

/-- The exact orderwise energy derivative identities on any initial open
subinterval follow from positive-time high-order classical smoothness. -/
theorem h3Audit_initialPositiveHighOrderClassicalNS_orderwiseDerivatives
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hSmooth : H3AuditInitialPositiveHighOrderClassicalNavierStokes u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
      H3OrderEnergyDerivativeIdentities u s := by
  exact h3Audit_initialPositiveEnergyClassCover_orderwiseDerivatives
    hH3
    (h3Audit_initialPositiveHighOrderClassicalNS_energyClass_cover hSmooth)
    t ht

/-- Initial-time data in which the ABSTRACT energy-class cover has been
replaced by a concrete positive-time C⁵ velocity / C⁴ pressure condition.
The actual velocity source, its initial endpoint continuity, integrability,
and the signed transport upper bound remain explicit hypotheses. -/
def H3AuditInitialPhysicalSignedTransportSmoothData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (V : Fin 3 → ℝ → H3ScalarL2)
    (Cvelocity Ctransport : ℝ),
    0 ≤ Cvelocity ∧ 0 ≤ Ctransport ∧
    H3AuditInitialPositiveHighOrderClassicalNavierStokes u T ∧
    (∀ j : Fin 3, ∀ t : ℝ, ∀ ht : t ∈ Set.Ioo (0 : ℝ) T,
      ContinuousOn
        (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
        (Set.Icc (0 : ℝ) t) ∧
      (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
        HasDerivAt
          (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
          (V j s) s) ∧
      IntervalIntegrable (V j) volume 0 t ∧
      (∀ᵐ s : ℝ ∂volume,
        s ∈ Set.uIoc (0 : ℝ) t → ‖V j s‖ ≤ Cvelocity)) ∧
    (∀ t : ℝ, ∀ ht : t ∈ Set.Ioo (0 : ℝ) T,
      ContinuousOn (velocityH3EnergyAt u) (Set.Icc (0 : ℝ) t) ∧
      IntervalIntegrable (velocityH3FormalDerivativeAt u) volume 0 t) ∧
    (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
      - velocityH3TransportDerivativeAt u s ≤ Ctransport)

/-- The actual positive-time C⁵/C⁴ smoothing condition supplies the abstract
energy-class cover required by the previously proved signed-transport FTC. -/
theorem h3Audit_initialSignedTransportSmooth_implies_signedTransportData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalSignedTransportSmoothData hH3) :
    H3AuditInitialPhysicalSignedTransportFTCData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, V, Cv, Ct,
    hCv, hCt, hSmooth, hVelocity, hEnergy, hTransport⟩ := hData
  exact ⟨hInt0, hMeas0, hFourier0, V, Cv, Ct,
    hCv, hCt, hVelocity, hEnergy,
    h3Audit_initialPositiveHighOrderClassicalNS_energyClass_cover hSmooth,
    hTransport⟩

/-- Strong initial H³ right trace with the energy-class cover removed from
the interface and replaced by positive-time physical high-order smoothness. -/
theorem h3Audit_initialSignedTransportSmooth_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalSignedTransportSmoothData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialSignedTransportFTC_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialSignedTransportSmooth_implies_signedTransportData
      hH3 hData)

/-- Retains the independent actual terminal strong-H³ vorticity endpoint
required by the prior two-component whole-time criterion. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSignedTransportSmooth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalSignedTransportSmoothData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSignedTransportFTC
      hH3 hClass i hPhysical
      (h3Audit_initialSignedTransportSmooth_implies_signedTransportData
        hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
