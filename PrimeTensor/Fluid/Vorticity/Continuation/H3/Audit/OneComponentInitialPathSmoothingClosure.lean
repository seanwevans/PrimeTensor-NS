import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPositiveHighOrderCover
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.H3.Path.Admissible

/-!
# Initial energy-class covering from the existing H³-path sliding restart

The preceding audit required positive-time C⁵ velocity and C⁴ pressure as a
separate smoothing hypothesis. The established sliding-window theorem for
`LoggedPreterminalH3PathAdmissible` already provides a canonical bounded
restart window surrounding *each* strictly positive old time `s`.

Selected/old uniqueness transfers the selected C⁵ velocity to the original
old velocity on each such window. Pressure-gradient uniqueness transfers
selected C⁴ pressure to the original preterminal pressure witness. The
window may depend on `s`: there is no uniform H³ bound near the terminal
candidate `T` and no assumption of an extension through `T`.

Consequently the positive-time energy-class cover follows directly from the
preterminal H³ path. This removes the smoothing hypothesis from the initial
signed-transport FTC criterion entirely. The genuine t=0 initial data,
physical temporal derivative, initial-time continuity/integrability, and
signed transport upper estimate remain separate analytical obligations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3AuditInitialPathSmoothingClosure
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The standard H³ path supplies the required fifth-order spatial
regularity of the actual old velocity at every positive time, using a
possibly different sliding restart window at each time. -/
theorem h3Audit_h3Path_positiveVelocitySpatialC5
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    H3AuditInitialPositiveVelocitySpatialC5 u T := by
  intro s hs j i k
  obtain ⟨t₀, S, E, ht₀, hST, hE, hTail,
      hq0, hqR, hts, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  have hS : 0 < S := lt_trans ht₀.1 ht₀.2
  have hNSShort : LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hS (le_of_lt hST)
  have hOld :=
    h3Preterminal_oldVelocity_secondPartial_spatialC3_of_canonicalTail
      (q := s - t₀) hNSShort ht₀ hE hTail hq0 (le_of_lt hqR)
      (by simpa only [hts] using hsS) j i k
  simpa only [hts] using hOld

/-- One genuine pressure witness of the old Navier--Stokes solution has
spatial C⁴ at *every* positive time. Each short restart may choose a
pressure with a different additive gauge; the existing pressure-gradient
uniqueness theorem handles this without requiring pressure equality. -/
theorem h3Audit_h3Path_positivePressureSpatialC4
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ∃ p : ℝ → ScalarField3,
      PreterminalNavierStokes3 (logSpaceTimeVectorField u) p T ∧
      H3AuditInitialPositivePressureSpatialC4 p T := by
  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hH3.navier_stokes
  have hPDE :
      PreterminalNavierStokes3 (logSpaceTimeVectorField u) pOld T := by
    dsimp only [pOld]
    exact Classical.choose_spec hH3.navier_stokes
  refine ⟨pOld, hPDE, ?_⟩
  intro s hs i
  obtain ⟨t₀, S, E, ht₀, hST, hE, hTail,
      hq0, hqR, hts, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  have hS : 0 < S := lt_trans ht₀.1 ht₀.2
  have hPDEShort :
      PreterminalNavierStokes3 (logSpaceTimeVectorField u) pOld S :=
    hPDE.mono_terminal hS (le_of_lt hST)
  let hNSShort : LoggedPreterminalNavierStokesAdmissible u S :=
    ⟨pOld, hPDEShort⟩
  have hOld :=
    h3Preterminal_pressureWitness_spatialDerivative_spatialC3_of_canonicalTail
      (q := s - t₀) hNSShort pOld hPDEShort ht₀ hE hTail
      hq0 hqR (by simpa only [hts] using hsS) i
  simpa only [hts] using hOld

/-- **Unconditional relative to H³-path admissibility:** the abstract
positive-time C⁵/C⁴ smoothing contract used by the previous audit is
already a theorem. It is NOT deduced from the weaker open-time classical
Navier--Stokes predicate alone. -/
theorem h3Audit_h3Path_positiveHighOrderClassicalNS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    H3AuditInitialPositiveHighOrderClassicalNavierStokes u T := by
  exact ⟨
    h3Audit_h3Path_positiveVelocitySpatialC5 hH3,
    h3Audit_h3Path_positivePressureSpatialC4 hH3⟩

/-- The initial energy-class covering assumption is a *closed theorem* for
every existing H³-path-admissible solution: no separately supplied high-order
smoothing premise is required. -/
theorem h3Audit_h3Path_positiveEnergyClassCover
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    H3AuditInitialPositiveEnergyClassCover (u := u) (T := T) := by
  exact h3Audit_initialPositiveHighOrderClassicalNS_energyClass_cover
    (h3Audit_h3Path_positiveHighOrderClassicalNS hH3)

/-- The actual NS energy derivative identities on every initial positive
subinterval also need no separate C⁵/C⁴ or energy-class assumption. -/
theorem h3Audit_h3Path_initialOrderwiseEnergyDerivatives
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
      H3OrderEnergyDerivativeIdentities u s := by
  exact h3Audit_initialPositiveEnergyClassCover_orderwiseDerivatives
    hH3 (h3Audit_h3Path_positiveEnergyClassCover hH3) t ht

/-- Reduced initial signed-transport contract. Compared with the previous
`...SignedTransportSmoothData`, it contains NEITHER a positive-time
energy-class cover NOR an assumed C⁵/C⁴ smoothing fact. Both follow from
`hH3` by the sliding canonical restart and the old-branch overlap theorem.

Initial-time continuity/integrability and transport estimates remain explicit.
-/
def H3AuditInitialPhysicalSignedTransportCoreData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (V : Fin 3 → ℝ → H3ScalarL2)
    (Cvelocity Ctransport : ℝ),
    0 ≤ Cvelocity ∧ 0 ≤ Ctransport ∧
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

/-- The actual H³ path itself discharges the entire high-order smoothing
and covering portion of the previous signed-transport FTC data record. -/
theorem h3Audit_initialSignedTransportCore_implies_signedTransportData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalSignedTransportCoreData hH3) :
    H3AuditInitialPhysicalSignedTransportFTCData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, V, Cv, Ct,
    hCv, hCt, hVelocity, hEnergy, hTransport⟩ := hData
  exact ⟨hInt0, hMeas0, hFourier0, V, Cv, Ct,
    hCv, hCt, hVelocity, hEnergy,
    h3Audit_h3Path_positiveEnergyClassCover hH3, hTransport⟩

/-- Strong initial H³ right trace of the actual velocity without an extra
positive-time high-order smoothing or energy-class covering hypothesis. -/
theorem h3Audit_initialSignedTransportCore_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalSignedTransportCoreData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialSignedTransportFTC_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialSignedTransportCore_implies_signedTransportData hH3 hData)

/-- The full-time two-transverse-component consequence still needs the
separate strong terminal physical vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSignedTransportCore
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalSignedTransportCoreData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSignedTransportFTC
    hH3 hClass i hPhysical
    (h3Audit_initialSignedTransportCore_implies_signedTransportData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
