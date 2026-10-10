import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalDifferentiatedFTC
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact

/-!
# Initial H³ derivative upper bound from actual signed NS transport

The preceding initial-time differentiated FTC criterion required a uniform
upper bound for the *full* canonical H³ energy derivative. That is stronger
than necessary: its dissipative part may be arbitrarily negative.

The already-proved physical Navier--Stokes balance on positive H³ energy
classes reads

  E'(s) + 2 D(s) = - Transport(s),     D(s) >= 0.

Consequently, any upper bound on the signed transport source bounds E'(s)
from above, regardless of the size of viscous dissipation. To apply the
previous closed-interval scalar FTC, the formal derivative at the single
point s=0 is absorbed into a harmless maximum; no PDE balance is asserted
at that excluded endpoint.

What remains explicit:
* covering every positive initial time by an admissible H³ energy class;
* actual anchored physical L² derivative and temporal source bounds;
* continuity at the initial endpoint and integrability of the energy rate;
* an upper bound on the signed transport source on (0,T).

None of these follows merely from open-time path admissibility. No terminal
endpoint is deduced by this initial-time result.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- Exact dissipation changes the initial upper energy-derivative question
into a signed transport upper bound. -/
theorem h3Audit_formalH3Derivative_le_of_signedTransportUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hTransport : - velocityH3TransportDerivativeAt u s ≤ C) :
    velocityH3FormalDerivativeAt u s ≤ C := by
  have hIds : H3OrderEnergyDerivativeIdentities u s :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3 a hClass s hs
  have hDerivative :
      deriv (velocityH3EnergyAt u) s =
        velocityH3FormalDerivativeAt u s :=
    deriv_velocityH3EnergyAt hIds
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hs
  have hDissipation : 0 ≤ velocityH3DissipationAt u s :=
    velocityH3DissipationAt_nonneg u s
  linarith

/-- This is the precise positive-time covering hypothesis needed to use
existing, already closed energy-class Navier--Stokes balance theorems near
initial time. Unlike a single fixed tail a>0, it covers every 0<s<T. -/
def H3AuditInitialPositiveEnergyClassCover
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} : Prop :=
  ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
    ∃ (a : ℝ) (hClass : PreterminalH3EnergyClass u a T),
      s ∈ Set.Ioo a T

/-- An initial-data contract whose energy-side rate assumption is directly
on the signed NS transport, rather than on the full energy derivative. -/
def H3AuditInitialPhysicalSignedTransportFTCData
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
    H3AuditInitialPositiveEnergyClassCover (u := u) (T := T) ∧
    (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
      - velocityH3TransportDerivativeAt u s ≤ Ctransport)

/-- An explicit positive-time energy-class covering provides all four
orderwise energy derivative identities on every initial open subinterval. -/
theorem h3Audit_initialPositiveEnergyClassCover_orderwiseDerivatives
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hCover : H3AuditInitialPositiveEnergyClassCover (u := u) (T := T))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
      H3OrderEnergyDerivativeIdentities u s := by
  intro s hs
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_trans hs.2 ht.2⟩
  obtain ⟨a, hClass, ha⟩ := hCover s hsT
  exact h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
    u T hH3 a hClass s ha

/-- The initial formal H³ energy derivative is bounded from above by a
single constant determined by signed transport and its value at zero.
The value at zero is included only because the previous FTC interface uses
pointwise `Icc` rather than an almost-everywhere upper estimate. -/
theorem h3Audit_initialFormalEnergyRate_le_of_signedTransport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hCover : H3AuditInitialPositiveEnergyClassCover (u := u) (T := T))
    (Ctransport : ℝ)
    (hTransport : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) T →
      - velocityH3TransportDerivativeAt u s ≤ Ctransport)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∀ s ∈ Set.Icc (0 : ℝ) t,
      velocityH3FormalDerivativeAt u s ≤
        max Ctransport (max 0 (velocityH3FormalDerivativeAt u 0)) := by
  intro s hs
  rcases lt_or_eq_of_le hs.1 with hsPositive | hsZero
  · have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hsPositive, lt_of_le_of_lt hs.2 ht.2⟩
    obtain ⟨a, hClass, ha⟩ := hCover s hsT
    exact (h3Audit_formalH3Derivative_le_of_signedTransportUpper
      hH3 hClass ha (hTransport s hsT)).trans
      (le_max_left Ctransport (max 0 (velocityH3FormalDerivativeAt u 0)))
  · subst s
    exact (le_max_right 0 (velocityH3FormalDerivativeAt u 0)).trans
      (le_max_right Ctransport
        (max 0 (velocityH3FormalDerivativeAt u 0)))

/-- Exact NS balance replaces the full temporal H³ energy growth bound
in the initial differentiated-FTC interface. All velocity temporal
conditions, initial continuity and initial integrability remain explicit. -/
theorem h3Audit_initialSignedTransportFTC_implies_differentiatedFTCData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalSignedTransportFTCData hH3) :
    H3AuditInitialPhysicalZeroJetDifferentiatedFTCData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, V, Cv, Ct,
    hCv, hCt, hVelocity, hEnergy, hCover, hTransport⟩ := hData
  let Ce : ℝ := max Ct (max 0 (velocityH3FormalDerivativeAt u 0))
  have hCe : 0 ≤ Ce := by
    dsimp only [Ce]
    exact (le_max_left 0 (velocityH3FormalDerivativeAt u 0)).trans
      (le_max_right Ct (max 0 (velocityH3FormalDerivativeAt u 0)))
  refine ⟨hInt0, hMeas0, hFourier0, V, Cv, Ce,
    hCv, hCe, hVelocity, ?_⟩
  intro t ht
  obtain ⟨hContinuous, hIntegrable⟩ := hEnergy t ht
  exact ⟨hContinuous,
    h3Audit_initialPositiveEnergyClassCover_orderwiseDerivatives
      hH3 hCover t ht,
    hIntegrable,
    h3Audit_initialFormalEnergyRate_le_of_signedTransport
      hH3 hCover Ct hTransport t ht⟩

/-- Main initial trace result: a signed NS transport upper bound suffices;
no uniform *absolute* bound on the full H³ energy derivative is needed. -/
theorem h3Audit_initialSignedTransportFTC_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalSignedTransportFTCData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalDifferentiatedFTC_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialSignedTransportFTC_implies_differentiatedFTCData
      hH3 hData)

/-- Full-time intrinsic two-component Sobolev consequence, still
conditional on the separate strong terminal vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSignedTransportFTC
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalSignedTransportFTCData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialDifferentiatedFTC
    hH3 hClass i hPhysical
    (h3Audit_initialSignedTransportFTC_implies_differentiatedFTCData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
