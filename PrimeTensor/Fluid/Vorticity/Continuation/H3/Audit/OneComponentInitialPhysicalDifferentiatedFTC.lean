import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalFTCControl
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Initial physical H³ FTC from genuine temporal derivatives

The previous file `OneComponentInitialPhysicalFTCControl` required *two exact
integral equations* for the actual zeroth physical velocity and H³ energy.
Here neither integral equation is postulated. The Banach-valued and scalar
fundamental theorems of calculus derive them from:

* an initial-anchored physical zeroth-jet path continuous on `[0,t]`;
* a genuine strong Hilbert-space derivative on `(0,t)` whose source is
  interval-integrable and almost everywhere bounded;
* the project's **exact** orderwise H³ energy derivative identities on
  `(0,t)`, continuity of the real energy on `[0,t]`, interval integrability
  and an upper bound for the **canonical** formal H³ energy derivative.

The initial-anchored path equals the actual logged zeroth physical `L²` jet at
all strict physical times, and the actual initial velocity `L²` jet at zero.
The open-time NS admissibility class does not imply the required `t=0`
continuity, Bochner integrability, or bounded initial temporal sources.
These are retained as explicit PDE-side obligations, and the terminal strong
vorticity endpoint remains independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3AuditInitialDifferentiatedFTC
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- An anchored physical `L²` path: the actual logged velocity for
`0 < t < T`, with its genuine `t=0` physical velocity at the origin. -/
noncomputable def h3AuditInitialPhysicalZeroJetAnchored
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (j : Fin 3) (t : ℝ) : H3ScalarL2 :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3AuditActualPhysicalZeroJetL2Total hH3 j t
  else
    velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)

/-- On the open physical time interval the anchored path is the original
physical zeroth velocity jet, with no selected restart surrogate. -/
theorem h3AuditInitialPhysicalZeroJetAnchored_eq_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j t =
      h3AuditActualPhysicalZeroJetL2Total hH3 j t := by
  simp only [h3AuditInitialPhysicalZeroJetAnchored, dite_eq_left ht]

/-- At zero, the anchored path equals precisely the initial `L²` jet. -/
theorem h3AuditInitialPhysicalZeroJetAnchored_eq_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (j : Fin 3) :
    h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j 0 =
      velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) := by
  simp [h3AuditInitialPhysicalZeroJetAnchored]

/-- The actual physical zeroth-jet FTC follows from the *strong* Banach
space derivative and the initial-anchored continuity, rather than being an
assumed identity. -/
theorem h3Audit_initialPhysicalZeroJet_FTC_of_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (V : Fin 3 → ℝ → H3ScalarL2)
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hContinuous : ContinuousOn
      (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
      (Set.Icc (0 : ℝ) t))
    (hDerivative : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
      HasDerivAt
        (h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j)
        (V j s) s)
    (hIntegrable : IntervalIntegrable (V j) volume 0 t) :
    h3AuditActualPhysicalZeroJetL2Total hH3 j t -
      velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) =
        ∫ s in (0 : ℝ)..t, V j s := by
  have hFTC :
      (∫ s in (0 : ℝ)..t, V j s) =
        h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j t -
        h3AuditInitialPhysicalZeroJetAnchored hH3 hInt0 hMeas0 j 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      ht.1.le hContinuous hDerivative hIntegrable
  rw [h3AuditInitialPhysicalZeroJetAnchored_eq_at hH3 hInt0 hMeas0 j t ht,
    h3AuditInitialPhysicalZeroJetAnchored_eq_zero hH3 hInt0 hMeas0 j] at hFTC
  exact hFTC.symm

/-- The scalar FTC for the actual H³ energy with its *canonical* derivative
`velocityH3FormalDerivativeAt`, using the orderwise differentiation theorem. -/
theorem h3Audit_initialPhysicalH3Energy_FTC_of_orderwiseDerivatives
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hContinuous : ContinuousOn (velocityH3EnergyAt u)
      (Set.Icc (0 : ℝ) t))
    (hIdentities : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
      H3OrderEnergyDerivativeIdentities u s)
    (hIntegrable : IntervalIntegrable (velocityH3FormalDerivativeAt u)
      volume 0 t) :
    velocityH3EnergyAt u t - velocityH3EnergyAt u 0 =
      ∫ s in (0 : ℝ)..t, velocityH3FormalDerivativeAt u s := by
  have hDerivative : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
      HasDerivAt (velocityH3EnergyAt u)
        (velocityH3FormalDerivativeAt u s) s := by
    intro s hs
    exact hasDerivAt_velocityH3EnergyAt (hIdentities s hs)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ht.1.le hContinuous hDerivative hIntegrable).symm

/-- Physical source terms are no longer abstract FTC witnesses: the velocity
source is stipulated as the actual strong time derivative of the anchored
physical L² path, while the energy source is the project's formal H³ energy
derivative, certified by its four orderwise `HasDerivAt` identities. -/
def H3AuditInitialPhysicalZeroJetDifferentiatedFTCData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (V : Fin 3 → ℝ → H3ScalarL2)
    (Cvelocity Cenergy : ℝ),
    0 ≤ Cvelocity ∧ 0 ≤ Cenergy ∧
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
      (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t →
        H3OrderEnergyDerivativeIdentities u s) ∧
      IntervalIntegrable (velocityH3FormalDerivativeAt u) volume 0 t ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t,
        velocityH3FormalDerivativeAt u s ≤ Cenergy))

/-- Genuine strong derivative and orderwise-energy hypotheses imply the
previous physical FTC contract, now using the exact canonical H³ source. -/
theorem h3Audit_initialPhysicalDifferentiatedFTC_implies_FTCControlData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalZeroJetDifferentiatedFTCData hH3) :
    H3AuditInitialPhysicalZeroJetFTCControlData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, V, Cv, Ce,
    hCv, hCe, hVelocity, hEnergy⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, V,
    velocityH3FormalDerivativeAt u, Cv, Ce, hCv, hCe, ?_, ?_⟩
  · intro j t ht
    obtain ⟨hContinuous, hDerivative, hIntegrable, hRate⟩ :=
      hVelocity j t ht
    exact ⟨hIntegrable,
      h3Audit_initialPhysicalZeroJet_FTC_of_hasDerivAt
        hH3 hInt0 hMeas0 V j t ht
        hContinuous hDerivative hIntegrable,
      hRate⟩
  · intro t ht
    obtain ⟨hContinuous, hIdentities, hIntegrable, hRate⟩ :=
      hEnergy t ht
    exact ⟨hIntegrable,
      h3Audit_initialPhysicalH3Energy_FTC_of_orderwiseDerivatives
        t ht hContinuous hIdentities hIntegrable,
      hRate⟩

/-- Canonical initial H³ right trace from genuine strong physical `L²`
derivatives and certified H³ energy derivatives on initial intervals. -/
theorem h3Audit_initialPhysicalDifferentiatedFTC_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetDifferentiatedFTCData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalFTCControl_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialPhysicalDifferentiatedFTC_implies_FTCControlData
      hH3 hData)

/-- Conditional full-time two-component intrinsic `L²_t Ḣ^(3/2)_x` bound,
retaining the separately assumed strong physical terminal vorticity path. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialDifferentiatedFTC
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalZeroJetDifferentiatedFTCData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalFTC
    hH3 hClass i hPhysical
    (h3Audit_initialPhysicalDifferentiatedFTC_implies_FTCControlData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
