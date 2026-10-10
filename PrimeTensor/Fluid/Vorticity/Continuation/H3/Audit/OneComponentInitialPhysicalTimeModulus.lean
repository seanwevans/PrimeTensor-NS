import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalZeroJetL2

/-!
# Initial physical H³ trace from a vanishing time modulus

The preceding checkpoint reduces initial strong H³ convergence to two
physical initial-value estimates: right convergence in zeroth-order L² of
the actual velocity and a one-sided initial H³ energy ceiling.

Here *both* follow from one common time modulus `ω(t) → 0` as `t → 0+`:

  velocityH3EnergyAt u t ≤ velocityH3EnergyAt u 0 + ω t,
  dist (u_j(t), u_j(0))_{L²} ≤ ω t.

The resulting initial spectral datum is still the actual Fourier encoding
of the velocity at t=0. Neither modulus bound is inferred from the
open-time Navier--Stokes class; they are the explicit next PDE obligations.

A linear-in-time specialization packages the natural objective of proving
uniform physical-L² temporal velocity bounds and a local H³ energy growth
bound from genuine initial-time Navier--Stokes estimates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace

noncomputable section

/-- A vanishing error modulus plus an eventual distance upper bound gives a
right strong limit in an arbitrary pseudometric space. No sign condition on
the modulus is needed separately, since the distance is nonnegative. -/
theorem h3Audit_tendstoRight_of_eventualDistanceLe_modulus
    {X : Type*} [PseudoMetricSpace X]
    (F : ℝ → X) (x₀ : X) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hBound : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      dist (F t) x₀ ≤ ω t) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 x₀) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hSmall : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), ω t < ε :=
    hω.eventually (Iio_mem_nhds hε)
  filter_upwards [hBound, hSmall] with t hDist hModulus
  exact lt_of_le_of_lt hDist hModulus

/-- A vanishing time modulus and an eventual upper estimate produce the
one-sided energy limsup condition required by the initial H³ trace chain. -/
theorem h3Audit_rightUpperEnergy_of_eventualModulus
    (E : ℝ → ℝ) (E₀ : ℝ) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hBound : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      E t ≤ E₀ + ω t) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), E t < E₀ + ε := by
  intro ε hε
  have hSmall : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), ω t < ε :=
    hω.eventually (Iio_mem_nhds hε)
  filter_upwards [hBound, hSmall] with t hE hωSmall
  linarith

/-- For positive terminal time, right-neighborhood times eventually lie
inside the genuine strict physical interval. -/
theorem h3Audit_eventually_initialStrictPhysicalTime
    {T : ℝ} (hT : 0 < T) :
    ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t ∈ Set.Ioo (0 : ℝ) T := by
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  filter_upwards [hPositive, hBeforeT] with t ht0 htT
  exact ⟨ht0, htT⟩

/-- Initial-data bounds for the ACTUAL velocity, with both initial-value
conditions expressed through one right-vanishing physical-time modulus.
The initial Fourier-compatibility proof is retained explicitly. -/
def H3AuditInitialPhysicalZeroJetTimeModulusData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (ω : ℝ → ℝ),
    Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      velocityH3EnergyAt u t ≤ velocityH3EnergyAt u 0 + ω t) ∧
    (∀ (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      dist (h3AuditActualPhysicalZeroJetL2Total hH3 j t)
        (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ≤ ω t)

/-- The shared vanishing modulus closes BOTH remaining initial physical
obligations, with no separately postulated right L² trace or energy limit. -/
theorem h3Audit_initialPhysicalTimeModulus_implies_zeroJetL2Data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetTimeModulusData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, ω, hω, hEnergy, hPhysical⟩ := hData
  have hStrict := h3Audit_eventually_initialStrictPhysicalTime hT
  refine ⟨hInt0, hMeas0, hFourier0, ?_, ?_⟩
  · apply h3Audit_rightUpperEnergy_of_eventualModulus
      (velocityH3EnergyAt u) (velocityH3EnergyAt u 0) ω hω
    filter_upwards [hStrict] with t ht
    exact hEnergy t ht
  · intro j
    apply h3Audit_tendstoRight_of_eventualDistanceLe_modulus
      (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ω hω
    filter_upwards [hStrict] with t ht
    exact hPhysical j t ht

/-- Vanishing physical-time modulus produces the actual full initial H³
spectral trace by the preceding Plancherel and polarization bridges. -/
theorem h3Audit_initialPhysicalTimeModulus_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetTimeModulusData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalZeroJetL2AndEnergyUpper_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialPhysicalTimeModulus_implies_zeroJetL2Data
      hH3 hT hData)

/-- The common modulus may be chosen to be `C * t` with a single
nonnegative physical-time rate constant. These two inequalities are
potential targets for an initial energy and physical velocity FTC estimate. -/
def H3AuditInitialPhysicalZeroJetLinearRateData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (C : ℝ),
    0 ≤ C ∧
    (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      velocityH3EnergyAt u t ≤ velocityH3EnergyAt u 0 + C * t) ∧
    (∀ (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      dist (h3AuditActualPhysicalZeroJetL2Total hH3 j t)
        (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ≤ C * t)

/-- Constant-times-time converges to zero on the right at zero. -/
theorem h3Audit_linearTimeModulus_tendstoRight_zero (C : ℝ) :
    Tendsto (fun t : ℝ => C * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hId : Tendsto (fun t : ℝ => t)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hMul :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => C)
      (𝓝[>] (0 : ℝ)) (𝓝 C)).mul hId
  simpa only [mul_zero] using hMul

/-- The linear-time physical estimates are a special case of the
vanishing-modulus initial-data criterion. -/
theorem h3Audit_initialPhysicalLinearRate_implies_timeModulusData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalZeroJetLinearRateData hH3) :
    H3AuditInitialPhysicalZeroJetTimeModulusData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, C, _hC, hEnergy, hPhysical⟩ := hData
  exact ⟨hInt0, hMeas0, hFourier0, (fun t : ℝ => C * t),
    h3Audit_linearTimeModulus_tendstoRight_zero C,
    hEnergy, hPhysical⟩

/-- Linear-time physical velocity and energy estimates imply the true
initial H³ right trace of the old Navier--Stokes solution. -/
theorem h3Audit_initialPhysicalLinearRate_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetLinearRateData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalTimeModulus_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialPhysicalLinearRate_implies_timeModulusData hH3 hData)

/-- Consequence for both transverse physical homogeneous Sobolev time
norms. The strong physical vorticity endpoint is an independent hypothesis. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalTimeModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalZeroJetTimeModulusData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  have hT : 0 < T :=
    lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalZeroJetL2
      hH3 hClass i hPhysical
      (h3Audit_initialPhysicalTimeModulus_implies_zeroJetL2Data
        hH3 hT hData)

end
end Euclidean
end Bridge
end PrimeTensor
