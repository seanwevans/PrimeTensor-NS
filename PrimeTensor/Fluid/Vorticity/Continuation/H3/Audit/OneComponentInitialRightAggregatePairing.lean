import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightTotalEnergyPairing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentFullTimeSobolevInitialContinuity

/-!
# Initial physical H³ trace from one energy and one aggregate correlation

The finite-component polarization argument only needs the SUM of the three
correlations with the proposed initial spectral velocity, not an independent
convergence hypothesis for each component.

This file proves the corresponding two-scalar characterization in the
sufficient direction:

* the actual normalized total physical H³ energy approaches the initial
  spectral energy, and
* the single sum of real H³ inner products with the initial velocity approaches
  the initial spectral square energy.

By the exact polarization identity their difference controls the sum of
squared H³ component distances. It follows that the actual full Fourier
velocity, and hence every selected actual physical component, has a strong
right H³ trace. The existing physical endpoint criterion then gives the
full-time intrinsic L²_t Ḣ^(3/2)_x statements.

The two scalar initial limits remain explicit PDE-side hypotheses. In
particular, the open-time H³ path does not assert initial-time continuity,
nor does this theorem prove the Liu--Zhang continuation implication.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace

noncomputable section

/-- The real aggregate Fourier H³ correlation of two three-component states. -/
noncomputable def h3AuditSpectralVelocityAggregateCorrelation
    (U V : H3SpectralVelocityState) : ℝ :=
  ∑ j : Fin 3, (inner ℂ (U j) (V j)).re

/-- The correlation of a state with itself equals its spectral square energy. -/
theorem h3AuditSpectralVelocityAggregateCorrelation_self
    (U : H3SpectralVelocityState) :
    h3AuditSpectralVelocityAggregateCorrelation U U =
      h3SpectralVelocitySquareEnergy U := by
  unfold h3AuditSpectralVelocityAggregateCorrelation
    h3SpectralVelocitySquareEnergy
  apply Finset.sum_congr rfl
  intro j _
  simp only [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Two scalar limits are enough for strong right H³ convergence of all
three Fourier coordinates. No separate three-component pairing hypothesis. -/
theorem h3Audit_rightSpectralVelocity_tendsto_of_totalEnergy_and_aggregateCorrelation
    (F : ℝ → H3SpectralVelocityState)
    (U₀ : H3SpectralVelocityState)
    (hEnergy : Tendsto
      (fun t : ℝ => h3SpectralVelocitySquareEnergy (F t))
      (𝓝[>] (0 : ℝ)) (𝓝 (h3SpectralVelocitySquareEnergy U₀)))
    (hCorrelation : Tendsto
      (fun t : ℝ => h3AuditSpectralVelocityAggregateCorrelation (F t) U₀)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3SpectralVelocitySquareEnergy U₀))) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  have hIdentity (t : ℝ) :
      (∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2) =
        h3SpectralVelocitySquareEnergy (F t) -
          2 * h3AuditSpectralVelocityAggregateCorrelation (F t) U₀ +
          h3SpectralVelocitySquareEnergy U₀ := by
    calc
      (∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2) =
          ∑ j : Fin 3,
            (‖F t j‖ ^ 2 - 2 * (inner ℂ (F t j) (U₀ j)).re +
              ‖U₀ j‖ ^ 2) := by
                apply Finset.sum_congr rfl
                intro j _
                exact norm_sub_sq (𝕜 := ℂ) (F t j) (U₀ j)
      _ = _ := by
        simp only [h3SpectralVelocitySquareEnergy,
          h3AuditSpectralVelocityAggregateCorrelation,
          Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hZero :
      h3SpectralVelocitySquareEnergy U₀ -
          2 * h3SpectralVelocitySquareEnergy U₀ +
          h3SpectralVelocitySquareEnergy U₀ = 0 := by ring
  have hDistanceLimit :
      Tendsto
        (fun t : ℝ => ∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hAux :
        Tendsto
          (fun t : ℝ => h3SpectralVelocitySquareEnergy (F t) -
            2 * h3AuditSpectralVelocityAggregateCorrelation (F t) U₀ +
            h3SpectralVelocitySquareEnergy U₀)
          (𝓝[>] (0 : ℝ))
          (𝓝 (h3SpectralVelocitySquareEnergy U₀ -
            2 * h3SpectralVelocitySquareEnergy U₀ +
            h3SpectralVelocitySquareEnergy U₀)) := by
      exact (hEnergy.sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ))).mul hCorrelation)).add
        tendsto_const_nhds
    have hEq :
        (fun t : ℝ => ∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2) =
          (fun t : ℝ => h3SpectralVelocitySquareEnergy (F t) -
            2 * h3AuditSpectralVelocityAggregateCorrelation (F t) U₀ +
            h3SpectralVelocitySquareEnergy U₀) := by
      funext t
      exact hIdentity t
    rw [hEq]
    simpa only [hZero] using hAux
  rw [tendsto_pi_nhds]
  intro j
  have hSq :
      Tendsto (fun t : ℝ => ‖F t j - U₀ j‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero
    · intro t
      exact sq_nonneg _
    · intro t
      exact Finset.single_le_sum
        (fun k _ => sq_nonneg ‖F t k - U₀ k‖)
        (Finset.mem_univ j)
    · exact hDistanceLimit
  have hSqrt :
      Tendsto (fun t : ℝ => Real.sqrt (‖F t j - U₀ j‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hSq
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg,
    Real.sqrt_zero] using hSqrt

/-- One scalar physical H³ energy limit and one scalar *actual-velocity*
aggregate spectral correlation replace the three separate initial tests. -/
def H3AuditInitialRightTotalEnergyAndAggregatePairing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ U₀ : H3SpectralVelocityState,
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + h3SpectralVelocitySquareEnergy U₀)) ∧
    Tendsto
      (fun t : ℝ =>
        h3AuditSpectralVelocityAggregateCorrelation
          (h3AuditActualSpectralVelocityTotal hH3 t) U₀)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3SpectralVelocitySquareEnergy U₀))

/-- The genuine old physical velocity has a three-component strong Fourier
H³ right trace from just the two aggregate scalar limits. -/
theorem h3Audit_initialRightAggregatePairing_implies_strongVelocityTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialRightTotalEnergyAndAggregatePairing hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨U₀, hEnergy, hCorrelation⟩ := hData
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [hPositive, hBeforeT] with t hp hlt
    exact ⟨hp, hlt⟩
  have hEnergyMinus :
      Tendsto (fun t : ℝ => velocityH3EnergyAt u t - 1)
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3SpectralVelocitySquareEnergy U₀)) := by
    have h := hEnergy.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)))
    have hOne : 1 + h3SpectralVelocitySquareEnergy U₀ - 1 =
        h3SpectralVelocitySquareEnergy U₀ := by ring
    simpa only [hOne] using h
  have hEventuallyEq :
      (fun t : ℝ => velocityH3EnergyAt u t - 1) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 t)) := by
    filter_upwards [hStrict] with t ht
    have hExact := h3AuditActualSpectralVelocityTotal_energy_exact hH3 t ht
    linarith
  have hSpectralEnergy :
      Tendsto
        (fun t : ℝ => h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 t))
        (𝓝[>] (0 : ℝ)) (𝓝 (h3SpectralVelocitySquareEnergy U₀)) :=
    hEnergyMinus.congr' hEventuallyEq
  exact ⟨U₀,
    h3Audit_rightSpectralVelocity_tendsto_of_totalEnergy_and_aggregateCorrelation
      (h3AuditActualSpectralVelocityTotal hH3) U₀
      hSpectralEnergy hCorrelation⟩

/-- Any strong right trace of the actual full H³ spectral velocity gives a
right trace of every selected actual physical velocity component. -/
theorem h3Audit_initialStrongFullSpectralTrace_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀))
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)
  have hCoordinate :
      Tendsto (fun t : ℝ =>
        (h3AuditActualSpectralVelocityTotal hH3 t) j)
        (𝓝[>] (0 : ℝ)) (𝓝 (U₀ j)) := by
    exact (continuous_apply j).continuousAt.tendsto.comp hTrace
  have hEventuallyEq :
      (fun t : ℝ => (h3AuditActualSpectralVelocityTotal hH3 t) j)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (h3AuditActualComplementSpectralStateTotal hH3 p) := by
    have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
      self_mem_nhdsWithin
    have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T :=
      nhdsWithin_le_nhds (Iio_mem_nhds hT)
    filter_upwards [hPositive, hBeforeT] with t hp hlt
    let ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨hp, hlt⟩
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
    have hComponent := h3AuditActualSpectralVelocityAt_complement hH3 p t ht
    simpa only [h3AuditActualComplementSpectralStateTotal, dite_eq_left ht,
      j] using hComponent
  exact ⟨U₀ j, hCoordinate.congr' hEventuallyEq⟩

/-- Derive the actual one-sided H³ Fourier trace of any chosen complement. -/
theorem h3Audit_initialRightAggregatePairing_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialRightTotalEnergyAndAggregatePairing hH3)
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  obtain ⟨U₀, hTrace⟩ :=
    h3Audit_initialRightAggregatePairing_implies_strongVelocityTrace
      hH3 hT hData
  exact h3Audit_initialStrongFullSpectralTrace_rightComplementTrace
    hH3 hT U₀ hTrace p

/-- The initial physical energy's already-defined continuity at zero,
together with its exact initial spectral value, supplies the first scalar
limit without an additional separately stated `Tendsto` assumption. -/
theorem h3Audit_initialEnergyContinuous_and_aggregatePairing_strongVelocityTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (U₀ : H3SpectralVelocityState)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u)
    (hValue : velocityH3EnergyAt u 0 =
      1 + h3SpectralVelocitySquareEnergy U₀)
    (hCorrelation : Tendsto
      (fun t : ℝ =>
        h3AuditSpectralVelocityAggregateCorrelation
          (h3AuditActualSpectralVelocityTotal hH3 t) U₀)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3SpectralVelocitySquareEnergy U₀))) :
    Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  have hEnergy : Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + h3SpectralVelocitySquareEnergy U₀)) := by
    rw [← hValue]
    exact hInitial.tendsto.mono_left nhdsWithin_le_nhds
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  have hEventuallyEq :
      (fun t : ℝ => velocityH3EnergyAt u t - 1) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 t)) := by
    filter_upwards [hPositive, hBeforeT] with t hp hlt
    have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨hp, hlt⟩
    have hExact := h3AuditActualSpectralVelocityTotal_energy_exact hH3 t ht
    linarith
  have hEnergyMinus :
      Tendsto (fun t : ℝ => velocityH3EnergyAt u t - 1)
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3SpectralVelocitySquareEnergy U₀)) := by
    have h := hEnergy.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)))
    have hOne : 1 + h3SpectralVelocitySquareEnergy U₀ - 1 =
        h3SpectralVelocitySquareEnergy U₀ := by ring
    simpa only [hOne] using h
  exact
    h3Audit_rightSpectralVelocity_tendsto_of_totalEnergy_and_aggregateCorrelation
      (h3AuditActualSpectralVelocityTotal hH3) U₀
      (hEnergyMinus.congr' hEventuallyEq) hCorrelation

/-- The final analytic time-L² criterion for both transverse actual physical
velocity components, conditional on the established terminal endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialAggregatePairing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hInitial : H3AuditInitialRightTotalEnergyAndAggregatePairing hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  have hT : 0 < T := lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightTraces
    hH3 hClass i hPhysical
    (h3Audit_initialRightAggregatePairing_rightComplementTrace
      hH3 hT hInitial (h3TerminalActualVorticityPositiveComplementPair i))
    (h3Audit_initialRightAggregatePairing_rightComplementTrace
      hH3 hT hInitial (h3TerminalActualVorticityNegativeComplementPair i))

end
end Euclidean
end Bridge
end PrimeTensor
