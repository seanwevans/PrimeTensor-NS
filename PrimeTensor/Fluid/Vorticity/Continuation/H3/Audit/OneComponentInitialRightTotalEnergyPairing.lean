import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightWeakNormTrace

/-!
# Strong initial H³ spectral trace from total physical energy and three pairings

In a three-component Hilbert product the *sum* of component square norms,
not a separate norm limit for each component, is sufficient to upgrade
convergence of three correlations against a proposed initial state to
strong convergence in every component.  The proof is the exact identity

  ∑ⱼ ‖Uⱼ(t) - U₀ⱼ‖²
    = ∑ⱼ ‖Uⱼ(t)‖² - 2 ∑ⱼ Re ⟪Uⱼ(t), U₀ⱼ⟫ + ∑ⱼ ‖U₀ⱼ‖².

For the actual physical velocity, the already proved weighted Fourier
encoder gives 1 + ∑ⱼ ‖Uⱼ(t)‖² = E_H³(t) at every strict physical time.
Thus one initial physical H³ energy limit and three initial test pairings
suffice to recover all one-sided physical H³ Fourier traces.

The physical initial-energy continuity and the three correlations are
EXPLICIT hypotheses: `LoggedPreterminalH3PathAdmissible` only provides
continuity at positive times. No existence of a local strong solution,
initial PDE mild formula, terminal continuation, or Liu--Zhang implication
is inferred from the open-time path alone.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace

noncomputable section

/-- Finite-component polarization: convergence of the total squared H³
norm and only *three selected initial correlations* forces strong H³
convergence, without component-by-component norm hypotheses. -/
theorem h3Audit_rightSpectralVelocity_tendsto_of_totalSquareEnergy_and_initialPairings
    (F : ℝ → H3SpectralVelocityState)
    (U₀ : H3SpectralVelocityState)
    (hEnergy : Tendsto (fun t : ℝ => h3SpectralVelocitySquareEnergy (F t))
      (𝓝[>] (0 : ℝ)) (𝓝 (h3SpectralVelocitySquareEnergy U₀)))
    (hPair : ∀ j : Fin 3,
      Tendsto (fun t : ℝ => (inner ℂ (F t j) (U₀ j)).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ (U₀ j) (U₀ j)).re)) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  have hPairSum :
      Tendsto
        (fun t : ℝ => ∑ j : Fin 3, (inner ℂ (F t j) (U₀ j)).re)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ j : Fin 3, (inner ℂ (U₀ j) (U₀ j)).re)) := by
    apply tendsto_finsetSum
    intro j _
    exact hPair j
  have hIdentity (t : ℝ) :
      (∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2) =
        h3SpectralVelocitySquareEnergy (F t) -
          2 * (∑ j : Fin 3, (inner ℂ (F t j) (U₀ j)).re) +
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
          Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hZero :
      h3SpectralVelocitySquareEnergy U₀ -
          2 * (∑ j : Fin 3, (inner ℂ (U₀ j) (U₀ j)).re) +
          h3SpectralVelocitySquareEnergy U₀ = 0 := by
    calc
      _ = ∑ j : Fin 3,
            (‖U₀ j‖ ^ 2 - 2 * (inner ℂ (U₀ j) (U₀ j)).re +
              ‖U₀ j‖ ^ 2) := by
                simp only [h3SpectralVelocitySquareEnergy,
                  Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = ∑ j : Fin 3, ‖U₀ j - U₀ j‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        exact (norm_sub_sq (𝕜 := ℂ) (U₀ j) (U₀ j)).symm
      _ = 0 := by simp
  have hDlimit :
      Tendsto
        (fun t : ℝ => ∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hAux :
        Tendsto
          (fun t : ℝ => h3SpectralVelocitySquareEnergy (F t) -
            2 * (∑ j : Fin 3, (inner ℂ (F t j) (U₀ j)).re) +
            h3SpectralVelocitySquareEnergy U₀)
          (𝓝[>] (0 : ℝ))
          (𝓝 (h3SpectralVelocitySquareEnergy U₀ -
            2 * (∑ j : Fin 3, (inner ℂ (U₀ j) (U₀ j)).re) +
            h3SpectralVelocitySquareEnergy U₀)) := by
      exact (hEnergy.sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ))).mul hPairSum)).add
        tendsto_const_nhds
    have hEq :
        (fun t : ℝ => ∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2) =
          (fun t : ℝ =>
            h3SpectralVelocitySquareEnergy (F t) -
              2 * (∑ j : Fin 3, (inner ℂ (F t j) (U₀ j)).re) +
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
    · exact hDlimit
  have hSqrt :
      Tendsto (fun t : ℝ => Real.sqrt (‖F t j - U₀ j‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hSq
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg,
    Real.sqrt_zero] using hSqrt

/-- The genuine three-component Fourier encoder of the actual velocity,
extended by zero away from the strict preterminal physical interval. -/
noncomputable def h3AuditActualSpectralVelocityTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) (t : ℝ) :
    H3SpectralVelocityState :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3AuditActualSpectralVelocityAt hH3 t ht
  else 0

/-- At strict times the total extension is the actual Fourier encoding. -/
theorem h3AuditActualSpectralVelocityTotal_eq_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditActualSpectralVelocityTotal hH3 t =
      h3AuditActualSpectralVelocityAt hH3 t ht := by
  simp only [h3AuditActualSpectralVelocityTotal, dite_eq_left ht]

/-- Exact physical H³ energy identity, not merely an energy upper bound. -/
theorem h3AuditActualSpectralVelocityTotal_energy_exact
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    1 + h3SpectralVelocitySquareEnergy
        (h3AuditActualSpectralVelocityTotal hH3 t) =
      velocityH3EnergyAt u t := by
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  change 1 + h3SpectralVelocitySquareEnergy
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) =
        velocityH3EnergyAt u t
  exact one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
    hFourier

/-- The physical H³ energy is continuous from the right at the initial time
and has the exact mass expected of a proposed initial Fourier velocity U₀.
There is no claim that the open-time H³ path supplies this condition. -/
def H3AuditInitialRightTotalEnergyAndThreePairings
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ U₀ : H3SpectralVelocityState,
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + h3SpectralVelocitySquareEnergy U₀)) ∧
    ∀ j : Fin 3,
      Tendsto
        (fun t : ℝ =>
          (inner ℂ (h3AuditActualSpectralVelocityTotal hH3 t j)
            (U₀ j)).re)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℂ (U₀ j) (U₀ j)).re)

/-- Exactly one physical scalar energy limit, plus the three initial H³
correlations, yields strong right continuity of the ACTUAL full Fourier
velocity. No three independent component norm limits are required. -/
theorem h3Audit_initialRightTotalEnergyPairings_implies_strongVelocityTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialRightTotalEnergyAndThreePairings hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨U₀, hEnergy, hPair⟩ := hData
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
    h3Audit_rightSpectralVelocity_tendsto_of_totalSquareEnergy_and_initialPairings
      (h3AuditActualSpectralVelocityTotal hH3) U₀ hSpectralEnergy hPair⟩

/-- Every actual physical complementary component acquires the same
one-sided H³ spectral trace, with no separate norm-limit assumption. -/
theorem h3Audit_initialRightTotalEnergyPairings_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialRightTotalEnergyAndThreePairings hH3)
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  obtain ⟨U₀, hConverges⟩ :=
    h3Audit_initialRightTotalEnergyPairings_implies_strongVelocityTrace
      hH3 hT hData
  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)
  have hCoordinate :
      Tendsto (fun t : ℝ =>
        (h3AuditActualSpectralVelocityTotal hH3 t) j)
        (𝓝[>] (0 : ℝ)) (𝓝 (U₀ j)) := by
    exact (continuous_apply j).continuousAt.tendsto.comp hConverges
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

/-- One physical vorticity strong endpoint and a single right total-H³-energy
limit plus three initial correlations suffice for *both* transverse physical
velocity coordinates in full-time L²_t Ḣ^(3/2)_x. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialTotalEnergyPairings
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hInitial : H3AuditInitialRightTotalEnergyAndThreePairings hH3) :
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
    (h3Audit_initialRightTotalEnergyPairings_rightComplementTrace
      hH3 hT hInitial (h3TerminalActualVorticityPositiveComplementPair i))
    (h3Audit_initialRightTotalEnergyPairings_rightComplementTrace
      hH3 hT hInitial (h3TerminalActualVorticityNegativeComplementPair i))

end
end Euclidean
end Bridge
end PrimeTensor
