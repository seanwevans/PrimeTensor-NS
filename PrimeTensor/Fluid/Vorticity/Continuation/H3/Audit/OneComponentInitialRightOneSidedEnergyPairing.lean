import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightAggregatePairing

/-!
# Initial physical H³ trace from one-sided energy and aggregate correlation

The preceding audit used two exact scalar limits: full H³ energy convergence
and convergence of the sum of H³ correlations against a proposed initial state.

Here the exact limits are weakened to *one-sided* estimates:
  limsup_{t -> 0+} (sum_j ‖U_j(t)‖²) <= sum_j ‖U₀_j‖²,
  liminf_{t -> 0+} (sum_j Re ⟪U_j(t),U₀_j⟫) >= sum_j ‖U₀_j‖².

Only eventual epsilon upper and lower bounds are used; no additional limit is
assumed. Polarization implies that the total squared H³ distance tends to
zero. These are natural directions for a physical energy inequality and an
initial weak-pairing argument, but neither PDE-side estimate follows from
mere open-time admissibility. The downstream H^(3/2) time-L² theorem retains
its separately stated strong terminal vorticity endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace

noncomputable section

/-- One-sided energy upper control and one-sided aggregate correlation lower
control imply full three-component H³ convergence. These hypotheses are
strictly weaker as *individual* assertions than either exact scalar limit. -/
theorem h3Audit_rightSpectralVelocity_tendsto_of_upperEnergy_lowerCorrelation
    (F : ℝ → H3SpectralVelocityState)
    (U₀ : H3SpectralVelocityState)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        h3SpectralVelocitySquareEnergy (F t) <
          h3SpectralVelocitySquareEnergy U₀ + ε)
    (hLower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        h3SpectralVelocitySquareEnergy U₀ <
          h3AuditSpectralVelocityAggregateCorrelation (F t) U₀ + ε) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  have hIdentity (t : ℝ) :
      (∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2) =
        h3SpectralVelocitySquareEnergy (F t) -
          2 * h3AuditSpectralVelocityAggregateCorrelation (F t) U₀ +
          h3SpectralVelocitySquareEnergy U₀ := by
    calc
      (∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2) =
          ∑ j : Fin 3,
            (‖F t j‖ ^ 2 -
              2 * (inner ℂ (F t j) (U₀ j)).re +
              ‖U₀ j‖ ^ 2) := by
                apply Finset.sum_congr rfl
                intro j _
                exact norm_sub_sq (𝕜 := ℂ) (F t j) (U₀ j)
      _ = _ := by
        simp only [h3SpectralVelocitySquareEnergy,
          h3AuditSpectralVelocityAggregateCorrelation,
          Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hNonneg (t : ℝ) :
      0 ≤ ∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2 := by
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hDistanceLimit :
      Tendsto (fun t : ℝ => ∑ j : Fin 3, ‖F t j - U₀ j‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hεHalf : 0 < ε / 2 := by positivity
    have hεQuarter : 0 < ε / 4 := by positivity
    have hU := hUpper (ε / 2) hεHalf
    have hL := hLower (ε / 4) hεQuarter
    filter_upwards [hU, hL] with t hEnergyBound hCorrelationBound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hNonneg t)]
    rw [hIdentity t]
    linarith
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

/-- A physical initial-data criterion involving no *assumed* exact limits.
The total physical H³ energy is controlled from above, and the aggregate
correlation of the ACTUAL weighted Fourier encoding is controlled from below. -/
def H3AuditInitialRightEnergyUpperCorrelationLower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ U₀ : H3SpectralVelocityState,
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        velocityH3EnergyAt u t <
          1 + h3SpectralVelocitySquareEnergy U₀ + ε) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        h3SpectralVelocitySquareEnergy U₀ <
          h3AuditSpectralVelocityAggregateCorrelation
            (h3AuditActualSpectralVelocityTotal hH3 t) U₀ + ε)

/-- At positive times the exact H³ Fourier energy identity transfers the
one-sided *physical* energy estimate to the three-component spectral state. -/
theorem h3Audit_initialRightEnergyUpperCorrelationLower_implies_strongVelocityTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialRightEnergyUpperCorrelationLower hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨U₀, hUpperPhysical, hLower⟩ := hData
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [hPositive, hBeforeT] with t hp hlt
    exact ⟨hp, hlt⟩
  have hUpperSpectral :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
          h3SpectralVelocitySquareEnergy
              (h3AuditActualSpectralVelocityTotal hH3 t) <
            h3SpectralVelocitySquareEnergy U₀ + ε := by
    intro ε hε
    have hPhysical := hUpperPhysical ε hε
    filter_upwards [hPhysical, hStrict] with t hBound ht
    have hExact := h3AuditActualSpectralVelocityTotal_energy_exact hH3 t ht
    linarith
  exact ⟨U₀,
    h3Audit_rightSpectralVelocity_tendsto_of_upperEnergy_lowerCorrelation
      (h3AuditActualSpectralVelocityTotal hH3) U₀
      hUpperSpectral hLower⟩

/-- A full physical H³ right trace gives all complementary component traces. -/
theorem h3Audit_initialRightEnergyUpperCorrelationLower_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialRightEnergyUpperCorrelationLower hH3)
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  obtain ⟨U₀, hTrace⟩ :=
    h3Audit_initialRightEnergyUpperCorrelationLower_implies_strongVelocityTrace
      hH3 hT hData
  exact h3Audit_initialStrongFullSpectralTrace_rightComplementTrace
    hH3 hT U₀ hTrace p

/-- Initial physical H³ energy continuity plus its correct initial value
provides the upper estimate for any positive epsilon. -/
theorem h3Audit_initialEnergyContinuous_implies_rightUpperEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (U₀ : H3SpectralVelocityState)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u)
    (hValue : velocityH3EnergyAt u 0 =
      1 + h3SpectralVelocitySquareEnergy U₀) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        velocityH3EnergyAt u t <
          1 + h3SpectralVelocitySquareEnergy U₀ + ε := by
  intro ε hε
  have hTendsto : Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) :=
    hInitial.tendsto.mono_left nhdsWithin_le_nhds
  have hNear := hTendsto.eventually
    (Iio_mem_nhds (lt_add_of_pos_right (velocityH3EnergyAt u 0) hε))
  simpa only [hValue] using hNear

/-- Packaging the one-sided physical energy bound from actual energy
continuity leaves only the aggregate lower correlation as an initial-data
PDE-side obligation. -/
theorem h3Audit_initialEnergyContinuous_and_rightLowerCorrelation_data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u)
    (hValue : velocityH3EnergyAt u 0 =
      1 + h3SpectralVelocitySquareEnergy U₀)
    (hLower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        h3SpectralVelocitySquareEnergy U₀ <
          h3AuditSpectralVelocityAggregateCorrelation
            (h3AuditActualSpectralVelocityTotal hH3 t) U₀ + ε) :
    H3AuditInitialRightEnergyUpperCorrelationLower hH3 := by
  exact ⟨U₀,
    h3Audit_initialEnergyContinuous_implies_rightUpperEnergy U₀
      hInitial hValue, hLower⟩

/-- The genuine full-time two-component physical L²_t Ḣ^(3/2)_x criterion
from one-sided initial data, conditional on the separately given strong
physical terminal vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOneSidedEnergyPairing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hInitial : H3AuditInitialRightEnergyUpperCorrelationLower hH3) :
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
    (h3Audit_initialRightEnergyUpperCorrelationLower_rightComplementTrace
      hH3 hT hInitial (h3TerminalActualVorticityPositiveComplementPair i))
    (h3Audit_initialRightEnergyUpperCorrelationLower_rightComplementTrace
      hH3 hT hInitial (h3TerminalActualVorticityNegativeComplementPair i))

end
end Euclidean
end Bridge
end PrimeTensor
