import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralHighRadialIntegral244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Angular.Concentration
import Mathlib.Tactic

/-!
# Moving high-radial H³ mass and physical dissipation sequence

The prior theorem expresses the terminal obstruction (conditional on failure
of the ordinary strong kinetic L² endpoint trace) as unbounded integrated
weighted H³ spectral mass outside EVERY fixed frequency ball.

This file makes two additional, quantitative deductions.

* The canonical spectral dissipation density is |D(ξ)|² times the weighted
  H³ spectral mass density. Above radius ρ it dominates ρ² times that mass.
  Its whole-space integral is the ACTUAL physical H³ dissipation, so the
  high-radial mass is controlled by genuine physical dissipation.
* A diagonal selection chooses one terminal time τ(n) within 1/(n+1) of T,
  at the MOVING cutoff ρ(n)=n+1, with high-radial weighted spectral square
  mass exceeding n+1. The same snapshots have physical H³ dissipation
  strictly greater than (n+1)^3.

The sequence is conditional on failure of a strong physical L² terminal
trace, NOT on failure of smooth H³ continuation. This produces a necessary
frequency-dissipation cascade and does not exclude that alternative.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3MovingRadialDissipation244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3MovingRadialDissipation244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The two independently constructed encoders of the actual physical H³
velocity are equal at every strict time. -/
theorem h3Path_actualSpectralVelocity_eq_terminalState244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditActualSpectralVelocityTotal hH3 t =
      h3TerminalVelocitySpectralStateAt hH3 t ht := by
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
  rfl

/-- Outside a radial frequency ball, the pointwise H³ dissipation density
is at least radius squared times the actual weighted H³ square amplitude. -/
theorem h3Path_highRadialSpectralSquare_le_dissipationDensity244
    (G : H3SpectralVelocityState)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    {ξ : H3FourierPoint3}
    (hξ : ξ ∈ (h3TerminalRadialFrequencyBelow ρ)ᶜ) :
    ρ ^ 2 * h3TerminalSpectralStateSquareAmplitude G ξ ≤
      h3TerminalSpectralDissipationSingleDensity G ξ := by
  have hOutside : ¬ h3FourierGradientMagnitude ξ < ρ := by
    simpa only [h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq,
      Set.mem_compl_iff] using hξ
  have hGrad : ρ ≤ h3FourierGradientMagnitude ξ :=
    le_of_not_gt hOutside
  have hSquare : ρ ^ 2 ≤ (h3FourierGradientMagnitude ξ) ^ 2 :=
    pow_le_pow_left₀ hρ hGrad 2
  rw [h3TerminalSpectralDissipationSingleDensity_eq_gradientMagnitude_sq_mul_stateSquareAmplitude]
  exact mul_le_mul_of_nonneg_right hSquare
    (h3TerminalSpectralStateSquareAmplitude_nonneg G ξ)

/-- At any actual strict physical time, full H³ dissipation dominates
ρ² times the weighted spectral square mass beyond the cutoff ρ.
The integral-to-physical identification is exact. -/
theorem h3Path_physicalDissipation_ge_highRadialSpectralMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ ^ 2 *
        (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3TerminalSpectralStateSquareAmplitude
            (h3AuditActualSpectralVelocityTotal hH3 t) ξ ∂volume) ≤
      velocityH3DissipationAt u t := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  let G : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow ρ)ᶜ
  let A : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralStateSquareAmplitude G
  let D : H3FourierPoint3 → ℝ :=
    h3TerminalSpectralDissipationSingleDensity G
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact (measurableSet_h3TerminalRadialFrequencyBelow ρ).compl
  have hAInt : Integrable A volume := by
    dsimp only [A]
    exact h3TerminalSpectralStateSquareAmplitude_integrable G
  have hDInt : Integrable D volume := by
    dsimp only [D, G]
    exact h3TerminalSpectralDissipationSingleDensity_integrable
      hH3 hClass ht
  have hScaledInt : Integrable (fun ξ => ρ ^ 2 * A ξ) volume :=
    hAInt.const_mul (ρ ^ 2)
  have hPoint : ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
      ρ ^ 2 * A ξ ≤ D ξ := by
    rw [ae_restrict_iff' hS]
    filter_upwards with ξ
    intro hξ
    dsimp only [A, D, S]
    exact h3Path_highRadialSpectralSquare_le_dissipationDensity244
      G hρ hξ
  have hRestrict :
      (∫ ξ in S, ρ ^ 2 * A ξ ∂volume) ≤
        ∫ ξ in S, D ξ ∂volume :=
    integral_mono_ae
      (hScaledInt.mono_measure Measure.restrict_le_self)
      (hDInt.mono_measure Measure.restrict_le_self)
      hPoint
  have hNonneg : 0 ≤ᵐ[volume] D := by
    exact Eventually.of_forall (fun ξ => by
      dsimp only [D]
      exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ)
  have hTotal :
      (∫ ξ in S, D ξ ∂volume) ≤ ∫ ξ, D ξ ∂volume :=
    integral_mono_measure Measure.restrict_le_self hNonneg hDInt
  have hExact :
      (∫ ξ : H3FourierPoint3, D ξ ∂volume) =
        velocityH3DissipationAt u t := by
    dsimp only [D, G]
    exact integral_h3TerminalSpectralDissipationSingleDensity_eq_dissipation
      hH3 hClass ht
  change ρ ^ 2 * (∫ ξ in S, A ξ ∂volume) ≤
    velocityH3DissipationAt u t
  calc
    ρ ^ 2 * (∫ ξ in S, A ξ ∂volume) =
        ∫ ξ in S, ρ ^ 2 * A ξ ∂volume := by
          rw [integral_const_mul]
    _ ≤ ∫ ξ in S, D ξ ∂volume := hRestrict
    _ ≤ ∫ ξ : H3FourierPoint3, D ξ ∂volume := hTotal
    _ = velocityH3DissipationAt u t := hExact

/-- If the physical L² terminal trace fails, the actual physical full H³
dissipation is unbounded on every strict terminal subtail. The deduction
uses any fixed strictly positive cutoff, with no auxiliary PDE hypothesis. -/
theorem h3Path_physicalNoL2Trace_forces_physicalDissipationEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        M < velocityH3DissipationAt u t := by
  intro c hc M
  obtain ⟨t, ht, hHigh⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialFourierIntegralEscape244
      hH3 hClass hL hNoTrace 1 (by norm_num) c hc M
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hD := h3Path_physicalDissipation_ge_highRadialSpectralMass244
    hH3 hClass t htClass 1 (by norm_num)
  have hD' :
      (∫ ξ in (h3TerminalRadialFrequencyBelow (1 : ℝ))ᶜ,
        h3TerminalSpectralStateSquareAmplitude
          (h3AuditActualSpectralVelocityTotal hH3 t) ξ ∂volume) ≤
        velocityH3DissipationAt u t := by
    simpa only [one_pow, one_mul] using hD
  exact ⟨t, ht, lt_of_lt_of_le hHigh hD'⟩

/-- Moving-cutoff diagonal extraction. The single sequence approaches T,
its excluded radial ball grows without bound, and the H³ spectral mass
outside that moving ball grows at least linearly in its radius. The SAME
snapshots have actual full H³ dissipation above the cube of the radius. -/
theorem h3Path_physicalNoL2Trace_forces_movingRadialDissipationSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ,
        dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        (n : ℝ) + 1 <
          ∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
            h3TerminalSpectralStateSquareAmplitude
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ξ ∂volume) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 < velocityH3DissipationAt u (τ n)) := by
  have hChoice (n : ℕ) :
      ∃ t : ℝ,
        t ∈ Set.Ioo a T ∧
        dist t T < (1 : ℝ) / ((n : ℝ) + 1) ∧
        (n : ℝ) + 1 <
          ∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
            h3TerminalSpectralStateSquareAmplitude
              (h3AuditActualSpectralVelocityTotal hH3 t) ξ ∂volume := by
    let ε : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
    let c : ℝ := max ((a + T) / 2) (T - ε)
    have hε : 0 < ε := by
      dsimp only [ε]
      positivity
    have hMidLower : a < (a + T) / 2 := by
      linarith only [hClass.terminal_start.2]
    have hMidUpper : (a + T) / 2 < T := by
      linarith only [hClass.terminal_start.2]
    have hc : c ∈ Set.Ioo a T := by
      dsimp only [c]
      exact ⟨lt_of_lt_of_le hMidLower (le_max_left _ _),
        (max_lt_iff).2 ⟨hMidUpper, by linarith only [hε]⟩⟩
    obtain ⟨t, ht, hLarge⟩ :=
      h3Path_physicalNoL2Trace_forces_highRadialFourierIntegralEscape244
        hH3 hClass hL hNoTrace
        ((n : ℝ) + 1) (by positivity) c hc ((n : ℝ) + 1)
    have htTail : t ∈ Set.Ioo a T :=
      ⟨lt_trans hc.1 ht.1, ht.2⟩
    have hNear : T - ε < t :=
      lt_of_le_of_lt (le_max_right _ _) ht.1
    have hDist : dist t T < (1 : ℝ) / ((n : ℝ) + 1) := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
      dsimp only [ε] at hNear
      linarith only [hNear]
    exact ⟨t, htTail, hDist, hLarge⟩
  choose τ hτ using hChoice
  have hInv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hNormBound : ∀ n : ℕ,
      ‖τ n - T‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    simpa only [Real.norm_eq_abs, Real.dist_eq] using
      (le_of_lt (hτ n).2.1)
  have hTendsto : Tendsto τ atTop (𝓝 T) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (τ n - T)))
        (Filter.Eventually.of_forall hNormBound)
        hInv)
  have hDiss (n : ℕ) :
      ((n : ℝ) + 1) ^ 3 < velocityH3DissipationAt u (τ n) := by
    have hRadius : 0 < (n : ℝ) + 1 := by positivity
    have hBound := h3Path_physicalDissipation_ge_highRadialSpectralMass244
      hH3 hClass (τ n) (hτ n).1 ((n : ℝ) + 1) hRadius.le
    have hMass := (hτ n).2.2
    calc
      ((n : ℝ) + 1) ^ 3 =
          ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) := by ring
      _ < ((n : ℝ) + 1) ^ 2 *
          (∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
            h3TerminalSpectralStateSquareAmplitude
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ξ ∂volume) :=
        mul_lt_mul_of_pos_left hMass (pow_pos hRadius 2)
      _ ≤ velocityH3DissipationAt u (τ n) := hBound
  exact ⟨τ, (fun n => (hτ n).1), (fun n => (hτ n).2.1),
    hTendsto, (fun n => (hτ n).2.2), hDiss⟩

end
end PrimeTensor.FirstMonomialTriad
