import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalViscousEscapeDiagonal
import Mathlib.Tactic

/-!
# Arbitrary terminal viscous height profiles from missing H³ trace

The high-radial H³ escape threshold is fixed independently of the cutoff.
Therefore the cutoff can be increased in advance until the sharp frequency-
square coercivity exceeds ANY prescribed finite nonnegative (or signed) height.
Dissipation is antitone in cutoff radius, so that height transfers to the
original natural n+1 cutoff on a cofinal terminal sequence.

This is a pointwise-height statement; neither persistence widths nor time
integrated dissipation divergence follow from it alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalArbitraryViscous244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For a fixed nonzero H³ tail, the radial coercivity factor can dominate
any requested finite real height, while remaining beyond a chosen cutoff. -/
theorem thirdFull_exists_largeRadialDissipationFactor244
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (M : ℝ) :
    ∃ R : ℕ, n ≤ R ∧ M < ((R : ℝ) + 1) ^ 2 * ε ^ 2 := by
  have hεSq : 0 < ε ^ 2 := pow_pos hε 2
  obtain ⟨R, hR⟩ :=
    exists_nat_gt (max (n : ℝ) (M / ε ^ 2 + 1))
  have hnR : (n : ℝ) ≤ (R : ℝ) :=
    (le_max_left _ _).trans hR.le
  have hn : n ≤ R := by exact_mod_cast hnR
  have hHeight : M / ε ^ 2 < (R : ℝ) := by
    have hMax := (le_max_right (n : ℝ) (M / ε ^ 2 + 1))
    linarith only [hR, hMax]
  have hLinear : M < (R : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ hεSq).mp hHeight
  have hSquare : (R : ℝ) ≤ ((R : ℝ) + 1) ^ 2 := by
    have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    nlinarith [sq_nonneg (R : ℝ)]
  refine ⟨R, hn, ?_⟩
  exact hLinear.trans_le
    (mul_le_mul_of_nonneg_right hSquare hεSq.le)

/-- Absence of an actual terminal H³ trace gives a SINGLE sequence approaching
T on which the genuine high-radial and full physical H³ dissipation exceed
ANY prescribed finite height profile `M n` at the natural n+1 cutoff.

The radius used to select each witness may be much larger than n+1, but the
witness is transferred back to n+1 using actual radial dissipation
monotonicity. There is no hypothesis on the rate of growth of M. -/
theorem thirdFullPhysical_noH3Trace_arbitraryViscousHeightDiagonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (M : ℕ → ℝ) :
    ∃ τ : ℕ → ℝ,
      (∀ n, τ n ∈ Set.Ioo b T) ∧
      (∀ n, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n, M n < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ n, M n < velocityH3DissipationAt u (τ n)) := by
  classical
  obtain ⟨ε, hε, hEscape⟩ :=
    (thirdFullPhysical_noH3Trace_iff_cofinalHighRadialEscape244
      hH3 hClass b hb).mp hNoTrace
  have hWitness (n : ℕ) :
      ∃ (R : ℕ) (t : ℝ), n ≤ R ∧
        t ∈ Set.Ioo b T ∧
        T - t < (1 : ℝ) / ((n : ℝ) + 1) ∧
        M n < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
        M n < velocityH3DissipationAt u t := by
    obtain ⟨R, hnR, hHeight⟩ :=
      thirdFull_exists_largeRadialDissipationFactor244 ε hε n (M n)
    obtain ⟨t, ht, hNear, hTail⟩ :=
      hEscape R ((1 : ℝ) / ((n : ℝ) + 1)) (by positivity)
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 ht.1, ht.2⟩
    have hSq : ε ^ 2 ≤
        ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2 :=
      (sq_le_sq₀ hε.le (norm_nonneg _)).mpr hTail
    have hScaled :
        M n < ((R : ℝ) + 1) ^ 2 *
          ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2 :=
      hHeight.trans_le
        (mul_le_mul_of_nonneg_left hSq (sq_nonneg _))
    have hHigh := thirdFullPhysical_highRadialViscousCoercivity244
      hH3 hClass t htClass R
    have hFull := thirdFullPhysical_fullViscousCoercivity244
      hH3 hClass t htClass R
    have hCast : (n : ℝ) ≤ (R : ℝ) := by exact_mod_cast hnR
    have hCut : (n : ℝ) + 1 ≤ (R : ℝ) + 1 :=
      add_le_add_left hCast 1
    have hMono := h3Path_actualHighRadialDissipation_antitone_radius244
      hH3 hClass t htClass hCut
    exact ⟨R, t, hnR, ht, hNear,
      (hScaled.trans_le hHigh).trans_le hMono,
      hScaled.trans_le hFull⟩
  choose R τ hInfo using hWitness
  have hτ (n : ℕ) : τ n ∈ Set.Ioo b T := (hInfo n).2.1
  have hNear (n : ℕ) :
      T - τ n < (1 : ℝ) / ((n : ℝ) + 1) := (hInfo n).2.2.1
  have hHigh (n : ℕ) :
      M n < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) := (hInfo n).2.2.2.1
  have hFull (n : ℕ) :
      M n < velocityH3DissipationAt u (τ n) := (hInfo n).2.2.2.2
  have hDist (n : ℕ) :
      dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1) := by
    simpa only [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (hτ n).2.le), neg_sub] using hNear n
  have hLimit : Tendsto τ atTop (𝓝 T) := by
    apply Metric.tendsto_atTop.2
    intro η hη
    have hRadius : Tendsto
        (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hEvent : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / ((n : ℝ) + 1) < η :=
      hRadius.eventually (eventually_lt_nhds hη)
    rw [Filter.eventually_atTop] at hEvent
    obtain ⟨N, hN⟩ := hEvent
    exact ⟨N, fun n hn => (hDist n).trans (hN n hn)⟩
  exact ⟨τ, hτ, hDist, hLimit, hHigh, hFull⟩

end
end PrimeTensor.FirstMonomialTriad
