import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticGapLowBandPDEFreezing
import Mathlib.Tactic

/-!
# Moving-radius physical PDE costs on the original kinetic sixth-flux gaps

The fixed-frequency low H3 Fourier state freezes on every late kinetic gap,
but a radius chosen along the gaps can grow. Here the genuinely physical
Bochner source action is multiplied by the exact native W3 finite-band ceiling.
If that product vanishes, the whole moving low band freezes uniformly over
all pairs of times in the same gap. Conversely, a persistent moving low-band
excursion, with vanishing source action, forces its chosen radius to infinity.
This proves a quantitative *temporal* radial-escape condition; it does not
assert continuity of the low-maximum signed sixth-order flux functional.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeKineticMovingGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Monotonicity of the exact square-root W3 polynomial multiplier ceiling.
The cutoff comparison is quantitative, with no high-frequency compactness. -/
theorem thirdFullKineticGap_finiteBandCeiling_mono244
    (r n : ℕ) (hrn : r ≤ n) :
    thirdFullFiniteBandH3WeightCeiling244 r ≤
      thirdFullFiniteBandH3WeightCeiling244 n := by
  have hρ : (r : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast (Nat.add_le_add_right hrn 1)
  have hρ0 : 0 ≤ (r : ℝ) + 1 := by positivity
  have h2 := pow_le_pow_left₀ hρ0 hρ 2
  have h4 := pow_le_pow_left₀ hρ0 hρ 4
  have h6 := pow_le_pow_left₀ hρ0 hρ 6
  unfold thirdFullFiniteBandH3WeightCeiling244
  apply Real.sqrt_le_sqrt
  linarith only [h2, h4, h6]

/-- The exact W3 finite-band ceiling grows at most cubically with the
natural cutoff. This is the derivative-counting exponent in physical H3. -/
theorem thirdFullKineticGap_finiteBandCeiling_le_cubic244
    (R : ℕ) :
    thirdFullFiniteBandH3WeightCeiling244 R ≤
      2 * ((R : ℝ) + 1) ^ 3 := by
  let ρ : ℝ := (R : ℝ) + 1
  have hρ : 1 ≤ ρ := by
    dsimp only [ρ]
    have hNonneg : 0 ≤ (R : ℝ) := by positivity
    linarith only [hNonneg]
  have hρ0 : 0 ≤ ρ := le_trans (by norm_num) hρ
  have hOne (n : ℕ) : 1 ≤ ρ ^ n := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hρ n)
  have hTwo : ρ ^ 2 ≤ ρ ^ 6 := by
    calc
      ρ ^ 2 = ρ ^ 2 * 1 := by ring
      _ ≤ ρ ^ 2 * ρ ^ 4 :=
        mul_le_mul_of_nonneg_left (hOne 4) (pow_nonneg hρ0 2)
      _ = ρ ^ 6 := by ring
  have hFour : ρ ^ 4 ≤ ρ ^ 6 := by
    calc
      ρ ^ 4 = ρ ^ 4 * 1 := by ring
      _ ≤ ρ ^ 4 * ρ ^ 2 :=
        mul_le_mul_of_nonneg_left (hOne 2) (pow_nonneg hρ0 4)
      _ = ρ ^ 6 := by ring
  have hSq : 1 + ρ ^ 2 + ρ ^ 4 + ρ ^ 6 ≤ (2 * ρ ^ 3) ^ 2 := by
    nlinarith only [hOne 6, hTwo, hFour]
  unfold thirdFullFiniteBandH3WeightCeiling244
  change Real.sqrt (1 + ρ ^ 2 + ρ ^ 4 + ρ ^ 6) ≤ 2 * ρ ^ 3
  calc
    Real.sqrt (1 + ρ ^ 2 + ρ ^ 4 + ρ ^ 6) ≤
        Real.sqrt ((2 * ρ ^ 3) ^ 2) := Real.sqrt_le_sqrt hSq
    _ = 2 * ρ ^ 3 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg hρ0 3))]

/-- Scalar escape lemma: an L1 clock tending to zero cannot pay a fixed
positive low-band jump while the natural-radius multiplier stays bounded.
The exact W3 ceiling is used, not a guessed power or a Fourier L∞ bound. -/
theorem thirdFullKineticGap_scalar_movingCeilingEscape244
    (R : ℕ → ℕ) (S : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (hSNonneg : ∀ k : ℕ, 0 ≤ S k)
    (hSZero : Tendsto S atTop (𝓝 (0 : ℝ)))
    (hJump : ∀ᶠ k : ℕ in atTop,
      η ≤ thirdFullFiniteBandH3WeightCeiling244 (R k) * S k) :
    Tendsto R atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  let K : ℝ := thirdFullFiniteBandH3WeightCeiling244 n + 1
  have hK : 0 < K := by
    dsimp only [K]
    have hc := thirdFullFiniteBandH3WeightCeiling_nonneg244 n
    linarith only [hc]
  have hSmallArg : 0 < η / K := div_pos hη hK
  have hEventually : ∀ᶠ k : ℕ in atTop, S k < η / K :=
    hSZero.eventually (eventually_lt_nhds hSmallArg)
  filter_upwards [hJump, hEventually] with k hk hSmall
  by_contra hNot
  have hRlt : R k < n := lt_of_not_ge hNot
  have hMono := thirdFullKineticGap_finiteBandCeiling_mono244
    (R k) n hRlt.le
  have hKBound : thirdFullFiniteBandH3WeightCeiling244 n ≤ K := by
    dsimp only [K]
    linarith
  have hAbsurd : η < η := by
    calc
      η ≤ thirdFullFiniteBandH3WeightCeiling244 (R k) * S k := hk
      _ ≤ thirdFullFiniteBandH3WeightCeiling244 n * S k :=
        mul_le_mul_of_nonneg_right hMono (hSNonneg k)
      _ ≤ K * S k :=
        mul_le_mul_of_nonneg_right hKBound (hSNonneg k)
      _ < K * (η / K) := mul_lt_mul_of_pos_left hSmall hK
      _ = η := mul_div_cancel₀ η hK.ne'
  exact (lt_irrefl η) hAbsurd

/-- Every PAIR of physical times in one strict gap satisfies a common
moving-radius low-H3 Fourier modulus, with the full physical source action
on the WHOLE gap on the right. No reference to a Schwartz selection enters. -/
theorem thirdFullPhysical_strictGap_uniformLowBandPDEModulus244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hy : y ∈ Set.Ioo (0 : ℝ) T)
    (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        ∫ r in x..y,
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hGInt : IntervalIntegrable G volume x y :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 hx.1 hxy hy.2
  have hInside (p : ℝ) (hp : p ∈ Set.Icc x y) :
      p ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hx.1 hp.1, lt_of_le_of_lt hp.2 hy.2⟩
  have hForward (p q : ℝ)
      (hp : p ∈ Set.Icc x y) (hq : q ∈ Set.Icc x y)
      (hpq : p ≤ q) :
      ‖thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 q) -
        thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 p)‖ ≤
        thirdFullFiniteBandH3WeightCeiling244 R *
          ∫ r in x..y, ‖G r‖ ∂volume := by
    have hSubIntegral :
        (∫ r in p..q, ‖G r‖ ∂volume) ≤
          ∫ r in x..y, ‖G r‖ ∂volume :=
      intervalIntegral.integral_mono_interval
        hp.1 hpq hq.2
        (Filter.Eventually.of_forall (fun r => norm_nonneg (G r)))
        hGInt.norm
    calc
      ‖thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 q) -
        thirdFullSpectralVelocityLowRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 p)‖ ≤
          thirdFullFiniteBandH3WeightCeiling244 R *
            ∫ r in p..q, ‖G r‖ ∂volume :=
        thirdFullPhysical_strictLowBandPDEModulus244
          hH3 R p q (hInside p hp) (hInside q hq) hpq
      _ ≤ thirdFullFiniteBandH3WeightCeiling244 R *
            ∫ r in x..y, ‖G r‖ ∂volume :=
        mul_le_mul_of_nonneg_left hSubIntegral
          (thirdFullFiniteBandH3WeightCeiling_nonneg244 R)
  by_cases hst : s ≤ t
  · rw [norm_sub_rev]
    exact hForward s t hs ht hst
  · have hts : t ≤ s := le_of_not_ge hst
    exact hForward t s ht hs hts

/-- Quantitative cutoff--clock criterion: EVEN A MOVING low-H3 radius
freezes on all pairs of times in each late kinetic gap, provided its exact
W3 multiplier times the genuine projected-source L1 action tends to zero.
No restriction that R(k) is bounded is needed. -/
theorem thirdFullPhysical_kineticGaps_movingLowBandPDEFreeze244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v R : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (hScale : Tendsto (fun k : ℕ =>
      thirdFullFiniteBandH3WeightCeiling244 (R k) *
        ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
      atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ s t : ℝ,
      s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
      t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
      ‖thirdFullSpectralVelocityLowRadialApply244 (R k)
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        thirdFullSpectralVelocityLowRadialApply244 (R k)
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ < ε := by
  have hSmall : ∀ᶠ k : ℕ in atTop,
      thirdFullFiniteBandH3WeightCeiling244 (R k) *
        (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) < ε :=
    hScale.eventually (eventually_lt_nhds hε)
  filter_upwards [hSmall] with k hk
  have hx : τ (v k) + δ (v k) ∈ Set.Ioo (0 : ℝ) T := by
    obtain ⟨ht, hw⟩ := hWindows k
    rcases hw with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [hClass.terminal_start.1, hb.1, ht.1, hδ], hEnd⟩
  have hy : τ (v (k + 1)) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1)
       (hWindows (k + 1)).1.1, (hWindows (k + 1)).1.2⟩
  intro s t hs ht
  exact lt_of_le_of_lt
    (thirdFullPhysical_strictGap_uniformLowBandPDEModulus244
      hH3 (R k) _ _ hx hy
      (hSeparated k (k + 1) (Nat.lt_succ_self k)) s t hs ht) hk

/-- Concrete cubic moving-cutoff criterion: if the physical source L1
action times (R(k)+1)^3 vanishes, then the entire moving low-H3 band freezes
uniformly on all pairs of times within each late kinetic gap. -/
theorem thirdFullPhysical_kineticGaps_cubicMovingCutoffFreeze244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v R : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (hCubic : Tendsto (fun k : ℕ =>
      ((R k : ℝ) + 1) ^ 3 *
        ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
      atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ s t : ℝ,
      s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
      t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
      ‖thirdFullSpectralVelocityLowRadialApply244 (R k)
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        thirdFullSpectralVelocityLowRadialApply244 (R k)
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ < ε := by
  let S : ℕ → ℝ := fun k =>
    ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume
  have hNonneg (k : ℕ) : 0 ≤ S k := by
    dsimp only [S]
    exact intervalIntegral.integral_nonneg
      (hSeparated k (k + 1) (Nat.lt_succ_self k)).le
      (fun r _ => norm_nonneg _)
  have hUpper : Tendsto (fun k : ℕ =>
      2 * (((R k : ℝ) + 1) ^ 3 * S k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul hCubic
  have hScale : Tendsto (fun k : ℕ =>
      thirdFullFiniteBandH3WeightCeiling244 (R k) * S k)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun k =>
        mul_nonneg (thirdFullFiniteBandH3WeightCeiling_nonneg244 (R k))
          (hNonneg k)))
      (Filter.Eventually.of_forall (fun k => by
        calc
          thirdFullFiniteBandH3WeightCeiling244 (R k) * S k ≤
              (2 * ((R k : ℝ) + 1) ^ 3) * S k :=
            mul_le_mul_of_nonneg_right
              (thirdFullKineticGap_finiteBandCeiling_le_cubic244 (R k))
              (hNonneg k)
          _ = 2 * (((R k : ℝ) + 1) ^ 3 * S k) := by ring))
      hUpper
  exact thirdFullPhysical_kineticGaps_movingLowBandPDEFreeze244
    hH3 hClass b hb M τ N δ v R hSeparated hWindows
    hScale ε hε

/-- Any persistent positive low-H3 excursion on the exact late kinetic
gaps forces its chosen moving radial cutoff to diverge. This uses the
unconditional physical momentum FTC and the finite-H3-dissipation source L1
limit. It does NOT claim that the signed low-maximum sixth flux itself has
an analogous continuity bound. -/
theorem thirdFullPhysical_kineticGaps_lowBandExcursion_forcesRadialEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v R : ℕ → ℕ)
    (hCofinal : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (η : ℝ) (hη : 0 < η)
    (hJump : ∀ᶠ k : ℕ in atTop,
      ∃ s t : ℝ,
        s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
        t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
        η ≤ ‖thirdFullSpectralVelocityLowRadialApply244 (R k)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          thirdFullSpectralVelocityLowRadialApply244 (R k)
            (h3AuditActualSpectralVelocityTotal hH3 t)‖) :
    Tendsto R atTop atTop := by
  let S : ℕ → ℝ := fun k =>
    ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume
  have hZero : Tendsto S atTop (𝓝 (0 : ℝ)) :=
    thirdFullPhysical_kineticGaps_sourceL1_tendsto_zero244
      hH3 hClass hDInt b hb M τ N δ v hCofinal hSeparated hWindows
  have hNonneg (k : ℕ) : 0 ≤ S k := by
    dsimp only [S]
    exact intervalIntegral.integral_nonneg
      (hSeparated k (k + 1) (Nat.lt_succ_self k)).le
      (fun r _ => norm_nonneg _)
  have hCost : ∀ᶠ k : ℕ in atTop,
      η ≤ thirdFullFiniteBandH3WeightCeiling244 (R k) * S k := by
    filter_upwards [hJump] with k hk
    obtain ⟨s, t, hs, ht, hLarge⟩ := hk
    have hx : τ (v k) + δ (v k) ∈ Set.Ioo (0 : ℝ) T := by
      obtain ⟨hTime, hw⟩ := hWindows k
      rcases hw with ⟨_, hd, _, he, _, _⟩
      exact ⟨by linarith only [hClass.terminal_start.1, hb.1,
        hTime.1, hd], he⟩
    have hy : τ (v (k + 1)) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1)
         (hWindows (k + 1)).1.1, (hWindows (k + 1)).1.2⟩
    exact hLarge.trans
      (thirdFullPhysical_strictGap_uniformLowBandPDEModulus244
        hH3 (R k) _ _ hx hy
        (hSeparated k (k + 1) (Nat.lt_succ_self k)) s t hs ht)
  exact thirdFullKineticGap_scalar_movingCeilingEscape244
    R S η hη hNonneg hZero hCost

/-- Retain the EXACT no-terminal-H3-trace kinetic witness family,
including its signed arbitrary-radius sixth-flux tradeoffs, disjoint viscous
charges and raw kinetic tightness. An additional universal moving-cutoff
consequence is forced: any fixed positive low-H3 gap excursion along these
witnesses requires the selected natural cutoffs to diverge. -/
theorem thirdFullPhysical_noH3Trace_kineticMovingRadialGapCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ τ (v k) ∈ Set.Ioo b T ∧
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (M (v k) / 4) *
            ENNReal.ofReal (δ (v k))) ≤
        ∫⁻ r in Set.Ioo a T,
          ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          h3PathActualBandRawKineticMass244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) < ε) ∧
      (∀ k : ℕ, ThirdFullKineticGapArbitraryRadialTradeoff244
        u T hH3 (τ (v k) + δ (v k)) (τ (v (k + 1)))) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ R : ℕ,
        Tendsto (fun k : ℕ =>
          ‖thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v (k + 1)))) -
            thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3
                (τ (v k) + δ (v k)))‖)
          atTop (𝓝 (0 : ℝ))) ∧
      (∀ R : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ∀ s t : ℝ,
          s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
          t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) →
          ‖thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            thirdFullSpectralVelocityLowRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ < ε) ∧
      (∀ R : ℕ → ℕ, ∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          ∃ s t : ℝ,
            s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
            t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
            η ≤ ‖thirdFullSpectralVelocityLowRadialApply244 (R k)
                (h3AuditActualSpectralVelocityTotal hH3 s) -
              thirdFullSpectralVelocityLowRadialApply244 (R k)
                (h3AuditActualSpectralVelocityTotal hH3 t)‖) →
        Tendsto R atTop atTop) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, hTradeoff,
    hGapSource, hLow, hAll⟩ :=
    thirdFullPhysical_noH3Trace_kineticGapLowBandPDEFreezing244
      hH3 hClass b hb hNoTrace hDInt M hM
  have hWindows (k : ℕ) :
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)) :=
    ⟨(hTimes k).2.1, (hTimes k).2.2⟩
  have hEscape (R : ℕ → ℕ) (η : ℝ) (hη : 0 < η)
      (hJump : ∀ᶠ k : ℕ in atTop,
        ∃ s t : ℝ,
          s ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
          t ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
          η ≤ ‖thirdFullSpectralVelocityLowRadialApply244 (R k)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            thirdFullSpectralVelocityLowRadialApply244 (R k)
              (h3AuditActualSpectralVelocityTotal hH3 t)‖) :
      Tendsto R atTop atTop :=
    thirdFullPhysical_kineticGaps_lowBandExcursion_forcesRadialEscape244
      hH3 hClass hDInt b hb M τ N δ v R
      hCofinal hSeparated hWindows η hη hJump
  exact ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hTimes, hCharges, hL1, hUniform, hTradeoff,
    hGapSource, hLow, hAll, hEscape⟩

end
end PrimeTensor.FirstMonomialTriad
