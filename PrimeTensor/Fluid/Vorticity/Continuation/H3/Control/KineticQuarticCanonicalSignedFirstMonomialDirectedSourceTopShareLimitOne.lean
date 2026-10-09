import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceSharperTopShare

/-!
# Fixed directed H³ obstruction: asymptotically all energy is top-order

The fixed source sequence has E₃(τ n) → +∞ and a uniform kinetic anchor.
The radial polynomial inequality, for A >= 1 and q >= 0,

  q + q² <= (A + A²) + (2/A) q³,

yields E₁ + E₂ <= (A + A²) E₀ + (2/A) E₃ on admissible slices.
With A fixed sufficiently large and E₀ bounded by the kinetic anchor,
E <= (1+epsilon) E₃ eventually for every epsilon > 0. Consequently the
actual selected terminal sequence satisfies E₃/E → 1.

The fixed index, indexed strict source inequality, all three critical
physical clocks, the full gradient top-share clock, and the alternative
fixed adverse ordered monomial are preserved. Neither PDE branch is
excluded; this is a necessary condition for hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TopShareLimitOne
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TopShareLimitOne :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Adjustable radial cubic dominates the first two spectral moments,
up to a finite zeroth-moment cost. -/
theorem h3PathCanonical_firstSecondRadialPolynomial_scaled
    (A q : ℝ) (hA : 1 ≤ A) (hq : 0 ≤ q) :
    q + q ^ 2 ≤ (A + A ^ 2) + (2 / A) * q ^ 3 := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  by_cases hqA : q ≤ A
  · have hSq : q ^ 2 ≤ A ^ 2 := by
      have hProduct : 0 ≤ (A - q) * (A + q) :=
        mul_nonneg (sub_nonneg.mpr hqA) (add_nonneg hApos.le hq)
      nlinarith only [hProduct]
    have hTerm : 0 ≤ (2 / A) * q ^ 3 := by positivity
    linarith only [hqA, hSq, hTerm]
  · have hAq : A ≤ q := le_of_lt (lt_of_not_ge hqA)
    have hOneQ : 1 ≤ q := le_trans hA hAq
    have hFirst : A * q ≤ q ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hAq) hq]
    have hSecond : A * q ^ 2 ≤ q ^ 3 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hAq) (sq_nonneg q)]
    have hThird : q ^ 2 ≤ q ^ 3 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hOneQ) (sq_nonneg q)]
    have hMul : A * (q + q ^ 2) ≤ 2 * q ^ 3 := by
      nlinarith only [hFirst, hSecond, hThird]
    have hDiv : q + q ^ 2 ≤ (2 * q ^ 3) / A :=
      (le_div_iff₀ hApos).2 (by nlinarith only [hMul])
    have hConst : 0 ≤ A + A ^ 2 := by positivity
    calc
      q + q ^ 2 ≤ (2 * q ^ 3) / A := hDiv
      _ = (2 / A) * q ^ 3 := by ring
      _ ≤ (A + A ^ 2) + (2 / A) * q ^ 3 := by
        linarith only [hConst]

/-- Physical Fourier interpolation with an arbitrarily small coefficient
in front of top-order energy, at a fixed kinetic cost depending on A. -/
theorem h3PathCanonical_firstSecondEnergy_le_kineticCost_add_scaledTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (A : ℝ) (hA : 1 ≤ A) :
    velocityH3Energy1At u t + velocityH3Energy2At u t ≤
      (A + A ^ 2) * velocityH3Energy0At u t +
        (2 / A) * velocityH3Energy3At u t := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt
  let S : H3FourierPoint3 → ℝ :=
    velocityH3FourierMassDensityAt u t hInt hMeas
  let q : H3FourierPoint3 → ℝ := h3FourierGradientSquare
  have h0Int : Integrable S volume := by
    dsimp only [S]
    exact velocityH3FourierMassDensityAt_integrable u t hInt hMeas
  have h1Int : Integrable (fun ξ => q ξ * S ξ) volume := by
    dsimp only [q, S]
    exact velocityH3FourierFirstAggregateDensity_integrable hInt hMeas hFourier
  have h2Int : Integrable (fun ξ => q ξ ^ 2 * S ξ) volume := by
    dsimp only [q, S]
    exact velocityH3FourierSecondAggregateDensity_integrable hInt hMeas hFourier
  have h3Int : Integrable (fun ξ => q ξ ^ 3 * S ξ) volume := by
    dsimp only [q, S]
    exact velocityH3FourierThirdAggregateDensity_integrable hInt hMeas hFourier
  have hPointwise (ξ : H3FourierPoint3) :
      q ξ * S ξ + q ξ ^ 2 * S ξ ≤
        (A + A ^ 2) * S ξ + (2 / A) * (q ξ ^ 3 * S ξ) := by
    have hq : 0 ≤ q ξ := h3FourierGradientSquare_nonneg ξ
    have hS : 0 ≤ S ξ := by
      dsimp only [S]
      exact velocityH3FourierMassDensityAt_nonneg u t hInt hMeas ξ
    have hPoly := h3PathCanonical_firstSecondRadialPolynomial_scaled
      A (q ξ) hA hq
    calc
      q ξ * S ξ + q ξ ^ 2 * S ξ =
          (q ξ + q ξ ^ 2) * S ξ := by ring
      _ ≤ ((A + A ^ 2) + (2 / A) * q ξ ^ 3) * S ξ :=
        mul_le_mul_of_nonneg_right hPoly hS
      _ = _ := by ring
  have hIntegral :
      (∫ ξ : H3FourierPoint3, q ξ * S ξ ∂volume) +
        (∫ ξ : H3FourierPoint3, q ξ ^ 2 * S ξ ∂volume) ≤
      (A + A ^ 2) * (∫ ξ : H3FourierPoint3, S ξ ∂volume) +
        (2 / A) * (∫ ξ : H3FourierPoint3, q ξ ^ 3 * S ξ ∂volume) := by
    have hBound :
        (∫ ξ : H3FourierPoint3,
          q ξ * S ξ + q ξ ^ 2 * S ξ ∂volume) ≤
        (∫ ξ : H3FourierPoint3,
          (A + A ^ 2) * S ξ + (2 / A) * (q ξ ^ 3 * S ξ) ∂volume) := by
      exact MeasureTheory.integral_mono
        (h1Int.add h2Int)
        ((h0Int.const_mul (A + A ^ 2)).add (h3Int.const_mul (2 / A)))
        hPointwise
    calc
      _ = ∫ ξ : H3FourierPoint3,
            q ξ * S ξ + q ξ ^ 2 * S ξ ∂volume :=
          (MeasureTheory.integral_add h1Int h2Int).symm
      _ ≤ ∫ ξ : H3FourierPoint3,
            (A + A ^ 2) * S ξ + (2 / A) * (q ξ ^ 3 * S ξ) ∂volume := hBound
      _ = (∫ ξ : H3FourierPoint3, (A + A ^ 2) * S ξ ∂volume) +
            (∫ ξ : H3FourierPoint3, (2 / A) * (q ξ ^ 3 * S ξ) ∂volume) :=
          MeasureTheory.integral_add
            (h0Int.const_mul (A + A ^ 2)) (h3Int.const_mul (2 / A))
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  have h0 := velocityH3Energy0At_eq_fourierZerothRadialMoment hInt hMeas
  have h1 := velocityH3Energy1At_eq_fourierFirstRadialMoment hInt hMeas hFourier
  have h2 := velocityH3Energy2At_eq_fourierSecondRadialMoment hInt hMeas hFourier
  have h3 := velocityH3Energy3At_eq_fourierThirdRadialMoment hInt hMeas hFourier
  rw [h0, h1, h2, h3]
  rw [velocityH3FourierFirstRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier,
    velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier,
    velocityH3FourierZerothRadialMomentAt_eq_integral_massDensity
      hInt hMeas,
    velocityH3FourierThirdRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier]
  exact hIntegral

/-- The physical H³ energy obeys an arbitrarily small top-energy
coefficient above one, paying only a fixed anchored kinetic remainder. -/
theorem h3PathCanonical_fullEnergy_le_anchorCost_add_scaledTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (A : ℝ) (hA : 1 ≤ A) :
    velocityH3EnergyAt u t ≤
      (1 + (1 + A + A ^ 2) * velocityH3Energy0At u b) +
        (1 + 2 / A) * velocityH3Energy3At u t := by
  have hAnti : AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass (le_of_lt ht.1)
  have hInterpolation :=
    h3PathCanonical_firstSecondEnergy_le_kineticCost_add_scaledTop
      hH3 hClass htClass A hA
  have hCoefficient : 0 ≤ 1 + A + A ^ 2 := by
    have hApos : 0 ≤ A := le_trans (by norm_num) hA
    positivity
  have hKineticScaled := mul_le_mul_of_nonneg_left hKinetic hCoefficient
  unfold velocityH3EnergyAt
  nlinarith only [hInterpolation, hKineticScaled]

/-- Divergence of E₃ makes the anchored kinetic cost negligible. The
coefficient of E₃ tends to one, not merely two or three. -/
theorem h3PathCanonical_eventually_fullEnergy_le_one_add_epsilon_top
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hτT : Tendsto τ atTop (𝓝 T))
    (hτUpper : ∀ n : ℕ, τ n < T)
    (hTopT : Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n))
      atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      velocityH3EnergyAt u (τ n) ≤
        (1 + ε) * velocityH3Energy3At u (τ n) := by
  let A : ℝ := 1 + 4 / ε
  have hA : 1 ≤ A := by
    dsimp only [A]
    have hDiv : 0 ≤ (4 : ℝ) / ε := div_nonneg (by norm_num) hε.le
    linarith only [hDiv]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hRatio : 2 / A ≤ ε / 2 := by
    have hAHigh : 4 / ε ≤ A := by
      dsimp only [A]
      have hOne : 0 ≤ (1 : ℝ) := by norm_num
      linarith only [hOne]
    have hScaled := mul_le_mul_of_nonneg_left hAHigh hε.le
    have hCancel : ε * (4 / ε) = 4 := by
      field_simp [ne_of_gt hε]
    have hFour : 4 ≤ ε * A := by
      nlinarith only [hScaled, hCancel]
    exact (div_le_iff₀ hApos).2 (by nlinarith only [hFour])
  let C : ℝ := 1 + (1 + A + A ^ 2) * velocityH3Energy0At u b
  let M : ℝ := (2 * C) / ε
  have hTopLarge : ∀ᶠ n : ℕ in atTop,
      M ≤ velocityH3Energy3At u (τ n) :=
    (tendsto_atTop.1 hTopT) M
  have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
    (tendsto_order.1 hτT).1 b hb.2
  filter_upwards [hTopLarge, hLate] with n hLarge hnLate
  have ht : τ n ∈ Set.Ioo b T := ⟨hnLate, hτUpper n⟩
  have hAnchor : velocityH3EnergyAt u (τ n) ≤
      C + (1 + 2 / A) * velocityH3Energy3At u (τ n) := by
    simpa only [C] using h3PathCanonical_fullEnergy_le_anchorCost_add_scaledTop
      hH3 hClass hb ht A hA
  have hScaled : (ε / 2) * M ≤
      (ε / 2) * velocityH3Energy3At u (τ n) :=
    mul_le_mul_of_nonneg_left hLarge (by positivity)
  have hCancel : (ε / 2) * M = C := by
    dsimp only [M]
    field_simp [ne_of_gt hε]
  have hSmall : C ≤ (ε / 2) * velocityH3Energy3At u (τ n) := by
    linarith only [hScaled, hCancel]
  have hRatioScaled :
      (2 / A) * velocityH3Energy3At u (τ n) ≤
        (ε / 2) * velocityH3Energy3At u (τ n) :=
    mul_le_mul_of_nonneg_right hRatio
      (velocityH3Energy3At_nonneg u (τ n))
  calc
    velocityH3EnergyAt u (τ n) ≤
        C + (1 + 2 / A) * velocityH3Energy3At u (τ n) := hAnchor
    _ = C + velocityH3Energy3At u (τ n) +
          (2 / A) * velocityH3Energy3At u (τ n) := by ring
    _ ≤ (ε / 2) * velocityH3Energy3At u (τ n) +
          velocityH3Energy3At u (τ n) +
          (ε / 2) * velocityH3Energy3At u (τ n) := by
      linarith only [hSmall, hRatioScaled]
    _ = (1 + ε) * velocityH3Energy3At u (τ n) := by ring

/-- Convert an arbitrary epsilon upper full-energy bound into a share
lower bound tending to one. -/
theorem h3PathCanonical_topShare_ge_inv_one_add_epsilon
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t ε : ℝ)
    (hε : 0 < ε)
    (hUpper : velocityH3EnergyAt u t ≤
      (1 + ε) * velocityH3Energy3At u t) :
    1 / (1 + ε) ≤
      velocityH3Energy3At u t / velocityH3EnergyAt u t := by
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hCoeff : 0 < 1 + ε := by linarith only [hε]
  have hDivide : velocityH3EnergyAt u t / (1 + ε) ≤
      velocityH3Energy3At u t :=
    (div_le_iff₀ hCoeff).2 (by
      calc
        velocityH3EnergyAt u t ≤
            (1 + ε) * velocityH3Energy3At u t := hUpper
        _ = velocityH3Energy3At u t * (1 + ε) := by ring)
  apply (le_div_iff₀ hE).2
  calc
    (1 / (1 + ε)) * velocityH3EnergyAt u t =
        velocityH3EnergyAt u t / (1 + ε) := by ring
    _ ≤ velocityH3Energy3At u t := hDivide

/-- Quantified eventual full/top comparisons imply convergence of the
actual physical top-order energy fraction to one. -/
theorem h3PathCanonical_topShare_tendsto_one_of_eventually_upper
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n : ℕ in atTop,
        velocityH3EnergyAt u (τ n) ≤
          (1 + ε) * velocityH3Energy3At u (τ n))) :
    Tendsto (fun n : ℕ =>
      velocityH3Energy3At u (τ n) / velocityH3EnergyAt u (τ n))
      atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    let ε : ℝ := (1 - c) / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      linarith only [hc]
    have hCoeff : 0 < 1 + ε := by linarith only [hε]
    have hFactor : 0 < (1 - c) * (2 - c) :=
      mul_pos (by linarith only [hc]) (by linarith only [hc])
    have hcBelow : c < 1 / (1 + ε) := by
      apply (lt_div_iff₀ hCoeff).2
      dsimp only [ε]
      nlinarith only [hFactor]
    filter_upwards [hUpper ε hε] with n hn
    exact lt_of_lt_of_le hcBelow
      (h3PathCanonical_topShare_ge_inv_one_add_epsilon u (τ n) ε hε hn)
  · intro c hc
    exact Filter.Eventually.of_forall (fun n => by
      have hE : 0 < velocityH3EnergyAt u (τ n) :=
        lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
      have hTop : velocityH3Energy3At u (τ n) ≤
          velocityH3EnergyAt u (τ n) :=
        velocityH3Energy3At_le_velocityH3EnergyAt u (τ n)
      exact lt_of_le_of_lt ((div_le_iff₀ hE).2 (by simpa using hTop)) hc)

/-- On the original indexed fixed-source nonextension sequence, the
physical top-order energy fraction converges to one. The gradient full
budget and signed ordered monomial remain neutral exhaustive branches. -/
theorem h3PathCanonical_fixedDirectedSource_topShareLimitOne_withPhysicalAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ,
        τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        velocityH3Energy3At u (τ n) / velocityH3EnergyAt u (τ n))
        atTop (𝓝 1) ∧
      (∀ ε : ℝ, 0 < ε →
        (∀ᶠ n : ℕ in atTop,
          velocityH3EnergyAt u (τ n) ≤
            (1 + ε) * velocityH3Energy3At u (τ n))) ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (τ n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientTopShareClockAt u T b (τ n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n))) := by
  obtain ⟨i, τ, hWitness, hτT, hTopT, _hOldShare, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_sharperTopShare_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  have hUpper : ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n : ℕ in atTop,
        velocityH3EnergyAt u (τ n) ≤
          (1 + ε) * velocityH3Energy3At u (τ n)) := by
    intro ε hε
    exact h3PathCanonical_eventually_fullEnergy_le_one_add_epsilon_top
      hH3 hClass hb hτT (fun n => (hWitness n).1.2) hTopT ε hε
  exact ⟨i, τ, hWitness, hτT, hTopT,
    h3PathCanonical_topShare_tendsto_one_of_eventually_upper u τ hUpper,
    hUpper, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
