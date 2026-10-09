import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceUniversalTopShare
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalAllLowerOrderAbsorption
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.Moment.Density

/-!
# Sharper universal physical H³ top-energy share from a signed radial polynomial

A new elementary *physical Fourier interpolation* yields

  E₁(t) + E₂(t) ≤ E₀(t) + E₃(t),

because q + q² ≤ 1 + q³ for the nonnegative radial frequency q = |ξ|²:

  1 + q³ - q - q² = (q - 1)²(q + 1) ≥ 0.

Thus kinetic monotonicity yields E(t) ≤ 1 + 2E₀(b) + 2E₃(t) after the
fixed kinetic anchor b. The SAME fixed directed-source witness sequence
from the previous theorem has E₃(τ n) → +∞. Therefore for each fixed
ε > 0, eventually

  E₃(τ n) ≤ E(τ n) ≤ (2+ε) E₃(τ n),
  1/(2+ε) ≤ E₃(τ n)/E(τ n).

This sharpens the previous coefficient three to two, independently of the
kinetic anchor and without excluding either signed nonextension branch.
It does not establish the limiting top share to be one.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

-- Match the explicit finite-axis and Fourier product measure instances used
-- by `KineticQuarticCanonicalAllLowerOrderAbsorption`. These instances are
-- local so they do not change global measure-space typeclass selection.
noncomputable local instance axisFintypeH3SharperTopShare
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SharperTopShare :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A nonnegative radial Fourier frequency satisfies the exact cubic
factorization needed to bound the first and second moments together. -/
theorem h3PathCanonical_firstSecondRadialPolynomial_le
    (q : ℝ) (hq : 0 ≤ q) :
    q + q ^ 2 ≤ 1 + q ^ 3 := by
  have hFact : 1 + q ^ 3 - (q + q ^ 2) = (q - 1) ^ 2 * (q + 1) := by
    ring
  have hNonneg : 0 ≤ (q - 1) ^ 2 * (q + 1) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hq])
  rw [← hFact] at hNonneg
  linarith only [hNonneg]

/-- New Fourier-moment interpolation on genuine H³ path slices:
`E₁ + E₂ ≤ E₀ + E₃`. No PDE sign or extra regularity hypothesis. -/
theorem h3PathCanonical_firstSecondEnergy_le_kinetic_add_top
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Energy1At u t + velocityH3Energy2At u t ≤
      velocityH3Energy0At u t + velocityH3Energy3At u t := by
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
      q ξ * S ξ + q ξ ^ 2 * S ξ ≤ S ξ + q ξ ^ 3 * S ξ := by
    have hq : 0 ≤ q ξ := h3FourierGradientSquare_nonneg ξ
    have hS : 0 ≤ S ξ := by
      dsimp only [S]
      exact velocityH3FourierMassDensityAt_nonneg u t hInt hMeas ξ
    have hPoly := h3PathCanonical_firstSecondRadialPolynomial_le (q ξ) hq
    have hScaled := mul_le_mul_of_nonneg_right hPoly hS
    nlinarith only [hScaled]
  have hIntegral :
      (∫ ξ : H3FourierPoint3, q ξ * S ξ ∂volume) +
        (∫ ξ : H3FourierPoint3, q ξ ^ 2 * S ξ ∂volume) ≤
      (∫ ξ : H3FourierPoint3, S ξ ∂volume) +
        (∫ ξ : H3FourierPoint3, q ξ ^ 3 * S ξ ∂volume) := by
    have hBound :
        (∫ ξ : H3FourierPoint3, q ξ * S ξ + q ξ ^ 2 * S ξ ∂volume) ≤
          (∫ ξ : H3FourierPoint3, S ξ + q ξ ^ 3 * S ξ ∂volume) := by
      exact MeasureTheory.integral_mono
        (h1Int.add h2Int) (h0Int.add h3Int) hPointwise
    calc
      _ = ∫ ξ : H3FourierPoint3,
            q ξ * S ξ + q ξ ^ 2 * S ξ ∂volume :=
          (MeasureTheory.integral_add h1Int h2Int).symm
      _ ≤ ∫ ξ : H3FourierPoint3,
            S ξ + q ξ ^ 3 * S ξ ∂volume := hBound
      _ = _ := MeasureTheory.integral_add h0Int h3Int
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

/-- A fixed kinetic anchor and the sharper radial interpolation yield a
full-H³ energy coefficient *two* in front of the top-order physical block. -/
theorem h3PathCanonical_fullEnergy_le_kineticAnchor_add_twoTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    velocityH3EnergyAt u t ≤
      (1 + 2 * velocityH3Energy0At u b) +
        2 * velocityH3Energy3At u t := by
  have hAnti : AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass (le_of_lt ht.1)
  have hInterpolation :=
    h3PathCanonical_firstSecondEnergy_le_kinetic_add_top
      hH3 hClass htClass
  unfold velocityH3EnergyAt
  linarith only [hInterpolation, hKinetic]

/-- Along any physical time sequence approaching T with E₃→+∞,
`E ≤ (2+ε) E₃` eventually for each positive ε. -/
theorem h3PathCanonical_eventually_fullEnergy_le_two_add_epsilon_top
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
        (2 + ε) * velocityH3Energy3At u (τ n) := by
  let M : ℝ := (1 + 2 * velocityH3Energy0At u b) / ε
  have hTopLarge : ∀ᶠ n : ℕ in atTop,
      M ≤ velocityH3Energy3At u (τ n) :=
    (tendsto_atTop.1 hTopT) M
  have hLate : ∀ᶠ n : ℕ in atTop, b < τ n :=
    (tendsto_order.1 hτT).1 b hb.2
  filter_upwards [hTopLarge, hLate] with n hLarge hnLate
  have ht : τ n ∈ Set.Ioo b T := ⟨hnLate, hτUpper n⟩
  have hAnchor := h3PathCanonical_fullEnergy_le_kineticAnchor_add_twoTop
    hH3 hClass hb ht
  have hScaled : ε * M ≤ ε * velocityH3Energy3At u (τ n) :=
    mul_le_mul_of_nonneg_left hLarge (le_of_lt hε)
  have hCancel : ε * M = 1 + 2 * velocityH3Energy0At u b := by
    dsimp only [M]
    field_simp [ne_of_gt hε]
  have hSmall :
      1 + 2 * velocityH3Energy0At u b ≤
        ε * velocityH3Energy3At u (τ n) := by
    linarith only [hScaled, hCancel]
  calc
    velocityH3EnergyAt u (τ n) ≤
        (1 + 2 * velocityH3Energy0At u b) +
          2 * velocityH3Energy3At u (τ n) := hAnchor
    _ ≤ ε * velocityH3Energy3At u (τ n) +
          2 * velocityH3Energy3At u (τ n) :=
      add_le_add_left hSmall _
    _ = (2 + ε) * velocityH3Energy3At u (τ n) := by ring

/-- The sharper physical top-energy share lower bound. -/
theorem h3PathCanonical_topShare_ge_inv_two_add_epsilon
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t ε : ℝ)
    (hε : 0 < ε)
    (hUpper : velocityH3EnergyAt u t ≤
      (2 + ε) * velocityH3Energy3At u t) :
    1 / (2 + ε) ≤
      velocityH3Energy3At u t / velocityH3EnergyAt u t := by
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hCoeff : 0 < 2 + ε := by linarith only [hε]
  have hDivide : velocityH3EnergyAt u t / (2 + ε) ≤
      velocityH3Energy3At u t :=
    (div_le_iff₀ hCoeff).2 (by
      calc
        velocityH3EnergyAt u t ≤
            (2 + ε) * velocityH3Energy3At u t := hUpper
        _ = velocityH3Energy3At u t * (2 + ε) := by ring)
  apply (le_div_iff₀ hE).2
  calc
    (1 / (2 + ε)) * velocityH3EnergyAt u t =
        velocityH3EnergyAt u t / (2 + ε) := by ring
    _ ≤ velocityH3Energy3At u t := hDivide

/-- On one unchanged fixed indexed signed-source witness, the top-order
fraction is eventually at least 1/(2+ε) for each ε>0, while all critical
physical clocks and both adverse-source alternatives remain synchronized. -/
theorem h3PathCanonical_fixedDirectedSource_sharperTopShare_withPhysicalAlternative
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
      (∀ ε : ℝ, 0 < ε →
        (∀ᶠ n : ℕ in atTop,
          velocityH3Energy3At u (τ n) ≤ velocityH3EnergyAt u (τ n) ∧
          velocityH3EnergyAt u (τ n) ≤
            (2 + ε) * velocityH3Energy3At u (τ n) ∧
          1 / (2 + ε) ≤
            velocityH3Energy3At u (τ n) / velocityH3EnergyAt u (τ n))) ∧
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
    h3PathCanonical_fixedDirectedSource_universalTopShare_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hWitness, hτT, hTopT, ?_, hClocks, hAlternative⟩
  intro ε hε
  have hUpper :=
    h3PathCanonical_eventually_fullEnergy_le_two_add_epsilon_top
      hH3 hClass hb hτT (fun n => (hWitness n).1.2) hTopT ε hε
  filter_upwards [hUpper] with n hn
  exact ⟨velocityH3Energy3At_le_velocityH3EnergyAt u (τ n), hn,
    h3PathCanonical_topShare_ge_inv_two_add_epsilon u (τ n) ε hε hn⟩

end
end Euclidean
end Bridge
end PrimeTensor
