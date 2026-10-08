import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalDissipationOnlyDeficit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Rate

/-!
# A physical Fourier-interpolation corridor for the cubic H3 dissipation deficit

The established *analytic* Fourier moment inequality says

  E₃(t)^4 <= E₀(t) D₃(t)^3,

where E₀ is kinetic L2 energy, E₃ the top H3 block, and D₃ its
fourth-order viscous dissipation. The physical kinetic energy is antitone;
full dissipation D dominates D₃. Therefore, for a fixed kinetic anchor b<t,

  E₃(t)^4 <= (E₀(b)+1) D(t)^3.

The preceding module identified every time with unabsorbed growth U(t)>M,
M>=0, as a *strict* cubic-dissipation deficit:

  2D(t) + M E(t) < A sqrt(E(t)) E(t),
  A = 4422 C1.

Combining these independent, already-closed PDE inequalities gives a new
physical-time moment corridor at every high-U time:

  8 E₃(t)^4 < (E₀(b)+1) [A sqrt(E(t)) E(t)-M E(t)]^3.

The reverse weak moment inequality is therefore a sufficient pointwise
criterion for U<=M, and if it holds throughout a terminal tail, the
established integrable-linear-growth theorem gives continuation.

This does NOT establish the reverse moment inequality: interpolative
coercivity is of order D~E₃^(4/3), below the required cubic E^(3/2)
scale. The result identifies a concrete physical PDE interpolation gap,
not an unconditional resolution of finite-time singularities.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Fixed-kinetic-anchor Fourier interpolation transferred from top
fourth-order dissipation to the actual full H3 viscous dissipation. -/
theorem h3PathCanonical_topMoment_le_kineticAnchor_mul_fullDissipationCube
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    velocityH3Energy3At u t ^ 4 ≤
      (velocityH3Energy0At u b + 1) * velocityH3DissipationAt u t ^ 3 := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hAnti : AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass ht.1.le
  have hMoment :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3 hClass htClass
  have hD3Nonneg : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hD3Bound : velocityH3Dissipation3At u t ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hDcube : velocityH3Dissipation3At u t ^ 3 ≤
      velocityH3DissipationAt u t ^ 3 :=
    pow_le_pow_left₀ hD3Nonneg hD3Bound 3
  have hDcubeNonneg : 0 ≤ velocityH3Dissipation3At u t ^ 3 :=
    pow_nonneg hD3Nonneg 3
  have hFullCubeNonneg : 0 ≤ velocityH3DissipationAt u t ^ 3 :=
    pow_nonneg (velocityH3DissipationAt_nonneg u t) 3
  calc
    velocityH3Energy3At u t ^ 4 ≤
        velocityH3Energy0At u t * velocityH3Dissipation3At u t ^ 3 :=
      hMoment
    _ ≤ velocityH3Energy0At u b * velocityH3Dissipation3At u t ^ 3 :=
      mul_le_mul_of_nonneg_right hKinetic hDcubeNonneg
    _ ≤ (velocityH3Energy0At u b + 1) *
          velocityH3Dissipation3At u t ^ 3 := by
      have hMass : velocityH3Energy0At u b ≤ velocityH3Energy0At u b + 1 := by
        linarith
      exact mul_le_mul_of_nonneg_right hMass hDcubeNonneg
    _ ≤ (velocityH3Energy0At u b + 1) *
          velocityH3DissipationAt u t ^ 3 :=
      mul_le_mul_of_nonneg_left hDcube
        (by have h0 := velocityH3Energy0At_nonneg u b; linarith)

/-- The raw *cubic dissipation budget* for a scalar positive growth threshold. -/
noncomputable def h3PathCanonicalCubicDissipationBudget
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (M t : ℝ) : ℝ :=
  ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
    Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
    M * velocityH3EnergyAt u t

/-- Every high-unabsorbed-growth time occupies the strict physical H3
interpolation corridor dictated by the genuine E3/E0/D3 Fourier estimate. -/
theorem h3PathCanonical_highUnabsorbed_forces_anchoredMomentCorridor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    8 * velocityH3Energy3At u t ^ 4 <
      (velocityH3Energy0At u b + 1) *
        (h3PathCanonicalCubicDissipationBudget u M t) ^ 3 := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hDShort :=
    h3PathCanonical_unabsorbedAbove_forces_cubicDissipationShortfall
      hH3 hClass htClass hM hHigh
  let B : ℝ := h3PathCanonicalCubicDissipationBudget u M t
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hB : 2 * velocityH3DissipationAt u t < B := by
    dsimp only [B, h3PathCanonicalCubicDissipationBudget]
    linarith only [hDShort]
  have hCube : (2 * velocityH3DissipationAt u t) ^ 3 < B ^ 3 :=
    pow_lt_pow_left₀ hB (mul_nonneg (by norm_num) hD) (by norm_num)
  have hCube8 : 8 * velocityH3DissipationAt u t ^ 3 < B ^ 3 := by
    nlinarith only [hCube]
  have hMass : 0 < velocityH3Energy0At u b + 1 := by
    have h0 := velocityH3Energy0At_nonneg u b
    linarith only [h0]
  have hMoment :=
    h3PathCanonical_topMoment_le_kineticAnchor_mul_fullDissipationCube
      hH3 hClass hb ht
  have hEight := mul_le_mul_of_nonneg_left hMoment
    (by norm_num : (0 : ℝ) ≤ 8)
  have hStrict := mul_lt_mul_of_pos_left hCube8 hMass
  calc
    8 * velocityH3Energy3At u t ^ 4 ≤
        (velocityH3Energy0At u b + 1) *
          (8 * velocityH3DissipationAt u t ^ 3) := by
      nlinarith only [hEight]
    _ < (velocityH3Energy0At u b + 1) * B ^ 3 := hStrict
    _ = (velocityH3Energy0At u b + 1) *
          (h3PathCanonicalCubicDissipationBudget u M t) ^ 3 := rfl

/-- Reversing the strict Fourier moment corridor certifies that actual
unabsorbed nonlinear growth does not exceed the chosen threshold. -/
theorem h3PathCanonical_unabsorbed_le_of_anchoredMomentBarrier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hBarrier :
      (velocityH3Energy0At u b + 1) *
          (h3PathCanonicalCubicDissipationBudget u M t) ^ 3 ≤
        8 * velocityH3Energy3At u t ^ 4) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤ M := by
  by_contra hNot
  have hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t :=
    lt_of_not_ge hNot
  have hCorridor := h3PathCanonical_highUnabsorbed_forces_anchoredMomentCorridor
    hH3 hClass hb ht hM hHigh
  exact (not_lt_of_ge hBarrier) hCorridor

/-- A strict physical terminal tail satisfying the moment barrier with a
fixed finite tolerance would have an integrable growth majorant and extend. -/
theorem h3PathCanonical_extension_of_eventual_anchoredMomentBarrier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hBarrier : ∀ t : ℝ, t ∈ Set.Ioo d T →
      (velocityH3Energy0At u b + 1) *
          (h3PathCanonicalCubicDissipationBudget u M t) ^ 3 ≤
        8 * velocityH3Energy3At u t ^ 4) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hdClass : d ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hd.1, hd.2⟩
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass
      (le_of_lt hdClass.1) hdClass.2
  have hConst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo d T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hBound : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathCanonicalUnabsorbedRiccatiRate u t ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact h3PathCanonical_unabsorbed_le_of_anchoredMomentBarrier
      hH3 hClass hb ⟨lt_trans hd.1 ht.1, ht.2⟩ hM (hBarrier t ht)
  exact h3PathCanonical_extension_of_ae_integrable_unabsorbed_majorant
    hH3 hClassD hConst hBound

/-- Neutral obstruction: on a hypothetical nonextension path there are
arbitrarily late physical times of arbitrarily large unabsorbed growth,
and the independent top-order Fourier moment corridor must hold there. -/
theorem h3PathCanonical_anchoredMomentCorridor_witness_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      M < h3PathCanonicalUnabsorbedRiccatiRate u t ∧
      8 * velocityH3Energy3At u t ^ 4 <
        (velocityH3Energy0At u b + 1) *
          (h3PathCanonicalCubicDissipationBudget u M t) ^ 3 := by
  have hdClass : d ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hd.1, hd.2⟩
  obtain ⟨t, ht, hHigh⟩ :=
    h3PathCanonical_unabsorbedRiccatiRate_unbounded_on_tail
      M hH3 hNoExtension hClass hdClass
  exact ⟨t, ht, hHigh,
    h3PathCanonical_highUnabsorbed_forces_anchoredMomentCorridor
      hH3 hClass hb ⟨lt_trans hd.1 ht.1, ht.2⟩ hM hHigh⟩

end Euclidean
end Bridge
end PrimeTensor
