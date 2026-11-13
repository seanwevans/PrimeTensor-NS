import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalTerminalScaleRigidity
import Mathlib.Tactic

/-!
# The self-calibrated annular clock saturates below the critical time scale

The cap-H physical viscous slope is affine in H. After normalization by
`max 1 (E_b rho^6 slope(H))`, the clock height H/CANNOT grow indefinitely
with H at a positive inner radius and positive kinetic anchor. In fact

  H / CapClockFactor(b,rho,H)
    <= 1 / (18 E_b rho^6 (3 + C_L)^2).

This bound is independent of H, the annular outer radius, and the snapshot
H3 state. Moreover strict actual physical kinetic excess after a positive
earlier kinetic anchor forces E_b > 0. Therefore, on any cofinal physical
time sequence with inner cutoffs bounded below by a positive constant, the
TERMINAL SCALED optimized height (T - x_k)*H_k/C_k tends to zero without
using the finiteness of H3 dissipation or the widths of the clock windows.

This identifies a structural limitation of the cap-normalized clock method:
the critical inverse-terminal-time arm of the previous width/height
dichotomy is ruled out by the normalizer itself at positive inner radius.
It does NOT establish Navier--Stokes continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Scalar saturation: the affine `C * H` term in the denominator caps
H/max(1,A*(B+C*H)) independently of H. -/
theorem thirdFull_scalar_affineCapHeight_saturation244
    (A B C H : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (hC : 0 < C) (hH : 0 ≤ H) :
    H / max 1 (A * (B + C * H)) ≤ 1 / (A * C) := by
  have hDen : 0 < max 1 (A * (B + C * H)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hAC : 0 < A * C := mul_pos hA hC
  have hDominates : H * (A * C) ≤ max 1 (A * (B + C * H)) := by
    calc
      H * (A * C) = A * (C * H) := by ring
      _ ≤ A * (B + C * H) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hB) hA.le
      _ ≤ max 1 (A * (B + C * H)) := le_max_right _ _
  apply (div_le_div_iff₀ hDen hAC).2
  simpa only [one_mul] using hDominates

/-- Exact parameter-independent saturation ceiling of the physical
cap-normalized clock at one strictly positive physical inner radius. -/
noncomputable def thirdFullPhysicalAnnularClockSaturationCeiling244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho : ℝ) : ℝ :=
  1 / (velocityH3Energy0At u b * (rho ^ 2) ^ 3 *
    (18 * (3 + h3AuditInitialLerayEnergyCoefficient) ^ 2))

/-- The saturation ceiling is strictly positive when the earlier kinetic
anchor and actual inner Fourier radius are strictly positive. -/
theorem thirdFullPhysical_annularClockSaturationCeiling_pos244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho : ℝ) (hEnergy : 0 < velocityH3Energy0At u b)
    (hRho : 0 < rho) :
    0 < thirdFullPhysicalAnnularClockSaturationCeiling244 u b rho := by
  have hK : 0 < 3 + h3AuditInitialLerayEnergyCoefficient := by
    linarith only [h3AuditInitialLerayEnergyCoefficient_nonneg]
  unfold thirdFullPhysicalAnnularClockSaturationCeiling244
  positivity

/-- Nonnegative H always has a bounded normalized clock height. The bound
uses the exact coefficient of H in the physical cap-linearization. -/
theorem thirdFullPhysical_annularClockHeight_le_saturation244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho H : ℝ) (hEnergy : 0 < velocityH3Energy0At u b)
    (hRho : 0 < rho) (hH : 0 ≤ H) :
    H / thirdFullPhysicalAnnularCapClockFactor244 u b rho H ≤
      thirdFullPhysicalAnnularClockSaturationCeiling244 u b rho := by
  have hK : 0 < 3 + h3AuditInitialLerayEnergyCoefficient := by
    linarith only [h3AuditInitialLerayEnergyCoefficient_nonneg]
  have hA : 0 < velocityH3Energy0At u b * (rho ^ 2) ^ 3 := by
    positivity
  have hB : 0 ≤
      12 * (3 + h3AuditInitialLerayEnergyCoefficient) ^ 2 *
        (1 + 6 * velocityH3Energy0At u b) := by positivity
  have hC : 0 <
      18 * (3 + h3AuditInitialLerayEnergyCoefficient) ^ 2 := by positivity
  have hScalar := thirdFull_scalar_affineCapHeight_saturation244
    (velocityH3Energy0At u b * (rho ^ 2) ^ 3)
    (12 * (3 + h3AuditInitialLerayEnergyCoefficient) ^ 2 *
      (1 + 6 * velocityH3Energy0At u b))
    (18 * (3 + h3AuditInitialLerayEnergyCoefficient) ^ 2)
    H hA hB hC hH
  simpa only [thirdFullPhysicalAnnularCapClockFactor244,
    thirdFullPhysicalOuterViscousCapSlope244,
    thirdFullPhysicalAnnularClockSaturationCeiling244] using hScalar

/-- For an inner-radius floor rho0>0, the height is uniformly bounded
independently of the actual threshold H and all larger inner radii. -/
theorem thirdFullPhysical_annularClockHeight_le_fixedInnerSaturation244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rho0 rho H : ℝ) (hEnergy : 0 < velocityH3Energy0At u b)
    (hRho0 : 0 < rho0) (hOrder : rho0 ≤ rho) (hH : 0 < H) :
    H / thirdFullPhysicalAnnularCapClockFactor244 u b rho H ≤
      thirdFullPhysicalAnnularClockSaturationCeiling244 u b rho0 := by
  calc
    H / thirdFullPhysicalAnnularCapClockFactor244 u b rho H ≤
        H / thirdFullPhysicalAnnularCapClockFactor244 u b rho0 H :=
      thirdFullPhysical_annularClockHeight_antitone_inner244
        u b H rho0 rho hH hRho0.le hOrder
    _ ≤ thirdFullPhysicalAnnularClockSaturationCeiling244 u b rho0 :=
      thirdFullPhysical_annularClockHeight_le_saturation244
        u b rho0 H hEnergy hRho0 hH.le

/-- A genuinely STRICT physical kinetic-excess margin at one snapshot
forces a positive earlier kinetic anchor. No separate positivity of the
anchor is postulated; the actual physical highpass mass pays the margin. -/
theorem thirdFullPhysical_strictAnnularExcess_forces_anchor_pos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin : ℝ) (hMargin : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) :
    0 < velocityH3Energy0At u b := by
  let M : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  have hSourceNonneg :
      0 ≤ Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 _ _))
  have hProduct : 0 < a * M := by
    change Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤ a * M at hExcess
    linarith only [hExcess, hSourceNonneg, hMargin]
  have hMNonneg : 0 ≤ M := by
    dsimp only [M, thirdFullPhysicalActualSharpKineticHighMass244]
    positivity
  have hMPos : 0 < M := by
    by_contra hNot
    have hZero : M = 0 := le_antisymm (le_of_not_gt hNot) hMNonneg
    rw [hZero, mul_zero] at hProduct
    linarith only [hProduct]
  have hAnchor : M ≤ velocityH3Energy0At u b :=
    thirdFullPhysical_actualSharpHighMass_le_kineticAnchor244
      hH3 hClass b hb x hx rho
  exact lt_of_lt_of_le hMPos hAnchor

/-- A cofinal physical sequence has automatically SUBCRITICAL
terminal-scaled cap heights once its positive inner radii remain above
one fixed cutoff. No finiteness of H3 dissipation is needed. -/
theorem thirdFullPhysical_cofinalClockHeight_autoSubcritical244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T rho0 : ℝ) (hEnergy : 0 < velocityH3Energy0At u b)
    (hRho0 : 0 < rho0)
    (x rho epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k < T)
    (hLimit : Tendsto x atTop (𝓝 T))
    (hRadius : ∀ k : ℕ, rho0 ≤ rho k)
    (hEps : ∀ k : ℕ, 0 < epsilon k) :
    Tendsto (fun k : ℕ =>
      (T - x k) *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (rho k) (epsilon k))) atTop (𝓝 (0 : ℝ)) := by
  let K : ℝ := thirdFullPhysicalAnnularClockSaturationCeiling244 u b rho0
  have hK : 0 < K :=
    thirdFullPhysical_annularClockSaturationCeiling_pos244
      u b rho0 hEnergy hRho0
  have hGap : Tendsto (fun k : ℕ => T - x k) atTop (𝓝 (0 : ℝ)) := by
    have hConstant : Tendsto (fun _ : ℕ => (T : ℝ)) atTop (𝓝 T) :=
      tendsto_const_nhds
    simpa only [sub_self] using hConstant.sub hLimit
  have hUpperLimit : Tendsto (fun k : ℕ => (T - x k) * K)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hGap.mul_const K
  have hLower (k : ℕ) :
      0 ≤ (T - x k) *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (rho k) (epsilon k)) := by
    exact mul_nonneg (sub_nonneg.mpr (hx k).le)
      (div_nonneg (hEps k).le
        (thirdFullPhysical_annularCapClockFactor_pos244
          u b (rho k) (epsilon k)).le)
  have hUpper (k : ℕ) :
      (T - x k) *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (rho k) (epsilon k)) ≤ (T - x k) * K := by
    exact mul_le_mul_of_nonneg_left
      (thirdFullPhysical_annularClockHeight_le_fixedInnerSaturation244
        u b rho0 (rho k) (epsilon k) hEnergy hRho0
        (hRadius k) (hEps k)) (sub_nonneg.mpr (hx k).le)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hUpper) hUpperLimit

/-- In particular, no positive inverse-terminal-time clock-height floor
can persist along a cofinal sequence of positive, bounded-below inner radii.
This obstruction comes from the normalization, not from viscous finiteness. -/
theorem thirdFullPhysical_cofinalClockHeight_noCriticalFloor244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T rho0 : ℝ) (hEnergy : 0 < velocityH3Energy0At u b)
    (hRho0 : 0 < rho0)
    (x rho epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k < T)
    (hLimit : Tendsto x atTop (𝓝 T))
    (hRadius : ∀ k : ℕ, rho0 ≤ rho k)
    (hEps : ∀ k : ℕ, 0 < epsilon k) :
    ¬ ∃ c : ℝ, 0 < c ∧
      (∀ᶠ k : ℕ in atTop,
        c ≤ (T - x k) *
          (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
            u b (rho k) (epsilon k))) := by
  intro ⟨c, hc, hCritical⟩
  have hZero := thirdFullPhysical_cofinalClockHeight_autoSubcritical244
    u b T rho0 hEnergy hRho0 x rho epsilon hx hLimit hRadius hEps
  have hSmall : ∀ᶠ k : ℕ in atTop,
      (T - x k) *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (rho k) (epsilon k)) < c :=
    hZero.eventually (eventually_lt_nhds hc)
  obtain ⟨k, hBig, hTiny⟩ := (hCritical.and hSmall).exists
  exact (not_lt_of_ge hBig) hTiny

/-- Strict physical kinetic excess requires an OUTER radius separated
from the inner cutoff by a factor greater than sqrt(5). The factor five is
forced by the kinetic Laplacian term of the genuine low-band source
ceiling and the highpass kinetic-anchor bound. This is a necessary geometry
constraint, not a newly assumed PDE frequency localization. -/
theorem thirdFullPhysical_strictAnnularExcess_forces_radialSeparation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin : ℝ) (hMargin : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) :
    5 * rho ^ 2 < sigma ^ 2 := by
  let E : ℝ := velocityH3Energy0At u b
  let M : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let S : ℝ := thirdFullPhysicalKineticLowBandSourceCeiling244 rho E
  have hEpos : 0 < E := by
    dsimp only [E]
    exact thirdFullPhysical_strictAnnularExcess_forces_anchor_pos244
      hH3 hClass b hb x hx rho sigma margin hMargin hExcess
  have hE : 0 ≤ E := hEpos.le
  have hSource : rho ^ 2 * Real.sqrt E ≤ S := by
    dsimp only [S, thirdFullPhysicalKineticLowBandSourceCeiling244]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hMul :
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) ≤
        Real.sqrt E * (3 * S) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hSource (by norm_num))
      (Real.sqrt_nonneg E)
  have hIdentity :
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) =
        3 * rho ^ 2 * E := by
    calc
      Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) =
          (Real.sqrt E * Real.sqrt E) * (3 * rho ^ 2) := by ring
      _ = 3 * rho ^ 2 * E := by
        rw [Real.mul_self_sqrt hE]
        ring
  have hSourceLower :
      3 * rho ^ 2 * E ≤ Real.sqrt E * (3 * S) := by
    calc
      3 * rho ^ 2 * E =
          Real.sqrt E * (3 * (rho ^ 2 * Real.sqrt E)) := hIdentity.symm
      _ ≤ Real.sqrt E * (3 * S) := hMul
  have hMCap : M ≤ E := by
    dsimp only [M, E]
    exact thirdFullPhysical_actualSharpHighMass_le_kineticAnchor244
      hH3 hClass b hb x hx rho
  have hA : 0 ≤ (rho ^ 2 + sigma ^ 2) / 2 := by positivity
  have hBound :
      ((rho ^ 2 + sigma ^ 2) / 2) * M ≤
      ((rho ^ 2 + sigma ^ 2) / 2) * E :=
    mul_le_mul_of_nonneg_left hMCap hA
  have hGap :
      3 * rho ^ 2 * E + margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) * E := by
    change Real.sqrt E * (3 * S) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) * M at hExcess
    linarith only [hSourceLower, hExcess, hBound]
  have hSeparatedProduct :
      5 * rho ^ 2 * E + 2 * margin ≤ sigma ^ 2 * E := by
    nlinarith only [hGap]
  have hStrict : 5 * rho ^ 2 * E < sigma ^ 2 * E := by
    linarith only [hSeparatedProduct, hMargin]
  by_contra hNot
  have hReverse : sigma ^ 2 ≤ 5 * rho ^ 2 := le_of_not_gt hNot
  have hScaled : sigma ^ 2 * E ≤ (5 * rho ^ 2) * E :=
    mul_le_mul_of_nonneg_right hReverse hEpos.le
  exact (not_lt_of_ge hScaled) hStrict

/-- A strict annular excess cannot occur at the zero-width diagonal
sigma=rho, regardless of how large the physical H3 state becomes.
The impossibility uses the ACTUAL kinetic source ceiling and genuine highpass. -/
theorem thirdFullPhysical_strictAnnularExcess_noDiagonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho margin : ℝ) (hMargin : 0 < margin) :
    ¬ (Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + rho ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) := by
  intro hExcess
  have hSep := thirdFullPhysical_strictAnnularExcess_forces_radialSeparation244
    hH3 hClass b hb x hx rho rho margin hMargin hExcess
  have hSq : 0 ≤ rho ^ 2 := sq_nonneg rho
  nlinarith only [hSep, hSq]

/-- Consequently the uniform strict-excess hypothesis used by the prior
full rectangular annular-family window and cofinal extraction is EMPTY:
that family always includes the diagonal annulus (rhoMin,rhoMin).
A viable future argument must use separated annuli or selected pairs. -/
theorem thirdFullPhysical_boundedAnnularUniformExcess_impossible244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x radiusMin R margin : ℝ)
    (hx : x ∈ Set.Ioo b T)
    (_hRadiusMin : 0 < radiusMin) (hRadiusMax : radiusMin ≤ R)
    (hMargin : 0 < margin) :
    ¬ (∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) := by
  intro hAll
  exact thirdFullPhysical_strictAnnularExcess_noDiagonal244
    hH3 hClass b hb x hx radiusMin margin hMargin
    (hAll radiusMin radiusMin le_rfl le_rfl hRadiusMax)

/-- In contrast to the impossible full rectangular family, a sequence of
INDIVIDUAL, sufficiently separated genuine physical excess witnesses may be
considered. If it exists with inner radii bounded away from zero, its
optimized cap heights are nevertheless automatically subcritical on the
terminal scale. This conclusion does not require finite H3 dissipation. -/
theorem thirdFullPhysical_cofinalSelectedExcess_autoSubcritical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hLimit : Tendsto x atTop (𝓝 T))
    (rhoFloor : ℝ) (hFloor : 0 < rhoFloor)
    (hRadiusFloor : ∀ k : ℕ, rhoFloor ≤ rho k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244
          hH3 (x k) (rho k)) :
    Tendsto (fun k : ℕ =>
      (T - x k) *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (rho k) (epsilon k))) atTop (𝓝 (0 : ℝ)) := by
  have hEnergy := thirdFullPhysical_strictAnnularExcess_forces_anchor_pos244
    hH3 hClass b hb (x 0) (hx 0) (rho 0) (sigma 0)
    (margin 0) (hMargin 0) (hExcess 0)
  exact thirdFullPhysical_cofinalClockHeight_autoSubcritical244
    u b T rhoFloor hEnergy hFloor x rho epsilon
    (fun k => (hx k).2) hLimit hRadiusFloor hEps

end
end PrimeTensor.FirstMonomialTriad
