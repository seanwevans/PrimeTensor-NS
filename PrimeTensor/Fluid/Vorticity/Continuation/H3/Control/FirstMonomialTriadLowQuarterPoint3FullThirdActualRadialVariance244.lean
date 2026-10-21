import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdReducedMiddleMomentBarrier244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.Moment.Cauchy
import Mathlib.Tactic

/-!
# Actual spectral variance underlying the first physical Fourier Cauchy defect

The previous sharp Young absorption retains the physical first-Cauchy defect
  F₁ = E₀ D₃ - E₂² ≥ 0.
Here this difference is identified with a genuine nonnegative Fourier
variance integral. With `q(ξ) = (2π)² |ξ|²` and nonnegative Fourier mass
`S(ξ)`, we prove the division-free identity

  E₀ F₁ = ∫ (E₀ q(ξ)² - E₂)² S(ξ) dξ.

No spectral positivity, localization, or new integrability hypothesis is
assumed beyond the already established H³ Fourier moment layer. As a
consequence, zero first-Cauchy defect forces almost-everywhere concentration
of every positive Fourier-mass point on one single radial level:

  S(ξ) > 0  ==>  E₀ q(ξ)² = E₂, almost everywhere.

Conversely, failure of that a.e. monochromaticity forces F₁ > 0.
This identifies the geometric obstruction to a strict variance gain.
A quantitative lower bound in time still requires genuine spectral-spread
information and is not claimed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeActualRadialVariance244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceActualRadialVariance244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The pointwise quartic centered-frequency identity before integration. -/
theorem h3_radialVariance_densityExpansion244
    (m0 m2 q S : ℝ) :
    (m0 * q ^ 2 - m2) ^ 2 * S =
      m0 ^ 2 * (q ^ 4 * S) -
        (2 * m0 * m2) * (q ^ 2 * S) + m2 ^ 2 * S := by
  ring

/-- Division-free variance identity for ANY three integrable moments of
an arbitrary nonnegative (or signed) real density. -/
theorem h3_radialVariance_integralIdentity244
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S q : α → ℝ) (m0 m2 m4 : ℝ)
    (h0Int : Integrable S μ)
    (h2Int : Integrable (fun ξ => q ξ ^ 2 * S ξ) μ)
    (h4Int : Integrable (fun ξ => q ξ ^ 4 * S ξ) μ)
    (h0 : (∫ ξ, S ξ ∂μ) = m0)
    (h2 : (∫ ξ, q ξ ^ 2 * S ξ ∂μ) = m2)
    (h4 : (∫ ξ, q ξ ^ 4 * S ξ ∂μ) = m4) :
    (∫ ξ, (m0 * q ξ ^ 2 - m2) ^ 2 * S ξ ∂μ) =
      m0 * (m0 * m4 - m2 ^ 2) := by
  have hExpand (ξ : α) :
      (m0 * q ξ ^ 2 - m2) ^ 2 * S ξ =
        m0 ^ 2 * (q ξ ^ 4 * S ξ) -
          (2 * m0 * m2) * (q ξ ^ 2 * S ξ) + m2 ^ 2 * S ξ :=
    h3_radialVariance_densityExpansion244 m0 m2 (q ξ) (S ξ)
  have hLeftInt : Integrable
      (fun ξ => m0 ^ 2 * (q ξ ^ 4 * S ξ) -
        (2 * m0 * m2) * (q ξ ^ 2 * S ξ)) μ :=
    (h4Int.const_mul _).sub (h2Int.const_mul _)
  calc
    (∫ ξ, (m0 * q ξ ^ 2 - m2) ^ 2 * S ξ ∂μ) =
        ∫ ξ, m0 ^ 2 * (q ξ ^ 4 * S ξ) -
          (2 * m0 * m2) * (q ξ ^ 2 * S ξ) + m2 ^ 2 * S ξ ∂μ := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact hExpand ξ
    _ = m0 ^ 2 * (∫ ξ, q ξ ^ 4 * S ξ ∂μ) -
          (2 * m0 * m2) * (∫ ξ, q ξ ^ 2 * S ξ ∂μ) +
          m2 ^ 2 * (∫ ξ, S ξ ∂μ) := by
      rw [MeasureTheory.integral_add hLeftInt (h0Int.const_mul _),
        MeasureTheory.integral_sub (h4Int.const_mul _) (h2Int.const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul]
    _ = m0 * (m0 * m4 - m2 ^ 2) := by rw [h0, h2, h4]; ring

/-- The first physical Fourier Cauchy defect is literally the unnormalized
variance of the squared frequency weight under the actual Fourier mass.
The extra `E₀` factor permits a division-free statement even at zero mass. -/
theorem h3Path_topFourier_firstCauchyDefect_radialVariance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    (∫ ξ : H3FourierPoint3,
        (velocityH3Energy0At u t * h3FourierGradientSquare ξ ^ 2 -
          velocityH3Energy2At u t) ^ 2 *
          velocityH3FourierMassDensityAt u t
            (hH3.velocity_h3_integrable t
              ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
            (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
              hH3.navier_stokes
              ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
          ξ ∂volume) =
      velocityH3Energy0At u t * h3PathTopFourierFirstCauchyDefect244 u t := by
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
  have h2Int : Integrable (fun ξ => q ξ ^ 2 * S ξ) volume := by
    dsimp only [q, S]
    exact velocityH3FourierSecondAggregateDensity_integrable
      hInt hMeas hFourier
  have h4Int : Integrable (fun ξ => q ξ ^ 4 * S ξ) volume := by
    dsimp only [q, S]
    exact h3Path_velocityH3FourierFourthAggregateDensity_integrable
      hH3 hClass ht hInt hMeas hFourier
  have h0 : (∫ ξ, S ξ ∂volume) = velocityH3Energy0At u t := by
    calc
      _ = velocityH3FourierZerothRadialMomentAt u t hInt hMeas :=
        (velocityH3FourierZerothRadialMomentAt_eq_integral_massDensity
          hInt hMeas).symm
      _ = velocityH3Energy0At u t :=
        (velocityH3Energy0At_eq_fourierZerothRadialMoment hInt hMeas).symm
  have h2 : (∫ ξ, q ξ ^ 2 * S ξ ∂volume) =
      velocityH3Energy2At u t := by
    calc
      _ = velocityH3FourierSecondRadialMomentAt u t hInt hMeas :=
        (velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
          hInt hMeas hFourier).symm
      _ = velocityH3Energy2At u t :=
        (velocityH3Energy2At_eq_fourierSecondRadialMoment
          hInt hMeas hFourier).symm
  have h4 : (∫ ξ, q ξ ^ 4 * S ξ ∂volume) =
      velocityH3Dissipation3At u t := by
    calc
      _ = velocityH3FourierFourthRadialMomentAt u t hInt hMeas :=
        (h3Path_velocityH3FourierFourthRadialMomentAt_eq_integral_massDensity
          hH3 hClass ht hInt hMeas hFourier).symm
      _ = velocityH3Dissipation3At u t :=
        (velocityH3Dissipation3At_eq_fourierFourthRadialMoment
          hH3 hClass ht hInt hMeas hFourier).symm
  have hIdentity := h3_radialVariance_integralIdentity244
    (μ := (volume : Measure H3FourierPoint3)) S q
    (velocityH3Energy0At u t) (velocityH3Energy2At u t)
    (velocityH3Dissipation3At u t)
    h0Int h2Int h4Int h0 h2 h4
  dsimp only [S, q] at hIdentity
  unfold h3PathTopFourierFirstCauchyDefect244
  simpa only [hInt, hMeas] using hIdentity

/-- Zero nonnegative variance forces the squared frequency to equal its
energy-weighted mean wherever the Fourier mass is positive, a.e. -/
theorem h3_radialVariance_zero_forces_monochromatic_ae244
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S q : α → ℝ) (m0 m2 : ℝ)
    (hS : ∀ ξ, 0 ≤ S ξ)
    (hInt : Integrable
      (fun ξ => (m0 * q ξ ^ 2 - m2) ^ 2 * S ξ) μ)
    (hZero : (∫ ξ, (m0 * q ξ ^ 2 - m2) ^ 2 * S ξ ∂μ) = 0) :
    ∀ᵐ ξ ∂μ, 0 < S ξ → m0 * q ξ ^ 2 = m2 := by
  have hNonneg : 0 ≤
      (fun ξ => (m0 * q ξ ^ 2 - m2) ^ 2 * S ξ) := by
    intro ξ
    exact mul_nonneg (sq_nonneg _) (hS ξ)
  have hAE := (integral_eq_zero_iff_of_nonneg hNonneg hInt).mp hZero
  filter_upwards [hAE] with ξ hz hPositive
  have hSq : (m0 * q ξ ^ 2 - m2) ^ 2 = 0 :=
    (mul_eq_zero.mp hz).resolve_right (ne_of_gt hPositive)
  nlinarith only [hSq]

/-- Physical zero variance implies radial single-level Fourier support,
with no assumption that individual Fourier transforms are continuous. -/
theorem h3Path_topFourier_firstCauchyZero_monochromatic_ae244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hZero : h3PathTopFourierFirstCauchyDefect244 u t = 0) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes htAbs
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      0 < velocityH3FourierMassDensityAt u t hInt hMeas ξ →
        velocityH3Energy0At u t * h3FourierGradientSquare ξ ^ 2 =
          velocityH3Energy2At u t := by
  dsimp only
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
  have hS : ∀ ξ, 0 ≤ S ξ := by
    intro ξ
    exact velocityH3FourierMassDensityAt_nonneg u t hInt hMeas ξ
  have h0Int : Integrable S volume := by
    dsimp only [S]
    exact velocityH3FourierMassDensityAt_integrable u t hInt hMeas
  have h2Int : Integrable (fun ξ => q ξ ^ 2 * S ξ) volume := by
    dsimp only [q, S]
    exact velocityH3FourierSecondAggregateDensity_integrable
      hInt hMeas hFourier
  have h4Int : Integrable (fun ξ => q ξ ^ 4 * S ξ) volume := by
    dsimp only [q, S]
    exact h3Path_velocityH3FourierFourthAggregateDensity_integrable
      hH3 hClass ht hInt hMeas hFourier
  have hExpand :
      (fun ξ => (velocityH3Energy0At u t * q ξ ^ 2 -
        velocityH3Energy2At u t) ^ 2 * S ξ) =
      (fun ξ => velocityH3Energy0At u t ^ 2 * (q ξ ^ 4 * S ξ) -
        (2 * velocityH3Energy0At u t * velocityH3Energy2At u t) *
          (q ξ ^ 2 * S ξ) + velocityH3Energy2At u t ^ 2 * S ξ) := by
    funext ξ
    exact h3_radialVariance_densityExpansion244
      (velocityH3Energy0At u t) (velocityH3Energy2At u t) (q ξ) (S ξ)
  have hCenteredInt : Integrable
      (fun ξ => (velocityH3Energy0At u t * q ξ ^ 2 -
        velocityH3Energy2At u t) ^ 2 * S ξ) volume := by
    rw [hExpand]
    exact ((h4Int.const_mul _).sub (h2Int.const_mul _)).add
      (h0Int.const_mul _)
  have hVar := h3Path_topFourier_firstCauchyDefect_radialVariance244
    hH3 hClass ht
  rw [hZero, mul_zero] at hVar
  have hMono := h3_radialVariance_zero_forces_monochromatic_ae244
    (volume : Measure H3FourierPoint3) S q
    (velocityH3Energy0At u t) (velocityH3Energy2At u t)
    hS hCenteredInt (by simpa only [S, q, hInt, hMeas] using hVar)
  simpa only [S, q, hInt, hMeas] using hMono


/-- A spectral mass distribution that is not a.e. concentrated on its
energy-weighted squared-frequency level has STRICTLY positive first
physical Cauchy defect. This is the contrapositive of the variance identity,
not a uniform-in-time dispersion estimate. -/
theorem h3Path_topFourier_nonmonochromatic_forces_positiveVariance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hSpread : ¬ (
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let hInt : VelocityH3IntegrableAt u t :=
        hH3.velocity_h3_integrable t htAbs
      let hMeas : VelocityH3MeasurableAt u t :=
        velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes htAbs
      ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
        0 < velocityH3FourierMassDensityAt u t hInt hMeas ξ →
          velocityH3Energy0At u t * h3FourierGradientSquare ξ ^ 2 =
            velocityH3Energy2At u t)) :
    0 < h3PathTopFourierFirstCauchyDefect244 u t := by
  have hNonneg : 0 ≤ h3PathTopFourierFirstCauchyDefect244 u t :=
    (h3Path_topFourier_twoCauchyDefects_nonneg244
      hH3 hClass ht).1
  by_contra hNotPos
  have hZero : h3PathTopFourierFirstCauchyDefect244 u t = 0 :=
    le_antisymm (le_of_not_gt hNotPos) hNonneg
  exact hSpread (h3Path_topFourier_firstCauchyZero_monochromatic_ae244
    hH3 hClass ht hZero)

/-- Failure of monochromatic Fourier support gives an actual strict
improvement of the formerly optimal 27/256 physical Young ceiling,
provided the Landau coefficient and top dissipation are positive. -/
theorem h3Path_topFourier_strictYoung_of_nonmonochromatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hSpread : ¬ (
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let hInt : VelocityH3IntegrableAt u t :=
        hH3.velocity_h3_integrable t htAbs
      let hMeas : VelocityH3MeasurableAt u t :=
        velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes htAbs
      ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
        0 < velocityH3FourierMassDensityAt u t hInt hMeas ξ →
          velocityH3Energy0At u t * h3FourierGradientSquare ξ ^ 2 =
            velocityH3Energy2At u t)) :
    K * velocityH3Energy3At u t <
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
  exact h3Path_topFourier_strictYoung_of_firstVariance244
    hH3 hClass ht hK hD
    (h3Path_topFourier_nonmonochromatic_forces_positiveVariance244
      hH3 hClass ht hSpread)

end
end PrimeTensor.FirstMonomialTriad
