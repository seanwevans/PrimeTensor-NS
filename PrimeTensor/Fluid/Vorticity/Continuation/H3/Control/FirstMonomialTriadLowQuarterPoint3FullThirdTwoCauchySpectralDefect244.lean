import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSharpTopFourierYoungRigidity244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSecondOrderKineticAbsorption
import Mathlib.Tactic

/-!
# Separate the two physical Fourier Cauchy defects in sharp H³ Young rigidity

The moment interpolation M₃⁴ ≤ M₀ M₄³ was obtained from TWO Cauchy steps:

  M₂² ≤ M₀ M₄,     M₃² ≤ M₂ M₄.

Rather than treating their combination as one opaque inequality, this
module keeps the two nonnegative deficits separately:

  M₀ M₄³ - M₃⁴
    = (M₀ M₄ - M₂²) M₄²
       + (M₂ M₄ - M₃²)(M₂ M₄ + M₃²).

We identify each term with an ACTUAL H³ Fourier energy/dissipation block,
then feed the identity into the already-proved optimal 27/256 Young defect.
Near saturation requires BOTH middle-moment Cauchy deficits and the spectral
frequency mismatch to be small in the corresponding weighted senses.

This does not assert a uniform positive spectral dispersion gap: the frequency
measure can concentrate in thin shells, so a quantitative PDE dynamical input
remains necessary for continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- First Fourier Cauchy defect `M₀ M₄ - M₂²`, expressed entirely in
actual physical energies. -/
noncomputable def h3PathTopFourierFirstCauchyDefect244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  velocityH3Energy0At u t * velocityH3Dissipation3At u t -
    velocityH3Energy2At u t ^ 2

/-- Second Fourier Cauchy defect `M₂ M₄ - M₃²`, in the original physical
energy/dissipation variables. -/
noncomputable def h3PathTopFourierSecondCauchyDefect244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  velocityH3Energy2At u t * velocityH3Dissipation3At u t -
    velocityH3Energy3At u t ^ 2

/-- The SECOND moment Cauchy step transported to physical H³ energies;
its middle `E₂` has not been eliminated by an inequality. -/
theorem h3Path_topFourier_secondCauchy_le244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Energy3At u t ^ 2 ≤
      velocityH3Energy2At u t * velocityH3Dissipation3At u t := by
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
  have hMoment :=
    velocityH3FourierThirdRadialMomentAt_sq_le_second_mul_fourth
      hH3 hClass ht hInt hMeas hFourier
  have h2 := velocityH3Energy2At_eq_fourierSecondRadialMoment
    hInt hMeas hFourier
  have h3 := velocityH3Energy3At_eq_fourierThirdRadialMoment
    hInt hMeas hFourier
  have h4 := velocityH3Dissipation3At_eq_fourierFourthRadialMoment
    hH3 hClass ht hInt hMeas hFourier
  rw [h3, h2, h4]
  exact hMoment

/-- Both genuinely physical Cauchy defects are nonnegative on every
strict admissible H³ energy-class time slice. -/
theorem h3Path_topFourier_twoCauchyDefects_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0 ≤ h3PathTopFourierFirstCauchyDefect244 u t ∧
      0 ≤ h3PathTopFourierSecondCauchyDefect244 u t := by
  constructor
  · unfold h3PathTopFourierFirstCauchyDefect244
    exact sub_nonneg.mpr
      (h3PathCanonical_secondEnergy_sq_le_kinetic_mul_topDissipation
        hH3 hClass ht)
  · unfold h3PathTopFourierSecondCauchyDefect244
    exact sub_nonneg.mpr
      (h3Path_topFourier_secondCauchy_le244 hH3 hClass ht)

/-- Division-free two-step Cauchy defect identity; it works for arbitrary
real moments, before any Navier–Stokes hypotheses are introduced. -/
theorem h3_twoCauchy_fourthMoment_exactDefect244
    (m0 m2 m3 m4 : ℝ) :
    m0 * m4 ^ 3 - m3 ^ 4 =
      (m0 * m4 - m2 ^ 2) * m4 ^ 2 +
        (m2 * m4 - m3 ^ 2) * (m2 * m4 + m3 ^ 2) := by
  ring

/-- Exact physical fourth-moment deficit decomposition into its two
separate Cauchy inequalities, not just their product bound. -/
theorem h3Path_topFourier_fourthMoment_exactTwoCauchy244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    velocityH3Energy0At u t * velocityH3Dissipation3At u t ^ 3 -
        velocityH3Energy3At u t ^ 4 =
      h3PathTopFourierFirstCauchyDefect244 u t *
          velocityH3Dissipation3At u t ^ 2 +
        h3PathTopFourierSecondCauchyDefect244 u t *
          (velocityH3Energy2At u t * velocityH3Dissipation3At u t +
            velocityH3Energy3At u t ^ 2) := by
  unfold h3PathTopFourierFirstCauchyDefect244
    h3PathTopFourierSecondCauchyDefect244
  ring

/-- Sharp physical Young deficit with THREE explicitly nonnegative
components: each of the two Fourier Cauchy gaps plus the mismatch square.
Unlike a bare coefficient improvement, this records which radial-moment
geometry is needed for near-saturation of the actual H³ absorption. -/
theorem h3Path_sharpTopYoung_exactTwoCauchyDefect244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t K : ℝ) :
    256 * velocityH3Dissipation3At u t ^ 3 *
        (velocityH3Dissipation3At u t +
          (27 / 256 : ℝ) * (K ^ 4 * velocityH3Energy0At u t) -
          K * velocityH3Energy3At u t) =
      27 * K ^ 4 *
        (h3PathTopFourierFirstCauchyDefect244 u t *
          velocityH3Dissipation3At u t ^ 2 +
         h3PathTopFourierSecondCauchyDefect244 u t *
          (velocityH3Energy2At u t * velocityH3Dissipation3At u t +
            velocityH3Energy3At u t ^ 2)) +
      (3 * (K * velocityH3Energy3At u t) -
        4 * velocityH3Dissipation3At u t) ^ 2 *
        (3 * (K * velocityH3Energy3At u t) ^ 2 +
          8 * (K * velocityH3Energy3At u t) * velocityH3Dissipation3At u t +
          16 * velocityH3Dissipation3At u t ^ 2) := by
  unfold h3PathTopFourierFirstCauchyDefect244
    h3PathTopFourierSecondCauchyDefect244
  ring

/-- A nonnegative quantitative Young deficit dominates the first Cauchy
gap, weighted by the square of the physical top-order dissipation. -/
theorem h3Path_sharpTopYoung_firstCauchy_le_gap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (hK : 0 ≤ K) :
    27 * K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t *
        velocityH3Dissipation3At u t ^ 2 ≤
      256 * velocityH3Dissipation3At u t ^ 3 *
        (velocityH3Dissipation3At u t +
          (27 / 256 : ℝ) * (K ^ 4 * velocityH3Energy0At u t) -
          K * velocityH3Energy3At u t) := by
  have hCS := h3Path_topFourier_twoCauchyDefects_nonneg244
    hH3 hClass ht
  have hD : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hFirst : 0 ≤ h3PathTopFourierFirstCauchyDefect244 u t := hCS.1
  have hSecond : 0 ≤ h3PathTopFourierSecondCauchyDefect244 u t := hCS.2
  have hOther : 0 ≤ 27 * K ^ 4 *
      (h3PathTopFourierSecondCauchyDefect244 u t *
        (velocityH3Energy2At u t * velocityH3Dissipation3At u t +
          velocityH3Energy3At u t ^ 2)) := by
    positivity
  have hMismatch : 0 ≤
      (3 * (K * velocityH3Energy3At u t) -
        4 * velocityH3Dissipation3At u t) ^ 2 *
        (3 * (K * velocityH3Energy3At u t) ^ 2 +
          8 * (K * velocityH3Energy3At u t) * velocityH3Dissipation3At u t +
          16 * velocityH3Dissipation3At u t ^ 2) := by
    have hE3 : 0 ≤ velocityH3Energy3At u t :=
      velocityH3Energy3At_nonneg u t
    positivity
  have hExact := h3Path_sharpTopYoung_exactTwoCauchyDefect244 u t K
  linarith only [hExact, hOther, hMismatch]

/-- Even with exact cancellation of the first Cauchy defect, the second
weighted Fourier Cauchy deficit remains an independent obstruction to
sharp Young saturation. -/
theorem h3Path_sharpTopYoung_secondCauchy_le_gap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (hK : 0 ≤ K) :
    27 * K ^ 4 * h3PathTopFourierSecondCauchyDefect244 u t *
        (velocityH3Energy2At u t * velocityH3Dissipation3At u t +
          velocityH3Energy3At u t ^ 2) ≤
      256 * velocityH3Dissipation3At u t ^ 3 *
        (velocityH3Dissipation3At u t +
          (27 / 256 : ℝ) * (K ^ 4 * velocityH3Energy0At u t) -
          K * velocityH3Energy3At u t) := by
  have hCS := h3Path_topFourier_twoCauchyDefects_nonneg244
    hH3 hClass ht
  have hD : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hFirst : 0 ≤ h3PathTopFourierFirstCauchyDefect244 u t := hCS.1
  have hSecond : 0 ≤ h3PathTopFourierSecondCauchyDefect244 u t := hCS.2
  have hOther : 0 ≤ 27 * K ^ 4 *
      h3PathTopFourierFirstCauchyDefect244 u t *
        velocityH3Dissipation3At u t ^ 2 := by
    positivity
  have hMismatch : 0 ≤
      (3 * (K * velocityH3Energy3At u t) -
        4 * velocityH3Dissipation3At u t) ^ 2 *
        (3 * (K * velocityH3Energy3At u t) ^ 2 +
          8 * (K * velocityH3Energy3At u t) * velocityH3Dissipation3At u t +
          16 * velocityH3Dissipation3At u t ^ 2) := by
    have hE3 : 0 ≤ velocityH3Energy3At u t :=
      velocityH3Energy3At_nonneg u t
    positivity
  have hExact := h3Path_sharpTopYoung_exactTwoCauchyDefect244 u t K
  linarith only [hExact, hOther, hMismatch]


/-- If the physical fourth-power moment interpolation is exactly saturated
at a time with positive third-order energy and dissipation, EACH of its two
underlying Cauchy inequalities must be saturated. This identifies the
intermediate E₂ moment that was discarded in the earlier proof. -/
theorem h3Path_topFourier_momentEquality_twoCauchyRigidity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hE3 : 0 < velocityH3Energy3At u t)
    (hSat : velocityH3Energy0At u t * velocityH3Dissipation3At u t ^ 3 =
      velocityH3Energy3At u t ^ 4) :
    h3PathTopFourierFirstCauchyDefect244 u t = 0 ∧
      h3PathTopFourierSecondCauchyDefect244 u t = 0 := by
  have hCS := h3Path_topFourier_twoCauchyDefects_nonneg244
    hH3 hClass ht
  have hId := h3Path_topFourier_fourthMoment_exactTwoCauchy244 u t
  rw [show velocityH3Energy0At u t * velocityH3Dissipation3At u t ^ 3 -
      velocityH3Energy3At u t ^ 4 = 0 by linarith only [hSat]] at hId
  have hWeight1 : 0 < velocityH3Dissipation3At u t ^ 2 :=
    pow_pos hD 2
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hWeight2 : 0 <
      velocityH3Energy2At u t * velocityH3Dissipation3At u t +
        velocityH3Energy3At u t ^ 2 := by
    have hDprod : 0 ≤ velocityH3Energy2At u t *
        velocityH3Dissipation3At u t := mul_nonneg hE2 hD.le
    have hE3sq : 0 < velocityH3Energy3At u t ^ 2 := pow_pos hE3 2
    linarith only [hDprod, hE3sq]
  have hTerm1 : 0 ≤ h3PathTopFourierFirstCauchyDefect244 u t *
      velocityH3Dissipation3At u t ^ 2 :=
    mul_nonneg hCS.1 hWeight1.le
  have hTerm2 : 0 ≤ h3PathTopFourierSecondCauchyDefect244 u t *
      (velocityH3Energy2At u t * velocityH3Dissipation3At u t +
        velocityH3Energy3At u t ^ 2) :=
    mul_nonneg hCS.2 hWeight2.le
  have hZero1 : h3PathTopFourierFirstCauchyDefect244 u t *
      velocityH3Dissipation3At u t ^ 2 = 0 := by
    linarith only [hId, hTerm1, hTerm2]
  have hZero2 : h3PathTopFourierSecondCauchyDefect244 u t *
      (velocityH3Energy2At u t * velocityH3Dissipation3At u t +
        velocityH3Energy3At u t ^ 2) = 0 := by
    linarith only [hId, hTerm1, hTerm2]
  exact ⟨(mul_eq_zero.mp hZero1).resolve_right (ne_of_gt hWeight1),
    (mul_eq_zero.mp hZero2).resolve_right (ne_of_gt hWeight2)⟩

end
end PrimeTensor.FirstMonomialTriad
