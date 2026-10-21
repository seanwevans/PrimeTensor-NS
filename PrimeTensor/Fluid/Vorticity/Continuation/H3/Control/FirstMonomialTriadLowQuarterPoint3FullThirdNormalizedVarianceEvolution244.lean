import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedFourierMomentRigidity244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Zero.Energy.Derivative.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Energy.Derivative.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.TopDissipation
import Mathlib.Tactic

/-!
# Physical time evolution of normalized Fourier variance

The exact dimensionless variance R = 1 - E₂²/(E₀ D₃) has a genuine
preterminal time derivative. The repository ALREADY supplies derivatives
of E₀ and E₂ from the physical selected/old energy evolution and of
D₃ from its fourth-radial Fourier Hilbert L² realization. No further
regularity or formal differentiability hypothesis is added to the
physical statement.

The signed source for the evolution is

    N = E₂² (E₀' D₃ + E₀ D₃') - 2 E₂ E₂' E₀ D₃,
    R' = N / (E₀ D₃)².

Thus strictly decreasing dimensionless variance requires the signed
middle-moment growth to dominate the kinetic/top-dissipation product
rate. This is an exact PDE-linked obstruction, NOT a sign estimate for N,
not an anti-concentration theorem, and not unconditional continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

/-- The normalized variance along the genuine class-local fourth-radial
Hilbert path, which agrees with the original physical ratio at all strict
times. Outside the class interval this definition has no interpretation
as the original physical moment ratio. -/
noncomputable def h3PathTopFourierNormalizedVarianceOnClass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hClass : PreterminalH3EnergyClass u a T)
    (s : ℝ) : ℝ :=
  1 - velocityH3Energy2At u s ^ 2 /
    (velocityH3Energy0At u s *
      h3TerminalPhysicalTopDissipation3Path hClass s)

/-- The already-closed strong Hilbert derivative of fourth-radial top
dissipation, named as one scalar source of normalized spectral dynamics. -/
noncomputable def h3PathTopFourierFourthRadialPairingRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) : ℝ :=
  ∑ j : Fin 3,
    2 * inner ℝ
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j t)
      (deriv
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j) t)

/-- Universal exact derivative of the relative Cauchy variance.
All three time derivatives are explicit, and the only denominator
hypothesis is its nonvanishing at the differentiation point. -/
theorem h3_normalizedFourierVariance_hasDerivAt244
    (E0 E2 D : ℝ → ℝ) (t e0 e2 d : ℝ)
    (h0 : HasDerivAt E0 e0 t)
    (h2 : HasDerivAt E2 e2 t)
    (hD : HasDerivAt D d t)
    (hDen : E0 t * D t ≠ 0) :
    HasDerivAt
      (fun s : ℝ => 1 - E2 s ^ 2 / (E0 s * D s))
      ((E2 t ^ 2 * (e0 * D t + E0 t * d) -
        2 * E2 t * e2 * (E0 t * D t)) /
          (E0 t * D t) ^ 2) t := by
  have hSq : HasDerivAt (fun s : ℝ => E2 s ^ 2)
      (2 * E2 t * e2) t := by
    -- `HasDerivAt.pow` produces the pointwise Pi-power `E2 ^ 2`.
    -- Unfold that function operation explicitly before using the result.
    have hPow := h2.pow 2
    rw [Pi.pow_def] at hPow
    have hCoeff :
        (2 : ℝ) * E2 t ^ (2 - 1) * e2 = 2 * E2 t * e2 := by
      norm_num
    exact hPow.congr_deriv hCoeff
  have hProd : HasDerivAt (fun s : ℝ => E0 s * D s)
      (e0 * D t + E0 t * d) t :=
    h0.mul hD
  have hQuot := hSq.div hProd hDen
  have hSub := (hasDerivAt_const t (1 : ℝ)).sub hQuot
  have hCoefficient :
      (0 : ℝ) -
          ((2 * E2 t * e2 * (E0 t * D t) -
            E2 t ^ 2 * (e0 * D t + E0 t * d)) /
            (E0 t * D t) ^ 2) =
        (E2 t ^ 2 * (e0 * D t + E0 t * d) -
          2 * E2 t * e2 * (E0 t * D t)) /
          (E0 t * D t) ^ 2 := by
    ring
  exact hSub.congr_deriv hCoefficient

/-- At strict times the class-local scalar is EXACTLY the actual physical
normalized Fourier Cauchy defect. In particular the differentiated object
is not a newly assumed surrogate for physical Fourier variance. -/
theorem h3Path_normalizedVarianceOnClass_eq_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierNormalizedVarianceOnClass244 hClass t =
      h3PathTopFourierNormalizedRadialVariance244 u t := by
  have hSum := h3Path_topFourier_normalizedVariance_add_middle_eq_one244
    hMass hD
  have hTop := h3TerminalPhysicalTopDissipation3Path_eq hClass ht
  unfold h3PathTopFourierNormalizedVarianceOnClass244
  rw [hTop]
  unfold h3PathTopFourierNormalizedMiddleMoment244 at hSum
  linarith only [hSum]

/-- Genuine PDE-linked derivative of the dimensionless Fourier variance.
Its top-dissipation contribution is the already-proved physical Hilbert
pairing of fourth-radial spectral states with their time derivatives. -/
theorem h3Path_normalizedVarianceOnClass_hasDerivAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    HasDerivAt (h3PathTopFourierNormalizedVarianceOnClass244 hClass)
      ((velocityH3Energy2At u t ^ 2 *
          (velocityH3FormalDerivative0At u t *
              h3TerminalPhysicalTopDissipation3Path hClass t +
            velocityH3Energy0At u t *
              h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t) -
          2 * velocityH3Energy2At u t *
            velocityH3FormalDerivative2At u t *
            (velocityH3Energy0At u t *
              h3TerminalPhysicalTopDissipation3Path hClass t)) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2) t := by
  have hZero := h3PathEnergyClassProducesOrder0EnergyDerivativeIdentity_closed
    hH3 hClass ht
  have hTwo := h3PathEnergyClassProducesOrder2EnergyDerivativeIdentity_closed
    hH3 hClass ht
  have hTop := h3TerminalPhysicalTopDissipation3Path_hasDerivAt
    hH3 hClass ht
  have hRate : HasDerivAt
      (h3TerminalPhysicalTopDissipation3Path hClass)
      (h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t) t := by
    exact hTop
  have hTopVal := h3TerminalPhysicalTopDissipation3Path_eq hClass ht
  have hDen : velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t ≠ 0 := by
    rw [hTopVal]
    exact ne_of_gt (mul_pos hMass hD)
  exact h3_normalizedFourierVariance_hasDerivAt244
    (velocityH3Energy0At u) (velocityH3Energy2At u)
    (h3TerminalPhysicalTopDissipation3Path hClass) t
    (velocityH3FormalDerivative0At u t)
    (velocityH3FormalDerivative2At u t)
    (h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t)
    hZero hTwo hRate hDen

/-- Exact ordinary derivative of normalized Fourier variance in terms of
physical kinetic/order-two energy rates and the fourth-radial pairing. -/
theorem h3Path_normalizedVarianceOnClass_deriv_eq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass) t =
      ((velocityH3Energy2At u t ^ 2 *
          (velocityH3FormalDerivative0At u t *
              h3TerminalPhysicalTopDissipation3Path hClass t +
            velocityH3Energy0At u t *
              h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t) -
          2 * velocityH3Energy2At u t *
            velocityH3FormalDerivative2At u t *
            (velocityH3Energy0At u t *
              h3TerminalPhysicalTopDissipation3Path hClass t)) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2) :=
  (h3Path_normalizedVarianceOnClass_hasDerivAt244
    hH3 hClass ht hMass hD).deriv

/-- A locally strictly shrinking relative Fourier variance necessarily
requires positive signed excess middle-moment production over kinetic
and fourth-radial dissipation product growth. This is a rigorously proved
orientation criterion, NOT a statement that such excess occurs. -/
theorem h3Path_normalizedVariance_decrease_forces_middleMomentExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hDecreasing :
      deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass) t < 0) :
    velocityH3Energy2At u t ^ 2 *
        (velocityH3FormalDerivative0At u t *
            h3TerminalPhysicalTopDissipation3Path hClass t +
          velocityH3Energy0At u t *
            h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t) <
      2 * velocityH3Energy2At u t *
        velocityH3FormalDerivative2At u t *
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) := by
  have hTopVal := h3TerminalPhysicalTopDissipation3Path_eq hClass ht
  have hDen : 0 < (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 := by
    rw [hTopVal]
    exact pow_pos (mul_pos hMass hD) 2
  rw [h3Path_normalizedVarianceOnClass_deriv_eq244
    hH3 hClass ht hMass hD] at hDecreasing
  have hNumer := (div_lt_iff₀ hDen).mp hDecreasing
  simp only [zero_mul] at hNumer
  linarith only [hNumer]

end
end PrimeTensor.FirstMonomialTriad
