import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedCubicRadialSynchronization244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Dissipative
import Mathlib.Tactic

/-!
# Rapid negative physical H³ energy slopes and simultaneous dissipative escape

The fixed no-kinetic-trace signed corridor has one remaining arm: an arbitrarily
negative logarithmic derivative of the physical H³ energy. Such a negative
slope need not force large H³ energy: strong dissipation may instead be
concentrated in a tiny high-frequency tail. We retain this distinction.

The exact physical PDE identity `E' + 2D = -T` and the existing whole-H³
commutator estimate `|T| <= 4422 * (1 + C₁ sqrt E) * E` imply that a very
negative slope forces either a large *physical* dissipation/energy ratio or
high physical H³ energy. The second arm can be converted, using the already
proved kinetic-anchored radial selection estimate, into high-radial spectral
energy dominance and a simultaneous physical dissipation clock.

We first choose the required slope threshold, and THEN choose a cofinal
physical time. Consequently all conclusions hold on the SAME selected
sequence; no intersection of independent cofinal sets is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The square-root H³ energy threshold that pays for the kinetic-anchored
low-radial spectral ceiling at radius `R`. -/
noncomputable def h3PathFastDecayRadialRootRequest244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b R : ℝ) : ℝ :=
  (R + 2) * (h3TerminalRadialSobolevWeightSquareCeiling R *
    velocityH3Energy0At u b + 2) + 1

/-- Physical logarithmic negative-slope threshold ensuring that either
`D > R E` or the radial energy request is satisfied at the SAME instant. -/
noncomputable def h3PathFastDecaySlopeThreshold244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b R : ℝ) : ℝ :=
  2 * R + 4422 * (1 +
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      h3PathFastDecayRadialRootRequest244 u b R)

/-- Elementary signed-balance dichotomy. Large negative energy slope can be
paid either by viscous dissipation or by a large positive transport term;
when the latter is bounded by its square-root H³ estimate, the energy root
must exceed the requested cutoff. -/
theorem h3Path_fastSlope_largeDissipation_or_largeEnergyRoot244
    (E D F W R K Q : ℝ)
    (hE : 0 < E) (hK : 0 ≤ K)
    (hBalance : F + 2 * D = -W)
    (hTransport : W ≤ (4422 + K * Real.sqrt E) * E)
    (hFast : (2 * R + 4422 + K * Q) * E < -F) :
    R * E < D ∨ Q ≤ Real.sqrt E := by
  by_cases hRoot : Q ≤ Real.sqrt E
  · exact Or.inr hRoot
  · left
    have hSmall : Real.sqrt E ≤ Q := le_of_lt (lt_of_not_ge hRoot)
    have hCoeff : 4422 + K * Real.sqrt E ≤ 4422 + K * Q := by
      have hMul := mul_le_mul_of_nonneg_left hSmall hK
      linarith only [hMul]
    have hBound : W ≤ (4422 + K * Q) * E :=
      le_trans hTransport (mul_le_mul_of_nonneg_right hCoeff hE.le)
    have hExpand : (2 * R + 4422 + K * Q) * E =
        2 * (R * E) + (4422 + K * Q) * E := by ring
    rw [hExpand] at hFast
    linarith only [hBalance, hBound, hFast]

/-- The exact physical transport plus its *two-sided* commutator estimate.
Unlike the one-sided growth inequality, this controls large negative H³
energy slopes when full viscosity is retained. -/
theorem h3Path_physicalFullTransport_abs_le_sqrtEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |velocityH3TransportDerivativeAt u t| ≤
      4422 * (1 +
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3EnergyAt u t := by
  have hRaw :=
    (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass
      (fun s hs => h3PathCanonicalSqrtEnergyGradientEnvelope_at
        hH3 hClass hs) t ht).2
  have hProd : 0 ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  change |velocityH3TransportDerivativeAt u t| ≤
    4422 * (1 + |h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)|) *
      velocityH3EnergyAt u t at hRaw
  rw [abs_of_nonneg hProd] at hRaw
  exact hRaw

/-- In a fixed physical fast-decay snapshot, choose the negative-slope
threshold large enough to force either large normalized physical viscous
dissipation or the very same radial concentration/dissipation pair. -/
theorem h3Path_fastDecaySnapshot_forces_dissipation_or_jointRadial244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (n : ℕ)
    (hFast : h3PathFastDecaySlopeThreshold244 u b ((n : ℝ) + 1) *
      velocityH3EnergyAt u t < -deriv (velocityH3EnergyAt u) t) :
    (((n : ℝ) + 1) * velocityH3EnergyAt u t <
      velocityH3DissipationAt u t) ∨
    (((n : ℝ) + 2) *
        h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) >
        ((n : ℝ) + 1) * h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u t <
        ((n : ℝ) + 3) * velocityH3DissipationAt u t) := by
  let R : ℝ := (n : ℝ) + 1
  let E : ℝ := velocityH3EnergyAt u t
  let D : ℝ := velocityH3DissipationAt u t
  let F : ℝ := deriv (velocityH3EnergyAt u) t
  let W : ℝ := velocityH3TransportDerivativeAt u t
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let Q : ℝ := h3PathFastDecayRadialRootRequest244 u b R
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hE : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u t)
  have hK : 0 ≤ 4422 * C := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4422)
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hBalance : F + 2 * D = -W := by
    dsimp only [F, D, W]
    exact deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass htClass
  have hAbs := h3Path_physicalFullTransport_abs_le_sqrtEnergy244
    hH3 hClass htClass
  have hTransport : W ≤ (4422 + (4422 * C) * Real.sqrt E) * E := by
    have hW : W ≤ |W| := le_abs_self W
    have hWBound : |W| ≤ (4422 + (4422 * C) * Real.sqrt E) * E := by
      dsimp only [W, C, E] at hAbs ⊢
      convert hAbs using 1 <;> ring
    exact hW.trans hWBound
  have hThreshold : (2 * R + 4422 + (4422 * C) * Q) * E < -F := by
    dsimp only [h3PathFastDecaySlopeThreshold244, R, E, F, C, Q] at hFast ⊢
    convert hFast using 1 <;> ring
  rcases h3Path_fastSlope_largeDissipation_or_largeEnergyRoot244
      E D F W R (4422 * C) Q hE hK hBalance hTransport hThreshold with
    hD | hRoot
  · left
    simpa only [R, D, E] using hD
  · right
    have hA : 0 ≤ 48 * C := by
      exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 48)
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
    have hHigh :
        h3PathHighEnergyRadialRequest244 u b R ≤
          (48 * C) * Real.sqrt E := by
      change (48 * C) * Q ≤ (48 * C) * Real.sqrt E
      exact mul_le_mul_of_nonneg_left hRoot hA
    have hJoint := h3Path_highEnergyRequest_forces_jointRadialClock244
      hH3 hClass b hb t ht n (by
        dsimp only [R, C, E] at hHigh
        convert hHigh using 1 <;> ring)
    exact hJoint

/-- A fixed cofinal fast-negative-energy-slope channel yields ONE strict
terminal sequence where the rapid decay remains present and normalized
physical H³ dissipation diverges. At every snapshot, either a direct
viscous-energy inequality holds or high-radial energy dominance accompanies
the full physical cubic dissipation clock. -/
theorem h3Path_cofinalFastDecay_forces_synchronizedDissipationSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hFast : ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        B * velocityH3EnergyAt u t < -deriv (velocityH3EnergyAt u) t) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        h3PathFastDecaySlopeThreshold244 u ((a + T) / 2) ((n : ℝ) + 1) *
          velocityH3EnergyAt u (τ n) <
            -deriv (velocityH3EnergyAt u) (τ n)) ∧
      (∀ n : ℕ,
        (((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
          velocityH3DissipationAt u (τ n)) ∨
        (((n : ℝ) + 2) *
            h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
            ((n : ℝ) + 1) * h3SpectralVelocitySquareEnergy
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ∧
          ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u (τ n) <
            ((n : ℝ) + 3) * velocityH3DissipationAt u (τ n))) ∧
      Tendsto (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          velocityH3EnergyAt u (τ n)) atTop atTop := by
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [hClass.terminal_start.2]
  have hChoice : ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        h3PathFastDecaySlopeThreshold244 u b B *
          velocityH3EnergyAt u t < -deriv (velocityH3EnergyAt u) t := by
    intro c hc B hB
    have hC : 0 ≤ h3TerminalRadialSobolevWeightSquareCeiling B *
        velocityH3Energy0At u b :=
      mul_nonneg (h3TerminalRadialSobolevWeightSquareCeiling_pos B).le
        (velocityH3Energy0At_nonneg u b)
    have hRoot : 0 ≤ h3PathFastDecayRadialRootRequest244 u b B := by
      unfold h3PathFastDecayRadialRootRequest244
      have hProd : 0 ≤ (B + 2) *
          (h3TerminalRadialSobolevWeightSquareCeiling B *
            velocityH3Energy0At u b + 2) :=
        mul_nonneg (by linarith) (by linarith)
      linarith only [hProd]
    have hSlope : 0 ≤ h3PathFastDecaySlopeThreshold244 u b B := by
      unfold h3PathFastDecaySlopeThreshold244
      have hProd : 0 ≤
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            h3PathFastDecayRadialRootRequest244 u b B :=
        mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
          hRoot
      nlinarith only [hB, hProd]
    have hcClass : c ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hc.1, hc.2⟩
    exact hFast c hcClass _ hSlope
  obtain ⟨τ, hτ, hNear, hLimit, hSlope⟩ :=
    h3Path_cofinalThreshold_diagonalPredicate244 hb.2
      (fun t B => h3PathFastDecaySlopeThreshold244 u b B *
        velocityH3EnergyAt u t < -deriv (velocityH3EnergyAt u) t) hChoice
  have hPair (n : ℕ) :=
    h3Path_fastDecaySnapshot_forces_dissipation_or_jointRadial244
      hH3 hClass b hb (τ n) (hτ n) n (hSlope n)
  have hDiverges : Tendsto (fun n : ℕ =>
      velocityH3DissipationAt u (τ n) /
        velocityH3EnergyAt u (τ n)) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    obtain ⟨N, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hnOne : 1 ≤ n := (le_max_right N 1).trans hn
    let R : ℝ := (n : ℝ) + 1
    have hR : 2 ≤ R := by
      have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnOne
      dsimp only [R]
      linarith
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (one_le_velocityH3EnergyAt u (τ n))
    have hNorm : R < velocityH3DissipationAt u (τ n) /
        velocityH3EnergyAt u (τ n) := by
      rcases hPair n with hDirect | hJoint
      · exact (lt_div_iff₀ hE).2 (by simpa only [R] using hDirect)
      · apply h3Path_cubicDissipationEnergyClock_forces_ratio_gt_radius244
          (velocityH3EnergyAt u (τ n))
          (velocityH3DissipationAt u (τ n)) R hR hE
        simpa only [R, show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
          using hJoint.2
    have hMn : M < (n : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hnN)
    have hnR : (n : ℝ) < R := by dsimp only [R]; linarith
    exact le_of_lt (lt_trans (lt_trans hMn hnR) hNorm)
  exact ⟨τ, (fun n => ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩),
    hNear, hLimit, (fun n => hSlope n), (fun n => hPair n), hDiverges⟩

end
end PrimeTensor.FirstMonomialTriad
