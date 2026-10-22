import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopBesselSecondRadial244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fourier.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.RHS.Continuity
import Mathlib.Tactic

/-!
# Physical second energy replaces the order-two radial Fourier ceiling

On a strict physical H³ time slice, the weighted Fourier state
`|ξ|² û_j` carries one component of the exact second-order energy:

  (2π)^4 ‖ |ξ|² û_j ‖₂² ≤ E₂(t).

This is proved using the actual Fourier-compatible velocity state and the
existing equality between the sum of second radial Fourier masses and
physical `velocityH3Energy2At`. It does not replace `|ξ|²` by `q` without
the factor `(2π)^4`.

Combining this estimate with the previously formalized inverse-Bessel and
kinetic-anchor reductions yields a physical terminal alternative between
second-order energy escape and eighth-order raw velocity moment escape.
The order-two Fourier representative's existence is retained as an explicit
premise, distinct from its now-derived quantitative energy ceiling.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 2400000

noncomputable local instance axisFintypeH3PhysicalSecondEnergyEightMoment244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalSecondEnergyEightMoment244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The second-order Fourier representative's squared norm is a genuine
component of the physical order-two energy, with the exact `2π` factor. -/
theorem h3Path_secondRadialFourierL2_sq_le_physicalEnergyTwo244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (j : Fin 3)
    (G₂ : H3FourierComplexL2)
    (hG₂ :
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ)) :
    (2 * Real.pi) ^ 4 * ‖G₂‖ ^ 2 ≤ velocityH3Energy2At u t := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hRaw : h3SpectralScalarRawFourierL2 (U j) =
      velocityH3BaseFourierAt u t hInt hMeas j := by
    dsimp only [U]
    unfold h3TerminalVelocitySpectralStateAt
    exact h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier j
  have hRawAE :
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier (U j) ξ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        velocityH3BaseFourierAt u t hInt hMeas j ξ) := by
    filter_upwards [h3SpectralScalarRawFourierL2_ae (U j)]
      with ξ hξ
    rw [hRaw] at hξ
    exact hξ.symm
  have hRep :
      ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ) := hG₂
  have hIntegral :
      (2 * Real.pi) ^ 4 * ‖G₂‖ ^ 2 =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 2 *
          ‖velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2 := by
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hRep, hRawAE] with ξ hGξ hUξ
    rw [hGξ, hUξ]
    rw [h3FourierGradientSquare_sq_eq_two_pi_four_mul_norm_four ξ]
    have hr0 : 0 ≤ ‖ξ‖ ^ 2 := pow_nonneg (norm_nonneg ξ) 2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, mul_pow]
    ring
  let f (k : Fin 3) : ℝ :=
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 2 *
        ‖velocityH3BaseFourierAt u t hInt hMeas k ξ‖ ^ 2
  have hfNonneg (k : Fin 3) : 0 ≤ f k := by
    dsimp only [f]
    exact integral_nonneg (fun ξ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hCoord : f j ≤ ∑ k : Fin 3, f k :=
    Finset.single_le_sum (fun k _ => hfNonneg k) (Finset.mem_univ j)
  have hSum : (∑ k : Fin 3, f k) = velocityH3Energy2At u t := by
    calc
      (∑ k : Fin 3, f k) =
          velocityH3FourierSecondRadialMomentAt u t hInt hMeas := rfl
      _ = velocityH3Energy2At u t :=
        (velocityH3Energy2At_eq_fourierSecondRadialMoment
          hInt hMeas hFourier).symm
  rw [hIntegral]
  exact hCoord.trans_eq hSum

/-- A second radial Fourier representative is bounded by the square root of
actual physical second-order energy, with exact normalization `(2π)²`. -/
theorem h3Path_secondRadialFourierL2_le_sqrt_physicalEnergyTwo244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (j : Fin 3)
    (G₂ : H3FourierComplexL2)
    (hG₂ :
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ)) :
    ‖G₂‖ ≤ Real.sqrt (velocityH3Energy2At u t) /
        (2 * Real.pi) ^ 2 := by
  let c : ℝ := (2 * Real.pi) ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hSquare := h3Path_secondRadialFourierL2_sq_le_physicalEnergyTwo244
    hH3 hClass ht j G₂ hG₂
  have hC : c ^ 2 = (2 * Real.pi) ^ 4 := by
    dsimp only [c]
    ring
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hRoot : (Real.sqrt (velocityH3Energy2At u t)) ^ 2 =
      velocityH3Energy2At u t := Real.sq_sqrt hE2
  have hQuad : (c * ‖G₂‖) ^ 2 ≤
      (Real.sqrt (velocityH3Energy2At u t)) ^ 2 := by
    calc
      (c * ‖G₂‖) ^ 2 = (2 * Real.pi) ^ 4 * ‖G₂‖ ^ 2 := by
        rw [mul_pow, hC]
      _ ≤ velocityH3Energy2At u t := hSquare
      _ = (Real.sqrt (velocityH3Energy2At u t)) ^ 2 := hRoot.symm
  have hNonneg : 0 ≤ c * ‖G₂‖ := mul_nonneg hc.le (norm_nonneg _)
  have hUpper : c * ‖G₂‖ ≤ Real.sqrt (velocityH3Energy2At u t) := by
    nlinarith only [hQuad, hNonneg,
      Real.sqrt_nonneg (velocityH3Energy2At u t)]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hUpper)

/-- A UNIFORM PHYSICAL second-order energy ceiling now supplies the
quantitative order-two Fourier input ceiling needed by the preceding
inverse-Bessel terminal criterion. Only existence of the representative
remains as a separate hypothesis. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMoment_of_energyTwoCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hSecondRep : ∀ t (ht : t ∈ Set.Ioo a T),
      ∀ j : Fin 3, ∃ G₂ : H3FourierComplexL2,
        let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
        let U : H3SpectralFinVectorState :=
          h3TerminalVelocitySpectralStateAt hH3 t htAbs
        ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier (U j) ξ))
    (hEnergy : ∀ t (ht : t ∈ Set.Ioo a T), s < t →
      velocityH3Energy2At u t ≤ B) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r := by
  let C : ℝ := Real.sqrt (max B 0) / (2 * Real.pi) ^ 2
  apply h3Path_unboundedPhysicalTop_forces_eightMoment_of_secondRadialL2Ceiling244
    (B := C) hH3 hClass hs hEscape hMom
  intro t ht hst j
  obtain ⟨G₂, hG₂⟩ := hSecondRep t ht j
  refine ⟨G₂, hG₂, ?_⟩
  have hNorm := h3Path_secondRadialFourierL2_le_sqrt_physicalEnergyTwo244
    hH3 hClass ht j G₂ hG₂
  have hEnergyLe : velocityH3Energy2At u t ≤ max B 0 :=
    (hEnergy t ht hst).trans (le_max_left B 0)
  have hSqrt := Real.sqrt_le_sqrt hEnergyLe
  have hInvNonneg : 0 ≤ ((2 * Real.pi) ^ 2 : ℝ)⁻¹ := by
    positivity
  have hScaled := mul_le_mul_of_nonneg_right hSqrt hInvNonneg
  exact hNorm.trans (by simpa only [C, div_eq_mul_inv] using hScaled)

/-- The intrinsic physical terminal obstruction, after removing raw Fourier
L² and L¹ escape channels, is now EITHER physical second-order energy growth
OR cofinal physical eighth raw velocity moments. The order-two Fourier
representatives are assumed to exist, not their size. -/
theorem h3Path_unboundedPhysicalTop_forces_energyTwo_or_eightMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hSecondRep : ∀ t (ht : t ∈ Set.Ioo a T),
      ∀ j : Fin 3, ∃ G₂ : H3FourierComplexL2,
        let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
        let U : H3SpectralFinVectorState :=
          h3TerminalVelocitySpectralStateAt hH3 t htAbs
        ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier (U j) ξ)) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Energy2At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  classical
  by_cases hUnbounded :
      ∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
        K < velocityH3Energy2At u r
  · exact Or.inl hUnbounded
  · right
    push Not at hUnbounded
    obtain ⟨B, hBound⟩ := hUnbounded
    apply h3Path_unboundedPhysicalTop_forces_eightMoment_of_energyTwoCeiling244
      (B := B) hH3 hClass hs hEscape hMom hSecondRep
    intro t ht hst
    exact hBound t ⟨hst, ht.2⟩


/-- The same necessary terminal alternative expressed in the exact physical
first-dissipation block `D₁ = E₂`; this equality was proved independently by
reordering the spatial-derivative energy sums. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hSecondRep : ∀ t (ht : t ∈ Set.Ioo a T),
      ∀ j : Fin 3, ∃ G₂ : H3FourierComplexL2,
        let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
        let U : H3SpectralFinVectorState :=
          h3TerminalVelocitySpectralStateAt hH3 t htAbs
        ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier (U j) ξ)) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  rcases h3Path_unboundedPhysicalTop_forces_energyTwo_or_eightMoment244
    hH3 hClass hs hEscape hMom hSecondRep with hLow | hHigh
  · left
    intro K
    obtain ⟨r, hr, hEnergy⟩ := hLow K
    exact ⟨r, hr, by
      rw [velocityH3Dissipation1At_eq_energy2]
      exact hEnergy⟩
  · exact Or.inr hHigh

end
end PrimeTensor.FirstMonomialTriad
