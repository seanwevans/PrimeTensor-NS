import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopSecondEnergyEightMomentAlternative244
import Mathlib.Tactic

/-!
# Construct the physical second-radial Fourier L² representative

The physical Fourier-compatible H³ velocity path provides an integrable
second-symbol density `q(ξ)^2 |U_j(ξ)|²`, with

  q(ξ)^2 = (2π)^4 |ξ|^4.

Thus `|ξ|² U_j(ξ)` actually belongs to Fourier L² on every strict time
slice. Construct this L² class with `MemLp.toLp` and identify its representative
almost everywhere. The previous second-energy/eighth-moment dichotomy then
requires no separately postulated order-two Fourier representative.

The strict-time raw eighth-moment input for the nonlinear convolution estimate
remains explicit; neither its existence nor a uniform bound is inferred here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalSecondRadialRepresentative244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalSecondRadialRepresentative244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2000000

/-- Each strict-time physical velocity component has its *actual*
second-radial Fourier L² representative. This follows from the already-proved
physical second-derivative Fourier-jet integrability, not an added assumption. -/
theorem h3Path_secondRadialFourierL2_exists_from_physicalJets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (j : Fin 3) :
    ∃ G₂ : H3FourierComplexL2,
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ) := by
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
  let f : H3FourierPoint3 → ℂ := fun ξ =>
    ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
      h3SpectralScalarRawFourier (U j) ξ
  have hFMeas : AEStronglyMeasurable f
      (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).aestronglyMeasurable.mul
        (h3SpectralScalarRawFourier_memLp2 (U j)).1
  have hc : ((2 * Real.pi) ^ 4 : ℝ) ≠ 0 := by positivity
  have hPhysical : Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 2 *
          ‖velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3) :=
    integrable_h3FourierGradientSquare_sq_mul_base_norm_sq
      hInt hMeas hFourier j
  have hScaled : Integrable
      (fun ξ : H3FourierPoint3 =>
        ((2 * Real.pi) ^ 4)⁻¹ *
          (h3FourierGradientSquare ξ ^ 2 *
            ‖velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2))
      (volume : Measure H3FourierPoint3) :=
    hPhysical.const_mul _
  have hSqInt : Integrable (fun ξ : H3FourierPoint3 => ‖f ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3) := by
    refine hScaled.congr ?_
    filter_upwards [hRawAE] with ξ hξ
    dsimp only [f]
    rw [hξ]
    rw [h3FourierGradientSquare_sq_eq_two_pi_four_mul_norm_four ξ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 2), mul_pow]
    field_simp [hc]
  have hF2 : MemLp f 2 (volume : Measure H3FourierPoint3) := by
    exact (memLp_two_iff_integrable_sq_norm hFMeas).2 hSqInt
  refine ⟨hF2.toLp f, ?_⟩
  exact MemLp.coeFn_toLp hF2

/-- Energy-two control implies eighth raw velocity moment escape, without
an assumption that the second-radial Fourier L² representatives exist. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMoment_of_energyTwoCeiling_noRep244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hEnergy : ∀ t (_ht : t ∈ Set.Ioo a T), s < t →
      velocityH3Energy2At u t ≤ B) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r := by
  exact h3Path_unboundedPhysicalTop_forces_eightMoment_of_energyTwoCeiling244
    hH3 hClass hs hEscape hMom
    (fun t ht j =>
      h3Path_secondRadialFourierL2_exists_from_physicalJets244
        hH3 hClass ht j)
    hEnergy

/-- The real physical obstruction no longer includes any Fourier
representative-existence hypothesis: `E₂` escape or cofinal eighth moments. -/
theorem h3Path_unboundedPhysicalTop_forces_energyTwo_or_eightMoment_noRep244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Energy2At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  exact h3Path_unboundedPhysicalTop_forces_energyTwo_or_eightMoment244
    hH3 hClass hs hEscape hMom
    (fun t ht j =>
      h3Path_secondRadialFourierL2_exists_from_physicalJets244
        hH3 hClass ht j)

/-- First-order physical dissipation equals second-order energy. The
same necessary escape alternative now has no second-radial premise. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_noRep244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  exact h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment244
    hH3 hClass hs hEscape hMom
    (fun t ht j =>
      h3Path_secondRadialFourierL2_exists_from_physicalJets244
        hH3 hClass ht j)

end
end PrimeTensor.FirstMonomialTriad
