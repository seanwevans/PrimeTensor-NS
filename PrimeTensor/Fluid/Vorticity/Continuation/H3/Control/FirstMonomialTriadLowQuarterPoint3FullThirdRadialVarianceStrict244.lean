import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdActualRadialVariance244
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Strict physical first-Cauchy variance from Fourier sphere nullity

The previously proved division-free physical variance identity and
zero-defect radial-level rigidity are combined with the Haar-measure
fact that a Euclidean sphere has zero ambient volume. No a priori
spectral-spread or quantitative gap is assumed.

For every admissible H³ time with **positive kinetic mass** E₀(t)>0,

  F₁(t) = E₀(t) D₃(t) - E₂(t)² > 0.

Thus the sharp 27/256 Fourier Young ceiling is strictly loose when its
Landau coefficient and D₃ are positive. This is qualitative only:
positive Fourier mass may concentrate into arbitrarily thin annuli,
and no uniform-in-time lower bound for F₁ is established here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeRadialVarianceStrict244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceRadialVarianceStrict244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The Fourier squared-frequency level has only one radius: equality
of `q(ξ)^2` and `q(η)^2` forces equality of their Euclidean norms. -/
theorem h3_radialVariance_equalLevel_eq_norm244
    (ξ η : H3FourierPoint3)
    (hLevel : h3FourierGradientSquare ξ ^ 2 =
      h3FourierGradientSquare η ^ 2) :
    ‖ξ‖ = ‖η‖ := by
  have hqξ : 0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ
  have hqη : 0 ≤ h3FourierGradientSquare η :=
    h3FourierGradientSquare_nonneg η
  have hq : h3FourierGradientSquare ξ =
      h3FourierGradientSquare η := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hLevel with hEq | hOpp
    · exact hEq
    · linarith only [hqξ, hqη, hOpp]
  have hc : 0 < (2 * Real.pi) ^ 2 := by
    exact pow_pos (mul_pos (by norm_num) Real.pi_pos) 2
  have hnormsq : ‖ξ‖ ^ 2 = ‖η‖ ^ 2 := by
    apply (mul_left_cancel₀ (ne_of_gt hc))
    simpa only [h3FourierGradientSquare] using hq
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hnormsq with hEq | hOpp
  · exact hEq
  · linarith only [norm_nonneg ξ, norm_nonneg η, hOpp]

/-- A fixed squared-frequency level is a null set for the actual
Lebesgue/Haar measure on the project's physical Fourier point space. -/
theorem h3_radialVariance_fixedLevel_null244
    (m0 m2 : ℝ) (hm0 : m0 ≠ 0) :
    (volume : Measure H3FourierPoint3)
      {ξ | m0 * h3FourierGradientSquare ξ ^ 2 = m2} = 0 := by
  classical
  -- The intrinsic three-axis type is inhabited; make this explicit so
  -- `EuclideanSpace` has its required `Nontrivial` instance for Haar spheres.
  haveI : Nonempty (PrimeTensor.Axis Depth.three) :=
    ⟨h3AxisOfFin3 (0 : Fin 3)⟩
  letI : Nontrivial H3FourierPoint3 := inferInstance
  by_cases hExists : ∃ η : H3FourierPoint3,
      m0 * h3FourierGradientSquare η ^ 2 = m2
  · obtain ⟨η, hη⟩ := hExists
    have hSubset :
        {ξ : H3FourierPoint3 |
          m0 * h3FourierGradientSquare ξ ^ 2 = m2} ⊆
        Metric.sphere (0 : H3FourierPoint3) ‖η‖ := by
      intro ξ hξ
      have hSquare : h3FourierGradientSquare ξ ^ 2 =
          h3FourierGradientSquare η ^ 2 := by
        apply (mul_left_cancel₀ hm0)
        exact hξ.trans hη.symm
      have hn := h3_radialVariance_equalLevel_eq_norm244 ξ η hSquare
      simpa only [Metric.mem_sphere, dist_zero_right] using hn
    exact measure_mono_null hSubset
      (MeasureTheory.Measure.addHaar_sphere
        (volume : Measure H3FourierPoint3)
        (0 : H3FourierPoint3) ‖η‖)
  · have hEmpty :
        {ξ : H3FourierPoint3 |
          m0 * h3FourierGradientSquare ξ ^ 2 = m2} = ∅ := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hξ
      exact hExists ⟨ξ, hξ⟩
    simp only [hEmpty, measure_empty]

/-- For positive kinetic mass, zero first Fourier Cauchy defect is
impossible: it would force all physical Fourier mass onto a null sphere. -/
theorem h3Path_topFourier_firstCauchyDefect_pos_of_kineticMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t) :
    0 < h3PathTopFourierFirstCauchyDefect244 u t := by
  have hFNonneg : 0 ≤ h3PathTopFourierFirstCauchyDefect244 u t :=
    (h3Path_topFourier_twoCauchyDefects_nonneg244 hH3 hClass ht).1
  by_contra hNotPos
  have hZero : h3PathTopFourierFirstCauchyDefect244 u t = 0 :=
    le_antisymm (le_of_not_gt hNotPos) hFNonneg
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  let S : H3FourierPoint3 → ℝ :=
    velocityH3FourierMassDensityAt u t hInt hMeas
  have hS : ∀ ξ, 0 ≤ S ξ := by
    intro ξ
    exact velocityH3FourierMassDensityAt_nonneg u t hInt hMeas ξ
  have hMono :=
    h3Path_topFourier_firstCauchyZero_monochromatic_ae244
      hH3 hClass ht hZero
  dsimp only at hMono
  have hLevelNull : (volume : Measure H3FourierPoint3)
      {ξ | velocityH3Energy0At u t *
        h3FourierGradientSquare ξ ^ 2 = velocityH3Energy2At u t} = 0 :=
    h3_radialVariance_fixedLevel_null244
      (velocityH3Energy0At u t) (velocityH3Energy2At u t)
      (ne_of_gt hMass)
  have hLevelAE : ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      ¬ (velocityH3Energy0At u t * h3FourierGradientSquare ξ ^ 2 =
        velocityH3Energy2At u t) := by
    rw [ae_iff]
    simpa only [not_not] using hLevelNull
  have hSAE : ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3), S ξ = 0 := by
    filter_upwards [hMono, hLevelAE] with ξ hMonochromatic hNotLevel
    have hNotPos : ¬ 0 < S ξ := fun hs => hNotLevel (hMonochromatic hs)
    exact le_antisymm (le_of_not_gt hNotPos) (hS ξ)
  have h0 : (∫ ξ : H3FourierPoint3, S ξ ∂volume) =
      velocityH3Energy0At u t := by
    calc
      _ = velocityH3FourierZerothRadialMomentAt u t hInt hMeas :=
        (velocityH3FourierZerothRadialMomentAt_eq_integral_massDensity
          hInt hMeas).symm
      _ = velocityH3Energy0At u t :=
        (velocityH3Energy0At_eq_fourierZerothRadialMoment hInt hMeas).symm
  have h0Zero : velocityH3Energy0At u t = 0 := by
    rw [← h0]
    have hIntegral : (∫ ξ : H3FourierPoint3, S ξ ∂volume) =
        (∫ _ξ : H3FourierPoint3, (0 : ℝ) ∂volume) :=
      integral_congr_ae hSAE
    simpa only [integral_zero] using hIntegral
  exact (ne_of_gt hMass) h0Zero

/-- Without an extra dispersion assumption, every positive-kinetic-mass
physical H³ state has a *strict* first Cauchy inequality. -/
theorem h3Path_topFourier_strictFirstCauchy_of_kineticMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t) :
    velocityH3Energy2At u t ^ 2 <
      velocityH3Energy0At u t * velocityH3Dissipation3At u t := by
  have hStrict :=
    h3Path_topFourier_firstCauchyDefect_pos_of_kineticMass244
      hH3 hClass ht hMass
  unfold h3PathTopFourierFirstCauchyDefect244 at hStrict
  linarith only [hStrict]

/-- The strict physical first-Cauchy inequality immediately improves the
optimal abstract Young ceiling for K>0 and D₃>0. Strictness has no
uniform quantitative modulus on a terminal time interval. -/
theorem h3Path_topFourier_strictYoung_of_kineticMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t) :
    K * velocityH3Energy3At u t <
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
  exact h3Path_topFourier_strictYoung_of_firstVariance244
    hH3 hClass ht hK hD
    (h3Path_topFourier_firstCauchyDefect_pos_of_kineticMass244
      hH3 hClass ht hMass)

end
end PrimeTensor.FirstMonomialTriad
