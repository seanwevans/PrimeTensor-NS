import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinLerayEncodedIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRealizabilityClosure
import PrimeTensor.Fluid.Vorticity.Preterminal.Equation

/-!
# Physical incompressibility implies spectral Leray invariance

`FinLerayEncodedIncompressibility` isolated the only remaining input to the
finite Leray projector: the raw base Fourier velocity must satisfy

    Σⱼ dⱼ(ξ) ûⱼ(ξ) = 0

almost everywhere.

This file derives that relation from the actual physical incompressibility
identity.  The route is deliberately exact:

* the three diagonal first-derivative physical `L²` slots sum to zero;
* the scalar Plancherel map is additive, so their Fourier transforms sum to
  zero in `L²`;
* Fourier compatibility identifies each transformed derivative with
  `dⱼ(ξ) ûⱼ(ξ)` almost everywhere.

The final theorem specializes the pointwise hypothesis to
`LoggedPreterminalNavierStokesAdmissible`, using the preterminal divergence
identity already proved in `Preterminal.Equation`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3FinLerayPhysicalIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Additivity of the scalar Plancherel bridge -/

@[simp]
theorem h3ScalarFourierL2_zero :
    h3ScalarFourierL2 (0 : H3ScalarL2) = 0 := by
  unfold h3ScalarFourierL2
  have hTo : h3ToFourierRealL2 (0 : H3ScalarL2) = 0 := by
    unfold h3ToFourierRealL2
    exact map_zero _
  rw [hTo, h3ComplexifyFourierL2_zero]
  exact map_zero _

@[simp]
theorem h3ScalarFourierL2_add
    (f g : H3ScalarL2) :
    h3ScalarFourierL2 (f + g)
      = h3ScalarFourierL2 f + h3ScalarFourierL2 g := by
  unfold h3ScalarFourierL2
  have hTo :
      h3ToFourierRealL2 (f + g)
        = h3ToFourierRealL2 f + h3ToFourierRealL2 g := by
    unfold h3ToFourierRealL2
    exact map_add _ f g
  rw [hTo, h3ComplexifyFourierL2_add]
  exact map_add _ _ _

/-- Additivity of the scalar Plancherel bridge over the canonical three-axis
    finite sum. -/
theorem h3ScalarFourierL2_sum_fin3
    (F : Fin 3 → H3ScalarL2) :
    h3ScalarFourierL2 (∑ j : Fin 3, F j)
      = ∑ j : Fin 3, h3ScalarFourierL2 (F j) := by
  simp only [Fin.sum_univ_three]
  rw [h3ScalarFourierL2_add, h3ScalarFourierL2_add]

/-! ## Representatives of the physical and Fourier finite sums -/

/-- One concrete physical H³ jet coordinate is represented almost everywhere
    by its defining scalar field. -/
theorem velocityH3L2JetAt_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (a : H3JetIndex) :
    (velocityH3L2JetAt u t hInt hMeas a : Point3 → ℝ)
      =ᵐ[volume]
    velocityH3JetFieldAt u t a := by
  unfold velocityH3L2JetAt
  dsimp only
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (velocityH3JetFieldAt_memLp2 hInt hMeas a)

/-- The representative of a three-term scalar `L²` sum is the pointwise
    three-term sum almost everywhere. -/
theorem h3ScalarL2_sum_fin3_ae
    (F : Fin 3 → H3ScalarL2) :
    ((∑ j : Fin 3, F j : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[volume]
    (fun x : Point3 => ∑ j : Fin 3, (F j : Point3 → ℝ) x) := by
  let A0 : H3ScalarL2 := F 0
  let A1 : H3ScalarL2 := F 1
  let A2 : H3ScalarL2 := F 2
  have h01 := MeasureTheory.Lp.coeFn_add A0 A1
  have h012 := MeasureTheory.Lp.coeFn_add (A0 + A1) A2
  filter_upwards [h01, h012] with x h01x h012x
  simp only [Fin.sum_univ_three]
  change ((A0 + A1 + A2 : H3ScalarL2) : Point3 → ℝ) x = _
  rw [h012x]
  simp only [Pi.add_apply]
  rw [h01x]
  simp only [Pi.add_apply]
  rfl

/-- The analogous representative identity for complex Fourier `L²`. -/
theorem h3FourierComplexL2_sum_fin3_ae
    (F : Fin 3 → H3FourierComplexL2) :
    ((∑ j : Fin 3, F j : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      ∑ j : Fin 3, (F j : H3FourierPoint3 → ℂ) ξ) := by
  let A0 : H3FourierComplexL2 := F 0
  let A1 : H3FourierComplexL2 := F 1
  let A2 : H3FourierComplexL2 := F 2
  have h01 := MeasureTheory.Lp.coeFn_add A0 A1
  have h012 := MeasureTheory.Lp.coeFn_add (A0 + A1) A2
  filter_upwards [h01, h012] with ξ h01ξ h012ξ
  simp only [Fin.sum_univ_three]
  change ((A0 + A1 + A2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) ξ = _
  rw [h012ξ]
  simp only [Pi.add_apply]
  rw [h01ξ]
  simp only [Pi.add_apply]
  rfl

/-! ## Pointwise physical divergence -> zero Fourier derivative sum -/

/-- Pointwise incompressibility makes the diagonal first-derivative physical
    `L²` slots sum to zero. -/
theorem velocityH3L2JetAt_orderOne_diag_sum_eq_zero_of_pointwise
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hDiv :
      ∀ x : Point3,
        (∑ j : Fin 3,
          spatial3.d
            (h3AxisOfFin3 j)
            (loggedVelocityComponent u t (h3AxisOfFin3 j))
            x) = 0) :
    (∑ j : Fin 3,
      velocityH3L2JetAt u t hInt hMeas (h3JetSlot1 j j)) = 0 := by
  apply MeasureTheory.Lp.ext
  let F : Fin 3 → H3ScalarL2 :=
    fun j => velocityH3L2JetAt u t hInt hMeas (h3JetSlot1 j j)
  have hRep := h3ScalarL2_sum_fin3_ae F
  have h0 := velocityH3L2JetAt_ae hInt hMeas (h3JetSlot1 0 0)
  have h1 := velocityH3L2JetAt_ae hInt hMeas (h3JetSlot1 1 1)
  have h2 := velocityH3L2JetAt_ae hInt hMeas (h3JetSlot1 2 2)
  have hZero :=
    MeasureTheory.Lp.coeFn_zero ℝ 2 (volume : Measure Point3)
  filter_upwards [hRep, h0, h1, h2, hZero] with x hRepx h0x h1x h2x hZerox
  have hh0 :
      (velocityH3L2JetAt u t hInt hMeas (h3JetSlot1 0 0) : Point3 → ℝ) x
        = spatial3.d xAxis (loggedVelocityComponent u t xAxis) x := by
    simpa [velocityH3JetFieldAt, h3JetSlot1] using h0x
  have hh1 :
      (velocityH3L2JetAt u t hInt hMeas (h3JetSlot1 1 1) : Point3 → ℝ) x
        = spatial3.d yAxis (loggedVelocityComponent u t yAxis) x := by
    simpa [velocityH3JetFieldAt, h3JetSlot1] using h1x
  have hh2 :
      (velocityH3L2JetAt u t hInt hMeas (h3JetSlot1 2 2) : Point3 → ℝ) x
        = spatial3.d zAxis (loggedVelocityComponent u t zAxis) x := by
    simpa [velocityH3JetFieldAt, h3JetSlot1] using h2x
  change ((∑ j : Fin 3, F j : H3ScalarL2) : Point3 → ℝ) x
      = ((0 : H3ScalarL2) : Point3 → ℝ) x
  rw [hRepx, hZerox]
  simp only [Fin.sum_univ_three, F, hh0, hh1, hh2]
  simpa only [
    Fin.sum_univ_three,
    h3AxisOfFin3_zero, h3AxisOfFin3_one, h3AxisOfFin3_two,
    Pi.zero_apply
  ] using hDiv x

/-- Therefore the three diagonal first-derivative Fourier jet slots sum to
    zero in complex `L²`. -/
theorem velocityH3FourierJetAt_orderOne_diag_sum_eq_zero_of_pointwise
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hDiv :
      ∀ x : Point3,
        (∑ j : Fin 3,
          spatial3.d
            (h3AxisOfFin3 j)
            (loggedVelocityComponent u t (h3AxisOfFin3 j))
            x) = 0) :
    (∑ j : Fin 3,
      velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j j)) = 0 := by
  have hPhysical :=
    velocityH3L2JetAt_orderOne_diag_sum_eq_zero_of_pointwise
      hInt hMeas hDiv
  have h := congrArg h3ScalarFourierL2 hPhysical
  rw [h3ScalarFourierL2_sum_fin3, h3ScalarFourierL2_zero] at h
  simpa [velocityH3FourierJetAt, h3L2JetFourierApply] using h

/-! ## Physical divergence -> raw Fourier divergence -/

/-- Pointwise physical incompressibility plus the already-proved derivative
    Fourier compatibility gives the exact raw Fourier divergence-free
    relation. -/
theorem velocityH3BaseFourierDivergenceFreeAt_of_pointwise
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hDiv :
      ∀ x : Point3,
        (∑ j : Fin 3,
          spatial3.d
            (h3AxisOfFin3 j)
            (loggedVelocityComponent u t (h3AxisOfFin3 j))
            x) = 0) :
    VelocityH3BaseFourierDivergenceFreeAt u t hInt hMeas := by
  let F : Fin 3 → H3FourierComplexL2 :=
    fun j => velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j j)

  have hFzero : (∑ j : Fin 3, F j) = 0 := by
    exact
      velocityH3FourierJetAt_orderOne_diag_sum_eq_zero_of_pointwise
        hInt hMeas hDiv

  have hRep := h3FourierComplexL2_sum_fin3_ae F
  have hZero :
      ((∑ j : Fin 3, F j : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      (fun _ : H3FourierPoint3 => 0) := by
    rw [hFzero]
    exact
      MeasureTheory.Lp.coeFn_zero ℂ 2
        (volume : Measure H3FourierPoint3)

  have h0 := velocityH3FourierCompatibleAt_orderOne hFourier 0 0
  have h1 := velocityH3FourierCompatibleAt_orderOne hFourier 1 1
  have h2 := velocityH3FourierCompatibleAt_orderOne hFourier 2 2

  filter_upwards [hRep, hZero, h0, h1, h2] with ξ hRepξ hZeroξ h0ξ h1ξ h2ξ
  have hh0 :
      (F 0 : H3FourierPoint3 → ℂ) ξ
        = h3FourierDerivativeSymbol 0 ξ *
            velocityH3BaseFourierAt u t hInt hMeas 0 ξ := by
    simpa [F] using h0ξ
  have hh1 :
      (F 1 : H3FourierPoint3 → ℂ) ξ
        = h3FourierDerivativeSymbol 1 ξ *
            velocityH3BaseFourierAt u t hInt hMeas 1 ξ := by
    simpa [F] using h1ξ
  have hh2 :
      (F 2 : H3FourierPoint3 → ℂ) ξ
        = h3FourierDerivativeSymbol 2 ξ *
            velocityH3BaseFourierAt u t hInt hMeas 2 ξ := by
    simpa [F] using h2ξ
  calc
    (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ)
        = ∑ j : Fin 3, (F j : H3FourierPoint3 → ℂ) ξ := by
          simp only [Fin.sum_univ_three, hh0, hh1, hh2]
    _ = ((∑ j : Fin 3, F j : H3FourierComplexL2) : H3FourierPoint3 → ℂ) ξ :=
      hRepξ.symm
    _ = 0 := hZeroξ

/-! ## Preterminal Navier--Stokes specialization -/

/-- The classical preterminal incompressibility equation implies raw Fourier
    divergence-freeness at every H³-integrable measurable compatible snapshot
    strictly before the terminal time. -/
theorem velocityH3BaseFourierDivergenceFreeAt_of_preterminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    VelocityH3BaseFourierDivergenceFreeAt u t hInt hMeas := by
  rcases hNS with ⟨p, s⟩
  apply velocityH3BaseFourierDivergenceFreeAt_of_pointwise hFourier
  intro x
  have hxyz := s.incompressible_xyz ht x
  change
    spatial3.d xAxis (loggedVelocityComponent u t xAxis) x +
      (spatial3.d yAxis (loggedVelocityComponent u t yAxis) x +
        spatial3.d zAxis (loggedVelocityComponent u t zAxis) x) = 0 at hxyz
  simpa only [
    Fin.sum_univ_three,
    h3AxisOfFin3_zero, h3AxisOfFin3_one, h3AxisOfFin3_two,
    add_assoc
  ] using hxyz

/-- Consequently the lifted finite Leray multiplier fixes every genuinely
    encoded preterminal Navier--Stokes snapshot. -/
theorem h3SpectralFinLerayApply_velocityH3SpectralStateAt_eq_of_preterminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3SpectralFinLerayApply
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
      =
    velocityH3SpectralStateAt u t hInt hMeas hFourier := by
  exact
    h3SpectralFinLerayApply_velocityH3SpectralStateAt_eq_of_base
      hFourier
      (velocityH3BaseFourierDivergenceFreeAt_of_preterminal
        hNS ht hFourier)

end

end Euclidean
end Bridge
end PrimeTensor
