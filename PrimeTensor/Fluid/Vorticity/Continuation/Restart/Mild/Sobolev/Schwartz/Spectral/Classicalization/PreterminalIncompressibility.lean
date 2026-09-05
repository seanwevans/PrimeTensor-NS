import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.Fourier.Jet.Incompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Preterminal.Canonical.Energy.Restart.Closure
import PrimeTensor.Fluid.Vorticity.Preterminal.Equation

/-!
# Preterminal physical incompressibility enters the H³ spectral encoder

`FourierJetIncompressibility` isolated the last PDE-facing boundary needed by
the finite Leray theory:

    Σⱼ Fourier(∂ⱼ uⱼ) = 0    a.e.

For an interior slice of `LoggedPreterminalNavierStokesAdmissible`, this is not
an additional hypothesis.  `PreterminalNavierStokes3.incompressible_xyz`
already says pointwise that

    ∂ₓ uₓ + (∂ᵧ uᵧ + ∂𝓏 u𝓏) = 0.

The concrete H³ jet packages those three derivatives as real `L²` classes.
This file transports the pointwise equation through that packaging and through
the canonical scalar Plancherel transform.

The resulting chain is now completely closed:

* physical preterminal incompressibility;
* zero diagonal first-jet sum in real `L²`;
* zero diagonal first-jet Fourier sum;
* raw Fourier divergence-freeness by Fourier compatibility;
* weighted H³ spectral divergence-freeness;
* exact invariance under the finite Leray projector.

No new PDE assumption is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PreterminalSpectralIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PreterminalSpectralIncompressibility :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Additivity of the canonical scalar Plancherel bridge -/

/-- Transport from the project `Point3` carrier to the Euclidean Fourier
carrier respects addition exactly. -/
theorem h3ToFourierRealL2_add
    (f g : H3ScalarL2) :
    h3ToFourierRealL2 (f + g)
      =
    h3ToFourierRealL2 f + h3ToFourierRealL2 g := by
  unfold h3ToFourierRealL2
  exact
    (MeasureTheory.Lp.compMeasurePreserving
      (WithLp.ofLp : H3FourierPoint3 → Point3)
      (PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three))).map_add f g

/-- The canonical scalar Plancherel transform is additive. -/
theorem h3ScalarFourierL2_add
    (f g : H3ScalarL2) :
    h3ScalarFourierL2 (f + g)
      =
    h3ScalarFourierL2 f + h3ScalarFourierL2 g := by
  unfold h3ScalarFourierL2
  rw [h3ToFourierRealL2_add]
  rw [h3ComplexifyFourierL2_add]
  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).map_add _ _

/-- The canonical scalar Plancherel transform sends zero to zero. -/
@[simp]
theorem h3ScalarFourierL2_zero :
    h3ScalarFourierL2 (0 : H3ScalarL2)
      =
    (0 : H3FourierComplexL2) := by
  apply norm_eq_zero.mp
  rw [norm_h3ScalarFourierL2]
  simp

/-! ## Physical divergence in the concrete H³ jet -/

/-- Every concrete H³ `L²` jet coordinate represents its underlying scalar jet
field almost everywhere. -/
theorem velocityH3L2JetAt_ae_eq_jetField
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (a : H3JetIndex) :
    ((velocityH3L2JetAt u t hInt hMeas a : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    velocityH3JetFieldAt u t a := by
  unfold velocityH3L2JetAt
  dsimp only
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (velocityH3JetFieldAt_memLp2 hInt hMeas a)

/-- Physical preterminal incompressibility says that the three diagonal
first-derivative jet coordinates sum to zero as an actual real `L²` element. -/
theorem velocityH3L2DiagonalDivergenceFreeAt_of_loggedPreterminalNavierStokes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (0 : Fin 3))
      +
      (
        velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot1 (1 : Fin 3) (1 : Fin 3))
        +
        velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot1 (2 : Fin 3) (2 : Fin 3))
      )
      =
    (0 : H3ScalarL2) := by
  rcases hNS with ⟨p, hp⟩

  apply MeasureTheory.Lp.ext

  filter_upwards [
    MeasureTheory.Lp.coeFn_add
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (0 : Fin 3) (0 : Fin 3)))
      (
        velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot1 (1 : Fin 3) (1 : Fin 3))
        +
        velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot1 (2 : Fin 3) (2 : Fin 3))
      ),
    MeasureTheory.Lp.coeFn_add
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (1 : Fin 3) (1 : Fin 3)))
      (velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot1 (2 : Fin 3) (2 : Fin 3))),
    velocityH3L2JetAt_ae_eq_jetField
      hInt hMeas
      (h3JetSlot1 (0 : Fin 3) (0 : Fin 3)),
    velocityH3L2JetAt_ae_eq_jetField
      hInt hMeas
      (h3JetSlot1 (1 : Fin 3) (1 : Fin 3)),
    velocityH3L2JetAt_ae_eq_jetField
      hInt hMeas
      (h3JetSlot1 (2 : Fin 3) (2 : Fin 3)),
    MeasureTheory.Lp.coeFn_zero
      ℝ (2 : ENNReal) (volume : Measure Point3)
  ] with x hOuter hInner h0 h1 h2 hZero

  rw [hOuter]
  simp only [Pi.add_apply]
  rw [hInner]
  simp only [Pi.add_apply]
  rw [h0, h1, h2, hZero]

  change
    spatial3.d
          xAxis
          (fun y : Point3 =>
            (logSpaceTimeVectorField u t y).component xAxis)
          x
      +
        (
          spatial3.d
              yAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField u t y).component yAxis)
              x
          +
          spatial3.d
              zAxis
              (fun y : Point3 =>
                (logSpaceTimeVectorField u t y).component zAxis)
              x
        )
      =
    0

  exact
    hp.incompressible_xyz ht x

/-! ## Plancherel transport of physical divergence -/

/-- The physical preterminal divergence equation produces exactly the diagonal
Fourier-jet identity isolated by `FourierJetIncompressibility`. -/
theorem velocityH3FourierDiagonalDivergenceFreeAt_of_loggedPreterminalNavierStokes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    VelocityH3FourierDiagonalDivergenceFreeAt
      u t hInt hMeas := by
  have hL2 :=
    velocityH3L2DiagonalDivergenceFreeAt_of_loggedPreterminalNavierStokes
      hNS ht hInt hMeas

  have hFourierSum :=
    congrArg h3ScalarFourierL2 hL2

  rw [
    h3ScalarFourierL2_add,
    h3ScalarFourierL2_add,
    h3ScalarFourierL2_zero
  ] at hFourierSum

  let F0 : H3FourierComplexL2 :=
    velocityH3FourierJetAt u t hInt hMeas
      (h3JetSlot1 (0 : Fin 3) (0 : Fin 3))
  let F1 : H3FourierComplexL2 :=
    velocityH3FourierJetAt u t hInt hMeas
      (h3JetSlot1 (1 : Fin 3) (1 : Fin 3))
  let F2 : H3FourierComplexL2 :=
    velocityH3FourierJetAt u t hInt hMeas
      (h3JetSlot1 (2 : Fin 3) (2 : Fin 3))

  have hBundled :
      (F0 + F1) + F2 = 0 := by
    simpa [
      F0,
      F1,
      F2,
      velocityH3FourierJetAt,
      h3L2JetFourierApply,
      add_assoc
    ] using hFourierSum

  have hSumZero :
      ((((F0 + F1) + F2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun _ => 0) := by
    rw [hBundled]
    exact
      MeasureTheory.Lp.coeFn_zero
        ℂ (2 : ENNReal)
        (volume : Measure H3FourierPoint3)

  unfold VelocityH3FourierDiagonalDivergenceFreeAt
  simp only [Fin.sum_univ_three]

  change
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      (F0 ξ + F1 ξ) + F2 ξ = 0

  filter_upwards [
    MeasureTheory.Lp.coeFn_add F0 F1,
    MeasureTheory.Lp.coeFn_add (F0 + F1) F2,
    hSumZero
  ] with ξ hInner hOuter hZero

  rw [hOuter] at hZero
  simp only [Pi.add_apply] at hZero
  rw [hInner] at hZero
  simp only [Pi.add_apply] at hZero
  exact hZero

/-! ## Closed preterminal spectral incompressibility -/

/-- Every H³-integrable interior slice of a logged preterminal
Navier--Stokes solution has a divergence-free canonical weighted spectral
state.  Measurability and Fourier compatibility are generated from the same
preterminal `C³` structure, so no additional snapshot assumption remains. -/
theorem velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t) :
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hNS ht
    let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
      velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
        hNS ht hInt
    H3SpectralFinDivergenceFree
      (velocityH3SpectralStateAt
        u t hInt hMeas hFourier) := by
  dsimp only

  exact
    velocityH3SpectralStateAt_divergenceFree_of_fourierDiagonal
      (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
        hNS ht hInt)
      (velocityH3FourierDiagonalDivergenceFreeAt_of_loggedPreterminalNavierStokes
        hNS
        ht
        hInt
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hNS ht))

/-- The finite Leray projector therefore fixes every canonical H³ spectral
slice encoded from an interior preterminal Navier--Stokes state. -/
theorem h3SpectralFinLerayApply_velocityH3SpectralStateAt_eq_of_loggedPreterminalNavierStokes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t) :
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hNS ht
    let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
      velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
        hNS ht hInt
    h3SpectralFinLerayApply
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier)
      =
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier := by
  dsimp only

  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
        hNS ht hInt)

end
end Euclidean
end Bridge
end PrimeTensor
