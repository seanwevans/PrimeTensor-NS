import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Derivative.Transfer
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Hilbert realization of the canonical top-order radial tail

The sharp top-order radial tail is

    Tail₃(t,R)
      =
    ∫_{|D(ξ)| ≥ R} q(ξ)^4 Σⱼ |ûⱼ(t,ξ)|² dξ,

where `q = h3FourierGradientSquare`.

Instead of differentiating this set integral pointwise in frequency, package
each coordinate as the genuine Fourier `L²` state

    1_{|D| ≥ R} q² ûⱼ(t).

Its squared `L²` norm is exactly the corresponding coordinate contribution to
`Tail₃(t,R)`.  Summing the three coordinates gives an exact Hilbert-space
realization of the canonical tail.

This is the natural interface for the next temporal step: once the weighted
tail `L²` path has a strong derivative, Mathlib's Hilbert-space
`HasDerivAt.norm_sq` theorem differentiates the tail energy without any
pointwise-in-frequency temporal derivative or differentiation-under-the-
integral argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailHilbertState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalTopTailHilbertState :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## The global fourth-radial coordinate -/

/--
The raw Fourier velocity coordinate multiplied by `q²`.  Squaring its norm
produces the `q⁴ |ûⱼ|²` top-dissipation density.
-/
noncomputable def h3TerminalPhysicalTopDissipationFourthRadialComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
    *
  velocityH3BaseFourierAt
    u t hInt hMeas j ξ

/--
The fourth-radial coordinate belongs to Fourier `L²` on every strict
energy-class slice.
-/
theorem h3TerminalPhysicalTopDissipationFourthRadialComponent_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    MemLp
      (h3TerminalPhysicalTopDissipationFourthRadialComponent
        hH3 hClass ht j)
      2
      volume := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hVelocityMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let hFourier : VelocityH3FourierCompatibleAt u t hInt hVelocityMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  have hWeightMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ))
        volume := by

    exact
      Complex.continuous_ofReal.comp_aestronglyMeasurable
        (h3FourierGradientSquare_aestronglyMeasurable.pow 2)

  have hBaseMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          velocityH3BaseFourierAt
            u t hInt hVelocityMeas j ξ)
        volume :=
    (MeasureTheory.Lp.memLp
      (velocityH3BaseFourierAt
        u t hInt hVelocityMeas j)).aestronglyMeasurable

  have hFourthMeas :
      AEStronglyMeasurable
        (h3TerminalPhysicalTopDissipationFourthRadialComponent
          hH3 hClass ht j)
        volume := by

    change
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          velocityH3BaseFourierAt
            u t hInt hVelocityMeas j ξ)
        volume

    exact
      hWeightMeas.mul
        hBaseMeas

  rw [
    memLp_two_iff_integrable_sq_norm
      hFourthMeas
  ]

  have hDensity :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 4
            *
          ‖velocityH3BaseFourierAt
              u t hInt hVelocityMeas j ξ‖ ^ 2)
        volume :=
    h3Path_integrable_h3FourierGradientSquare_four_mul_base_norm_sq
      hH3 hClass ht hInt hVelocityMeas hFourier j

  refine
    hDensity.congr ?_

  filter_upwards with ξ

  unfold
    h3TerminalPhysicalTopDissipationFourthRadialComponent

  dsimp only

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        2),
    mul_pow
  ]

  ring

/-! ## Sharp radial-tail coordinate as an `L²` state -/

/--
One coordinate of the canonical sharp top-dissipation tail, as a genuine
Fourier `L²` element.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailComponentL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow R)ᶜ
  let f : H3FourierPoint3 → ℂ :=
    h3TerminalPhysicalTopDissipationFourthRadialComponent
      hH3 hClass ht j
  let hf : MemLp f 2 volume :=
    h3TerminalPhysicalTopDissipationFourthRadialComponent_memLp2
      hH3 hClass ht j
  let hTail :
      MemLp (S.indicator f) 2 volume :=
    MeasureTheory.MemLp.indicator
      (measurableSet_h3TerminalRadialFrequencyBelow R).compl
      hf
  hTail.toLp
    (S.indicator f)

/--
The `L²` tail component has the expected sharp weighted representative almost
everywhere.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailComponentL2At_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ)
    (j : Fin 3) :
    (
      (h3TerminalPhysicalTopDissipationRadialTailComponentL2At
        hH3 hClass ht R j :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[volume]
    (
      (h3TerminalRadialFrequencyBelow R)ᶜ.indicator
        (h3TerminalPhysicalTopDissipationFourthRadialComponent
          hH3 hClass ht j)
    ) := by

  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow R)ᶜ

  let f : H3FourierPoint3 → ℂ :=
    h3TerminalPhysicalTopDissipationFourthRadialComponent
      hH3 hClass ht j

  let hf : MemLp f 2 volume :=
    h3TerminalPhysicalTopDissipationFourthRadialComponent_memLp2
      hH3 hClass ht j

  let hS : MeasurableSet S :=
    (measurableSet_h3TerminalRadialFrequencyBelow R).compl

  let hTail : MemLp (S.indicator f) 2 volume :=
    MeasureTheory.MemLp.indicator hS hf

  change
    ((hTail.toLp (S.indicator f) : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    S.indicator f

  exact
    MeasureTheory.MemLp.coeFn_toLp
      hTail

/-! ## Exact norm-square identity -/

/--
The squared `L²` norm of one sharp-tail component is exactly that coordinate's
localized `q⁴ |ûⱼ|²` mass.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationRadialTailComponentL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ)
    (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationRadialTailComponentL2At
        hH3 hClass ht R j‖ ^ 2
      =
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes htAbs
    ∫ ξ in (h3TerminalRadialFrequencyBelow R)ᶜ,
      h3FourierGradientSquare ξ ^ 4
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂volume := by

  let S : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow R)ᶜ

  let f : H3FourierPoint3 → ℂ :=
    h3TerminalPhysicalTopDissipationFourthRadialComponent
      hH3 hClass ht j

  let F : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationRadialTailComponentL2At
      hH3 hClass ht R j

  have hFAE :
      ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      S.indicator f := by

    dsimp only [F, S, f]

    exact
      h3TerminalPhysicalTopDissipationRadialTailComponentL2At_ae
        hH3 hClass ht R j

  rw [
    h3FourierComplexL2_norm_sq_eq_integral_norm_sq
  ]

  rw [
    ← integral_indicator
      (measurableSet_h3TerminalRadialFrequencyBelow R).compl
  ]

  apply integral_congr_ae

  filter_upwards [hFAE] with ξ hξ

  rw [hξ]

  by_cases hξS :
      ξ ∈ S

  · rw [
      Set.indicator_of_mem hξS,
      Set.indicator_of_mem hξS
    ]

    unfold f
    unfold
      h3TerminalPhysicalTopDissipationFourthRadialComponent

    dsimp only

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg
        (pow_nonneg
          (h3FourierGradientSquare_nonneg ξ)
          2),
      mul_pow
    ]

    ring

  · rw [
      Set.indicator_of_notMem hξS,
      Set.indicator_of_notMem hξS,
      norm_zero,
      zero_pow
    ]

    norm_num

/-! ## Three-component Hilbert realization -/

/--
The three-component sharp top-tail Hilbert state.
-/
noncomputable def h3TerminalPhysicalTopDissipationRadialTailL2StateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ) :
    Fin 3 → H3FourierComplexL2 :=
  fun j =>
    h3TerminalPhysicalTopDissipationRadialTailComponentL2At
      hH3 hClass ht R j

/--
The canonical top-order radial-tail mass is exactly the sum of the three
squared Hilbert norms of the sharp weighted tail coordinates.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailMassAt_eq_sum_norm_sq_tailL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℝ) :
    h3TerminalPhysicalTopDissipationRadialTailMassAt
        hH3 hClass t ht R
      =
    ∑ j : Fin 3,
      ‖h3TerminalPhysicalTopDissipationRadialTailL2StateAt
          hH3 hClass ht R j‖ ^ 2 := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  unfold
    h3TerminalPhysicalTopDissipationRadialTailMassAt
    h3TerminalPhysicalTopDissipationSetMassAt

  dsimp only

  unfold
    velocityH3FourierMassDensityAt

  simp_rw [
    Finset.mul_sum
  ]

  have hEach :
      ∀ j : Fin 3,
        IntegrableOn
          (fun ξ : H3FourierPoint3 =>
            h3FourierGradientSquare ξ ^ 4
              *
            ‖velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2)
          (h3TerminalRadialFrequencyBelow R)ᶜ
          volume := by

    intro j

    exact
      (
        h3Path_integrable_h3FourierGradientSquare_four_mul_base_norm_sq
          hH3
          hClass
          ht
          hInt
          hMeas
          (velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
            hH3.navier_stokes
            htAbs
            hInt)
          j
      ).integrableOn

  rw [
    integral_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hEach j)
  ]

  apply Finset.sum_congr rfl

  intro j hj

  symm

  exact
    norm_sq_h3TerminalPhysicalTopDissipationRadialTailComponentL2At
      hH3 hClass ht R j

end

end Euclidean
end Bridge
end PrimeTensor
