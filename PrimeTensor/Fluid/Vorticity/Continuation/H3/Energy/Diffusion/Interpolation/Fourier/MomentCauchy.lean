import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.MomentDensity

/-!
# H³ Fourier moment interpolation by two Cauchy--Schwarz steps

Write

    S(ξ) = Σⱼ ‖ûⱼ(ξ)‖²,
    q(ξ) = h3FourierGradientSquare ξ,

and

    M₀ = ∫ S,
    M₂ = ∫ q² S,
    M₃ = ∫ q³ S,
    M₄ = ∫ q⁴ S.

All four densities are integrable by `MomentDensity`.

Apply `2,2` Hölder twice:

    M₂
      = ∫ (√S) (q² √S)
      ≤ M₀^(1/2) M₄^(1/2),

    M₃
      = ∫ (q √S) (q² √S)
      ≤ M₂^(1/2) M₄^(1/2).

Squaring gives

    M₂² ≤ M₀ M₄,
    M₃² ≤ M₂ M₄,

and eliminating `M₂` gives the division-free polynomial estimate

    M₃⁴ ≤ M₀ M₄³.

Finally the exact radial identities transport this to physical variables:

    E₃(t)⁴ ≤ E₀(t) D₃(t)³.

This is a standard Fourier moment interpolation inequality.  It is neutral
with respect to continuation versus singularity: it quantifies how large the
top dissipation must be if the third H³ block becomes large.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3InterpolationMomentCauchy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3InterpolationMomentCauchy :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Half-power normalization -/

/-- For a nonnegative real number, the product of its two half powers is the
number itself. -/
lemma h3_halfPower_mul_self
    (x : ℝ)
    (hx : 0 ≤ x) :
    x ^ (1 / (2 : ℝ)) * x ^ (1 / (2 : ℝ))
      =
    x := by

  rw [
    ← Real.rpow_add_of_nonneg
        hx
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))
  ]

  norm_num

/-! ## Moment nonnegativity -/

theorem velocityH3FourierZerothRadialMomentAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    0 ≤ velocityH3FourierZerothRadialMomentAt
      u t hInt hMeas := by

  rw [
    velocityH3FourierZerothRadialMomentAt_eq_integral_massDensity
      hInt hMeas
  ]

  exact
    integral_nonneg
      (fun ξ =>
        velocityH3FourierMassDensityAt_nonneg
          u t hInt hMeas ξ)

theorem velocityH3FourierSecondRadialMomentAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    0 ≤ velocityH3FourierSecondRadialMomentAt
      u t hInt hMeas := by

  rw [
    velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier
  ]

  exact
    integral_nonneg
      (fun ξ => by
        have hq :
            0 ≤ h3FourierGradientSquare ξ :=
          h3FourierGradientSquare_nonneg ξ
        have hS :
            0 ≤ velocityH3FourierMassDensityAt
              u t hInt hMeas ξ :=
          velocityH3FourierMassDensityAt_nonneg
            u t hInt hMeas ξ
        positivity)

theorem velocityH3FourierThirdRadialMomentAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    0 ≤ velocityH3FourierThirdRadialMomentAt
      u t hInt hMeas := by

  rw [
    velocityH3FourierThirdRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier
  ]

  exact
    integral_nonneg
      (fun ξ => by
        have hq :
            0 ≤ h3FourierGradientSquare ξ :=
          h3FourierGradientSquare_nonneg ξ
        have hS :
            0 ≤ velocityH3FourierMassDensityAt
              u t hInt hMeas ξ :=
          velocityH3FourierMassDensityAt_nonneg
            u t hInt hMeas ξ
        positivity)

theorem h3Path_velocityH3FourierFourthRadialMomentAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    0 ≤ velocityH3FourierFourthRadialMomentAt
      u t hInt hMeas := by

  rw [
    h3Path_velocityH3FourierFourthRadialMomentAt_eq_integral_massDensity
      hH3 hClass ht hInt hMeas hFourier
  ]

  exact
    integral_nonneg
      (fun ξ => by
        have hq :
            0 ≤ h3FourierGradientSquare ξ :=
          h3FourierGradientSquare_nonneg ξ
        have hS :
            0 ≤ velocityH3FourierMassDensityAt
              u t hInt hMeas ξ :=
          velocityH3FourierMassDensityAt_nonneg
            u t hInt hMeas ξ
        positivity)

/-! ## Common square-root factors -/

theorem velocityH3FourierMassSqrt_aestronglyMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    AEStronglyMeasurable
      (fun ξ : H3FourierPoint3 =>
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ))
      volume := by

  exact
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (velocityH3FourierMassDensityAt_integrable
        u t hInt hMeas).aestronglyMeasurable

theorem h3FourierGradientSquare_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ)
      volume := by

  unfold h3FourierGradientSquare
  fun_prop

/-! ## L² factors for the Cauchy steps -/

theorem velocityH3FourierMassSqrt_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ))
      2
      volume := by

  have hMeasSqrt :=
    velocityH3FourierMassSqrt_aestronglyMeasurable
      hInt hMeas

  rw [
    memLp_two_iff_integrable_sq
      hMeasSqrt
  ]

  refine
    (velocityH3FourierMassDensityAt_integrable
      u t hInt hMeas).congr ?_

  filter_upwards with ξ

  exact
    (Real.sq_sqrt
      (velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ)).symm

theorem velocityH3FourierQMulMassSqrt_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ))
      2
      volume := by

  have hMeasFactor :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ))
        volume :=
    h3FourierGradientSquare_aestronglyMeasurable.mul
      (velocityH3FourierMassSqrt_aestronglyMeasurable
        hInt hMeas)

  rw [
    memLp_two_iff_integrable_sq
      hMeasFactor
  ]

  refine
    (velocityH3FourierSecondAggregateDensity_integrable
      hInt hMeas hFourier).congr ?_

  filter_upwards with ξ

  have hS :
      0 ≤ velocityH3FourierMassDensityAt
        u t hInt hMeas ξ :=
    velocityH3FourierMassDensityAt_nonneg
      u t hInt hMeas ξ

  rw [mul_pow, Real.sq_sqrt hS]

theorem velocityH3FourierQSqMulMassSqrt_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 2
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ))
      2
      volume := by

  have hMeasFactor :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 2
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ))
        volume :=
    (h3FourierGradientSquare_aestronglyMeasurable.pow 2).mul
      (velocityH3FourierMassSqrt_aestronglyMeasurable
        hInt hMeas)

  rw [
    memLp_two_iff_integrable_sq
      hMeasFactor
  ]

  refine
    (h3Path_velocityH3FourierFourthAggregateDensity_integrable
      hH3 hClass ht hInt hMeas hFourier).congr ?_

  filter_upwards with ξ

  have hS :
      0 ≤ velocityH3FourierMassDensityAt
        u t hInt hMeas ξ :=
    velocityH3FourierMassDensityAt_nonneg
      u t hInt hMeas ξ

  rw [mul_pow, Real.sq_sqrt hS]

  ring

/-! ## First Cauchy step: M₂² ≤ M₀ M₄ -/

theorem velocityH3FourierSecondRadialMomentAt_le_halfPowers
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierSecondRadialMomentAt
        u t hInt hMeas
      ≤
    velocityH3FourierZerothRadialMomentAt
        u t hInt hMeas ^ (1 / (2 : ℝ))
      *
    velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas ^ (1 / (2 : ℝ)) := by

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      Real.sqrt
        (velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)

  let g : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 2
        *
      Real.sqrt
        (velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)

  have hf : MemLp f 2 volume := by
    dsimp only [f]
    exact
      velocityH3FourierMassSqrt_memLp2
        hInt hMeas

  have hg : MemLp g 2 volume := by
    dsimp only [g]
    exact
      velocityH3FourierQSqMulMassSqrt_memLp2
        hH3 hClass ht hInt hMeas hFourier

  have hf_nonneg :
      0 ≤ᵐ[volume] f := by
    filter_upwards with ξ
    dsimp only [f]
    exact Real.sqrt_nonneg _

  have hg_nonneg :
      0 ≤ᵐ[volume] g := by
    filter_upwards with ξ
    dsimp only [g]
    have hq :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ
    have hsqrt :
        0 ≤ Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ) :=
      Real.sqrt_nonneg _
    positivity

  have hTwo :
      ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    norm_num

  have hf' :
      MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa [hTwo] using hf

  have hg' :
      MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa [hTwo] using hg

  have hCauchy :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume)
      (p := (2 : ℝ))
      (q := (2 : ℝ))
      (f := f)
      (g := g)
      Real.HolderConjugate.two_two
      hf_nonneg
      hg_nonneg
      hf'
      hg'

  dsimp only [f, g] at hCauchy

  have hLeft :
      (∫ ξ : H3FourierPoint3,
        Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
          *
        (
          h3FourierGradientSquare ξ ^ 2
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        )
        ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 2
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ
        ∂volume := by

    apply integral_congr_ae
    filter_upwards with ξ

    have hS :
        0 ≤ velocityH3FourierMassDensityAt
          u t hInt hMeas ξ :=
      velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ

    calc
      Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
          *
        (
          h3FourierGradientSquare ξ ^ 2
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        )
          =
        h3FourierGradientSquare ξ ^ 2
          *
        (
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        ) ^ 2 := by
          ring

      _ =
        h3FourierGradientSquare ξ ^ 2
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ := by
          rw [Real.sq_sqrt hS]

  have hRight0 :
      (∫ ξ : H3FourierPoint3,
        (Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)) ^ (2 : ℝ)
        ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ
        ∂volume := by

    apply integral_congr_ae
    filter_upwards with ξ

    have hS :
        0 ≤ velocityH3FourierMassDensityAt
          u t hInt hMeas ξ :=
      velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ

    calc
      (Real.sqrt
        (velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)) ^ (2 : ℝ)
          =
        (Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)) ^ (2 : ℕ) := by
            exact
              Real.rpow_natCast
                (Real.sqrt
                  (velocityH3FourierMassDensityAt
                    u t hInt hMeas ξ))
                2

      _ =
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ :=
        Real.sq_sqrt hS

  have hRight4 :
      (∫ ξ : H3FourierPoint3,
        (
          h3FourierGradientSquare ξ ^ 2
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        ) ^ (2 : ℝ)
        ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 4
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ
        ∂volume := by

    apply integral_congr_ae
    filter_upwards with ξ

    have hS :
        0 ≤ velocityH3FourierMassDensityAt
          u t hInt hMeas ξ :=
      velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ

    calc
      (
        h3FourierGradientSquare ξ ^ 2
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      ) ^ (2 : ℝ)
          =
      (
        h3FourierGradientSquare ξ ^ 2
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      ) ^ (2 : ℕ) := by
        exact
          Real.rpow_natCast
            (
              h3FourierGradientSquare ξ ^ 2
                *
              Real.sqrt
                (velocityH3FourierMassDensityAt
                  u t hInt hMeas ξ)
            )
            2

      _ =
        h3FourierGradientSquare ξ ^ 4
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ := by
        rw [mul_pow, Real.sq_sqrt hS]
        ring

  rw [hLeft, hRight0, hRight4] at hCauchy

  rw [
    ← velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier,
    ← velocityH3FourierZerothRadialMomentAt_eq_integral_massDensity
      hInt hMeas,
    ← h3Path_velocityH3FourierFourthRadialMomentAt_eq_integral_massDensity
      hH3 hClass ht hInt hMeas hFourier
  ] at hCauchy

  exact hCauchy

theorem velocityH3FourierSecondRadialMomentAt_sq_le_zero_mul_fourth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierSecondRadialMomentAt
        u t hInt hMeas ^ 2
      ≤
    velocityH3FourierZerothRadialMomentAt
        u t hInt hMeas
      *
    velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas := by

  let M0 :=
    velocityH3FourierZerothRadialMomentAt
      u t hInt hMeas

  let M2 :=
    velocityH3FourierSecondRadialMomentAt
      u t hInt hMeas

  let M4 :=
    velocityH3FourierFourthRadialMomentAt
      u t hInt hMeas

  have hM0 :
      0 ≤ M0 := by
    dsimp only [M0]
    exact
      velocityH3FourierZerothRadialMomentAt_nonneg
        hInt hMeas

  have hM2 :
      0 ≤ M2 := by
    dsimp only [M2]
    exact
      velocityH3FourierSecondRadialMomentAt_nonneg
        hInt hMeas hFourier

  have hM4 :
      0 ≤ M4 := by
    dsimp only [M4]
    exact
      h3Path_velocityH3FourierFourthRadialMomentAt_nonneg
        hH3 hClass ht hInt hMeas hFourier

  have hRoot :
      M2
        ≤
      M0 ^ (1 / (2 : ℝ))
        *
      M4 ^ (1 / (2 : ℝ)) := by
    dsimp only [M0, M2, M4]
    exact
      velocityH3FourierSecondRadialMomentAt_le_halfPowers
        hH3 hClass ht hInt hMeas hFourier

  have hRoot0 :
      M0 ^ (1 / (2 : ℝ))
        *
      M0 ^ (1 / (2 : ℝ))
        =
      M0 :=
    h3_halfPower_mul_self M0 hM0

  have hRoot4 :
      M4 ^ (1 / (2 : ℝ))
        *
      M4 ^ (1 / (2 : ℝ))
        =
      M4 :=
    h3_halfPower_mul_self M4 hM4

  have hSquare :=
    mul_self_le_mul_self hM2 hRoot

  dsimp only [M0, M2, M4] at hRoot0 hRoot4 hSquare ⊢

  calc
    velocityH3FourierSecondRadialMomentAt
        u t hInt hMeas ^ 2
        =
      velocityH3FourierSecondRadialMomentAt
          u t hInt hMeas
        *
      velocityH3FourierSecondRadialMomentAt
          u t hInt hMeas := by
      ring

    _ ≤
      (
        velocityH3FourierZerothRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
          *
        velocityH3FourierFourthRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
      )
        *
      (
        velocityH3FourierZerothRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
          *
        velocityH3FourierFourthRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
      ) :=
      hSquare

    _ =
      velocityH3FourierZerothRadialMomentAt
          u t hInt hMeas
        *
      velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas := by
      rw [show
        (
          velocityH3FourierZerothRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        )
          *
        (
          velocityH3FourierZerothRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        )
          =
        (
          velocityH3FourierZerothRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierZerothRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        )
          *
        (
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        ) by ring]
      rw [hRoot0, hRoot4]

/-! ## Second Cauchy step: M₃² ≤ M₂ M₄ -/

theorem velocityH3FourierThirdRadialMomentAt_le_halfPowers
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierThirdRadialMomentAt
        u t hInt hMeas
      ≤
    velocityH3FourierSecondRadialMomentAt
        u t hInt hMeas ^ (1 / (2 : ℝ))
      *
    velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas ^ (1 / (2 : ℝ)) := by

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ
        *
      Real.sqrt
        (velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)

  let g : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 2
        *
      Real.sqrt
        (velocityH3FourierMassDensityAt
          u t hInt hMeas ξ)

  have hf : MemLp f 2 volume := by
    dsimp only [f]
    exact
      velocityH3FourierQMulMassSqrt_memLp2
        hInt hMeas hFourier

  have hg : MemLp g 2 volume := by
    dsimp only [g]
    exact
      velocityH3FourierQSqMulMassSqrt_memLp2
        hH3 hClass ht hInt hMeas hFourier

  have hf_nonneg :
      0 ≤ᵐ[volume] f := by
    filter_upwards with ξ
    dsimp only [f]
    have hq :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ
    have hsqrt :
        0 ≤ Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ) :=
      Real.sqrt_nonneg _
    positivity

  have hg_nonneg :
      0 ≤ᵐ[volume] g := by
    filter_upwards with ξ
    dsimp only [g]
    have hq :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ
    have hsqrt :
        0 ≤ Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ) :=
      Real.sqrt_nonneg _
    positivity

  have hTwo :
      ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    norm_num

  have hf' :
      MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa [hTwo] using hf

  have hg' :
      MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa [hTwo] using hg

  have hCauchy :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume)
      (p := (2 : ℝ))
      (q := (2 : ℝ))
      (f := f)
      (g := g)
      Real.HolderConjugate.two_two
      hf_nonneg
      hg_nonneg
      hf'
      hg'

  dsimp only [f, g] at hCauchy

  have hLeft :
      (∫ ξ : H3FourierPoint3,
        (
          h3FourierGradientSquare ξ
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        )
          *
        (
          h3FourierGradientSquare ξ ^ 2
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        )
        ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 3
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ
        ∂volume := by

    apply integral_congr_ae
    filter_upwards with ξ

    have hS :
        0 ≤ velocityH3FourierMassDensityAt
          u t hInt hMeas ξ :=
      velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ

    calc
      (
        h3FourierGradientSquare ξ
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      )
        *
      (
        h3FourierGradientSquare ξ ^ 2
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      )
          =
        h3FourierGradientSquare ξ ^ 3
          *
        (
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        ) ^ 2 := by
          ring

      _ =
        h3FourierGradientSquare ξ ^ 3
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ := by
          rw [Real.sq_sqrt hS]

  have hRight2 :
      (∫ ξ : H3FourierPoint3,
        (
          h3FourierGradientSquare ξ
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        ) ^ (2 : ℝ)
        ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 2
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ
        ∂volume := by

    apply integral_congr_ae
    filter_upwards with ξ

    have hS :
        0 ≤ velocityH3FourierMassDensityAt
          u t hInt hMeas ξ :=
      velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ

    calc
      (
        h3FourierGradientSquare ξ
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      ) ^ (2 : ℝ)
          =
      (
        h3FourierGradientSquare ξ
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      ) ^ (2 : ℕ) := by
        exact
          Real.rpow_natCast
            (
              h3FourierGradientSquare ξ
                *
              Real.sqrt
                (velocityH3FourierMassDensityAt
                  u t hInt hMeas ξ)
            )
            2

      _ =
        h3FourierGradientSquare ξ ^ 2
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ := by
        rw [mul_pow, Real.sq_sqrt hS]

  have hRight4 :
      (∫ ξ : H3FourierPoint3,
        (
          h3FourierGradientSquare ξ ^ 2
            *
          Real.sqrt
            (velocityH3FourierMassDensityAt
              u t hInt hMeas ξ)
        ) ^ (2 : ℝ)
        ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 4
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ
        ∂volume := by

    apply integral_congr_ae
    filter_upwards with ξ

    have hS :
        0 ≤ velocityH3FourierMassDensityAt
          u t hInt hMeas ξ :=
      velocityH3FourierMassDensityAt_nonneg
        u t hInt hMeas ξ

    calc
      (
        h3FourierGradientSquare ξ ^ 2
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      ) ^ (2 : ℝ)
          =
      (
        h3FourierGradientSquare ξ ^ 2
          *
        Real.sqrt
          (velocityH3FourierMassDensityAt
            u t hInt hMeas ξ)
      ) ^ (2 : ℕ) := by
        exact
          Real.rpow_natCast
            (
              h3FourierGradientSquare ξ ^ 2
                *
              Real.sqrt
                (velocityH3FourierMassDensityAt
                  u t hInt hMeas ξ)
            )
            2

      _ =
        h3FourierGradientSquare ξ ^ 4
          *
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ := by
        rw [mul_pow, Real.sq_sqrt hS]
        ring

  rw [hLeft, hRight2, hRight4] at hCauchy

  rw [
    ← velocityH3FourierThirdRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier,
    ← velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
      hInt hMeas hFourier,
    ← h3Path_velocityH3FourierFourthRadialMomentAt_eq_integral_massDensity
      hH3 hClass ht hInt hMeas hFourier
  ] at hCauchy

  exact hCauchy

theorem velocityH3FourierThirdRadialMomentAt_sq_le_second_mul_fourth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierThirdRadialMomentAt
        u t hInt hMeas ^ 2
      ≤
    velocityH3FourierSecondRadialMomentAt
        u t hInt hMeas
      *
    velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas := by

  let M2 :=
    velocityH3FourierSecondRadialMomentAt
      u t hInt hMeas

  let M3 :=
    velocityH3FourierThirdRadialMomentAt
      u t hInt hMeas

  let M4 :=
    velocityH3FourierFourthRadialMomentAt
      u t hInt hMeas

  have hM2 :
      0 ≤ M2 := by
    dsimp only [M2]
    exact
      velocityH3FourierSecondRadialMomentAt_nonneg
        hInt hMeas hFourier

  have hM3 :
      0 ≤ M3 := by
    dsimp only [M3]
    exact
      velocityH3FourierThirdRadialMomentAt_nonneg
        hInt hMeas hFourier

  have hM4 :
      0 ≤ M4 := by
    dsimp only [M4]
    exact
      h3Path_velocityH3FourierFourthRadialMomentAt_nonneg
        hH3 hClass ht hInt hMeas hFourier

  have hRoot :
      M3
        ≤
      M2 ^ (1 / (2 : ℝ))
        *
      M4 ^ (1 / (2 : ℝ)) := by
    dsimp only [M2, M3, M4]
    exact
      velocityH3FourierThirdRadialMomentAt_le_halfPowers
        hH3 hClass ht hInt hMeas hFourier

  have hRoot2 :
      M2 ^ (1 / (2 : ℝ))
        *
      M2 ^ (1 / (2 : ℝ))
        =
      M2 :=
    h3_halfPower_mul_self M2 hM2

  have hRoot4 :
      M4 ^ (1 / (2 : ℝ))
        *
      M4 ^ (1 / (2 : ℝ))
        =
      M4 :=
    h3_halfPower_mul_self M4 hM4

  have hSquare :=
    mul_self_le_mul_self hM3 hRoot

  dsimp only [M2, M3, M4] at hRoot2 hRoot4 hSquare ⊢

  calc
    velocityH3FourierThirdRadialMomentAt
        u t hInt hMeas ^ 2
        =
      velocityH3FourierThirdRadialMomentAt
          u t hInt hMeas
        *
      velocityH3FourierThirdRadialMomentAt
          u t hInt hMeas := by
      ring

    _ ≤
      (
        velocityH3FourierSecondRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
          *
        velocityH3FourierFourthRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
      )
        *
      (
        velocityH3FourierSecondRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
          *
        velocityH3FourierFourthRadialMomentAt
            u t hInt hMeas ^ (1 / (2 : ℝ))
      ) :=
      hSquare

    _ =
      velocityH3FourierSecondRadialMomentAt
          u t hInt hMeas
        *
      velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas := by
      rw [show
        (
          velocityH3FourierSecondRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        )
          *
        (
          velocityH3FourierSecondRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        )
          =
        (
          velocityH3FourierSecondRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierSecondRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        )
          *
        (
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
            *
          velocityH3FourierFourthRadialMomentAt
              u t hInt hMeas ^ (1 / (2 : ℝ))
        ) by ring]
      rw [hRoot2, hRoot4]

/-! ## Eliminate M₂ -/

/--
Exact polynomial moment interpolation:

    M₃⁴ ≤ M₀ M₄³.
-/
theorem velocityH3FourierThirdRadialMomentAt_pow_four_le_zero_mul_fourth_pow_three
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3FourierThirdRadialMomentAt
        u t hInt hMeas ^ 4
      ≤
    velocityH3FourierZerothRadialMomentAt
        u t hInt hMeas
      *
    velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas ^ 3 := by

  let M0 :=
    velocityH3FourierZerothRadialMomentAt
      u t hInt hMeas

  let M2 :=
    velocityH3FourierSecondRadialMomentAt
      u t hInt hMeas

  let M3 :=
    velocityH3FourierThirdRadialMomentAt
      u t hInt hMeas

  let M4 :=
    velocityH3FourierFourthRadialMomentAt
      u t hInt hMeas

  have h23 :
      M3 ^ 2 ≤ M2 * M4 := by
    dsimp only [M2, M3, M4]
    exact
      velocityH3FourierThirdRadialMomentAt_sq_le_second_mul_fourth
        hH3 hClass ht hInt hMeas hFourier

  have h02 :
      M2 ^ 2 ≤ M0 * M4 := by
    dsimp only [M0, M2, M4]
    exact
      velocityH3FourierSecondRadialMomentAt_sq_le_zero_mul_fourth
        hH3 hClass ht hInt hMeas hFourier

  have h23sq :
      (M3 ^ 2) * (M3 ^ 2)
        ≤
      (M2 * M4) * (M2 * M4) :=
    mul_self_le_mul_self
      (sq_nonneg M3)
      h23

  have hScale :
      M2 ^ 2 * M4 ^ 2
        ≤
      (M0 * M4) * M4 ^ 2 :=
    mul_le_mul_of_nonneg_right
      h02
      (sq_nonneg M4)

  dsimp only [M0, M2, M3, M4] at h23sq hScale ⊢

  calc
    velocityH3FourierThirdRadialMomentAt
        u t hInt hMeas ^ 4
        =
      (
        velocityH3FourierThirdRadialMomentAt
          u t hInt hMeas ^ 2
      )
        *
      (
        velocityH3FourierThirdRadialMomentAt
          u t hInt hMeas ^ 2
      ) := by
      ring

    _ ≤
      (
        velocityH3FourierSecondRadialMomentAt
          u t hInt hMeas
          *
        velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas
      )
        *
      (
        velocityH3FourierSecondRadialMomentAt
          u t hInt hMeas
          *
        velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas
      ) :=
      h23sq

    _ =
      velocityH3FourierSecondRadialMomentAt
          u t hInt hMeas ^ 2
        *
      velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas ^ 2 := by
      ring

    _ ≤
      (
        velocityH3FourierZerothRadialMomentAt
          u t hInt hMeas
          *
        velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas
      )
        *
      velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas ^ 2 :=
      hScale

    _ =
      velocityH3FourierZerothRadialMomentAt
          u t hInt hMeas
        *
      velocityH3FourierFourthRadialMomentAt
          u t hInt hMeas ^ 3 := by
      ring

/-! ## Physical H³ interpolation -/

/--
Physical top-order H³ interpolation on every strict energy-class slice:

    E₃(t)⁴ ≤ E₀(t) D₃(t)³.
-/
theorem velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Energy3At u t ^ 4
      ≤
    velocityH3Energy0At u t
      *
    velocityH3Dissipation3At u t ^ 3 := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  let hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  let hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      htAbs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      htAbs
      hInt

  have hMoment :=
    velocityH3FourierThirdRadialMomentAt_pow_four_le_zero_mul_fourth_pow_three
      hH3
      hClass
      ht
      hInt
      hMeas
      hFourier

  have h0 :=
    velocityH3Energy0At_eq_fourierZerothRadialMoment
      hInt hMeas

  have h3 :=
    velocityH3Energy3At_eq_fourierThirdRadialMoment
      hInt hMeas hFourier

  have h4 :=
    velocityH3Dissipation3At_eq_fourierFourthRadialMoment
      hH3 hClass ht hInt hMeas hFourier

  rw [h3, h0, h4]

  exact hMoment

end

end Euclidean
end Bridge
end PrimeTensor
