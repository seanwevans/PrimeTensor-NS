import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Factors

/-!
# Split the terminal fourth-radial Hilbert pairing into physical PDE rates

The preceding checkpoints supplied:

* the exact combined restricted Hilbert-pairing integral;
* genuine strict-time Fourier `L²` factors `q³ û_j` and `q² F_j(U,U)`.

The existing physical fourth-radial state supplies `q² û_j ∈ L²`.
Therefore ordinary `L² × L² → L¹` Hilbert pairing gives separate
integrability of

    q⁵ |û_j|²

and

    q⁴ Re ⟪û_j, F_j(U,U)⟫.

This makes `integral_add` legitimate.  The componentwise combined integral can
then be split into the named diffusion and nonlinear-transfer pieces.  Finally
the three diffusion coordinates are recombined into the existing fifth-radial
mass definition, while the nonlinear coordinates already sum definitionally
to the named nonlinear transfer rate.

Thus the cutoff-independent fourth-radial Hilbert derivative now identifies
the concrete localized PDE rates outright.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedOldDerivativeSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-! ## Canonical `q² û_j` representative -/

/--
The physical fourth-radial `L²` state has the intrinsic canonical terminal
representative `q² û_j`.
-/
theorem h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae_gradientSquare
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (
      (
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass ht j :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
        *
      h3SpectralScalarRawFourierL2
        (U j) ξ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  let hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  have hRawEq :
      h3SpectralScalarRawFourierL2 (U j)
        =
      velocityH3BaseFourierAt
        u t hInt hMeas j := by

    dsimp only [U]

    unfold
      h3TerminalVelocitySpectralStateAt
      velocityH3SpectralStateAt

    rw [
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        hFourier j
    ]

  have hAt :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae
      hH3 hClass ht j

  filter_upwards [hAt] with ξ hξ

  rw [hξ]

  unfold
    h3TerminalPhysicalTopDissipationFourthRadialComponent

  change
    ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        velocityH3BaseFourierAt
          u t hInt hMeas j ξ
      =
    ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3SpectralScalarRawFourierL2
          (U j) ξ

  rw [hRawEq]

/-! ## Separate strict-time integrability -/

/--
The scalar coordinate diffusion density `q⁵ |û_j|²` is integrable at every
strict physical time.
-/
theorem integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 5
          *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  let X2 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass ht j

  obtain
    ⟨
      V3,
      F2,
      hV3,
      hF2
    ⟩ :=
    exists_h3TerminalPhysicalTopDissipationStrictTimeWeightedPDEFactors
      hH3 hClass ht j

  have hX2 :
      ((X2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3SpectralScalarRawFourierL2
          (U j) ξ) := by

    dsimp only [X2, U]

    exact
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae_gradientSquare
        hH3 hClass ht j

  have hV3' :
      ((V3 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        h3SpectralScalarRawFourierL2
          (U j) ξ) := by

    simpa only [htAbs, U] using hV3

  have hInner :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Complex.re
            (inner ℂ (X2 ξ) (V3 ξ)))
        (volume : Measure H3FourierPoint3) :=
    Complex.reCLM.integrable_comp
      (MeasureTheory.L2.integrable_inner X2 V3)

  refine
    hInner.congr ?_

  filter_upwards [hX2, hV3'] with ξ hXξ hVξ

  rw [hXξ, hVξ]

  let q : ℝ :=
    h3FourierGradientSquare ξ

  let z : ℂ :=
    h3SpectralScalarRawFourierL2
      (U j) ξ

  change
    Complex.re
      (
        inner ℂ
          (((q ^ 2 : ℝ) : ℂ) * z)
          (((q ^ 3 : ℝ) : ℂ) * z)
      )
      =
    q ^ 5 * ‖z‖ ^ 2

  have hComplex :
      inner ℂ
          (((q ^ 2 : ℝ) : ℂ) * z)
          (((q ^ 3 : ℝ) : ℂ) * z)
        =
      ((q ^ 5 : ℝ) : ℂ)
        *
      ((‖z‖ ^ 2 : ℝ) : ℂ) := by

    simp only [
      RCLike.inner_apply,
      map_mul,
      Complex.conj_ofReal
    ]

    have hz :
        z * (starRingEnd ℂ) z
          =
        ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      simpa using
        (RCLike.mul_conj z)

    rw [← hz]

    push_cast

    ring

  rw [hComplex]

  simp only [
    Complex.mul_re,
    Complex.ofReal_re,
    Complex.ofReal_im,
    mul_zero,
    sub_zero
  ]

/--
The scalar coordinate nonlinear density

    `q⁴ Re ⟪û_j, F_j(U,U)⟫`

is integrable at every strict physical time.
-/
theorem integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 4
          *
        (
          inner ℂ
            (h3SpectralScalarRawFourierL2
              (U j) ξ)
            (h3RawFinLerayOuterProductDivergence
              U U j ξ)
        ).re)
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  let X2 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass ht j

  obtain
    ⟨
      V3,
      F2,
      hV3,
      hF2
    ⟩ :=
    exists_h3TerminalPhysicalTopDissipationStrictTimeWeightedPDEFactors
      hH3 hClass ht j

  have hX2 :
      ((X2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3SpectralScalarRawFourierL2
          (U j) ξ) := by

    dsimp only [X2, U]

    exact
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae_gradientSquare
        hH3 hClass ht j

  have hF2' :
      ((F2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          U U j ξ) := by

    simpa only [htAbs, U] using hF2

  have hInner :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Complex.re
            (inner ℂ (X2 ξ) (F2 ξ)))
        (volume : Measure H3FourierPoint3) :=
    Complex.reCLM.integrable_comp
      (MeasureTheory.L2.integrable_inner X2 F2)

  refine
    hInner.congr ?_

  filter_upwards [hX2, hF2'] with ξ hXξ hFξ

  rw [hXξ, hFξ]

  let q : ℝ :=
    h3FourierGradientSquare ξ

  let z : ℂ :=
    h3SpectralScalarRawFourierL2
      (U j) ξ

  let f : ℂ :=
    h3RawFinLerayOuterProductDivergence
      U U j ξ

  change
    Complex.re
      (
        inner ℂ
          (((q ^ 2 : ℝ) : ℂ) * z)
          (((q ^ 2 : ℝ) : ℂ) * f)
      )
      =
    q ^ 4 * (inner ℂ z f).re

  have hComplex :
      inner ℂ
          (((q ^ 2 : ℝ) : ℂ) * z)
          (((q ^ 2 : ℝ) : ℂ) * f)
        =
      ((q ^ 4 : ℝ) : ℂ)
        *
      inner ℂ z f := by

    simp only [
      RCLike.inner_apply,
      map_mul,
      Complex.conj_ofReal
    ]

    push_cast

    ring

  rw [hComplex]

  simp only [
    Complex.mul_re,
    Complex.ofReal_re,
    Complex.ofReal_im,
    zero_mul,
    sub_zero
  ]

/-! ## Componentwise split -/

/--
For one coordinate, the exact restricted Hilbert pairing splits into the
separately meaningful diffusion integral and the already-named nonlinear
coordinate transfer rate.
-/
theorem h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_two_mul_inner_derivativeValue_eq_diffusion_plus_nonlinearCoordinate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (W : H3FourierComplexL2)
    (hW :
      HasDerivAt
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j)
        W
        t) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    2 *
      inner ℝ
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
            hH3 hClass R j t
        )
        (
          h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
            R W
        )
      =
    (-2 : ℝ)
      *
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 5
        *
      ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
      ∂(
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow R)ᶜ
      )
      +
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
      hH3 hClass ht R j := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hPair :=
    h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_two_mul_inner_derivativeValue_eq_unitPDE_integral
      (R := R)
      hH3 hClass ht j W hW

  have hDiffFull :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by

    simpa only [htAbs, U] using
      (
        integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
          hH3 hClass ht j
      )

  have hNonlinFull :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 4
            *
          (
            inner ℂ
              (h3SpectralScalarRawFourierL2
                (U j) ξ)
              (h3RawFinLerayOuterProductDivergence
                U U j ξ)
          ).re)
        (volume : Measure H3FourierPoint3) := by

    simpa only [htAbs, U] using
      (
        integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
          hH3 hClass ht j
      )

  have hDiff :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2)
        (
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) :=
    hDiffFull.mono_measure
      Measure.restrict_le_self

  have hNonlin :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 4
            *
          (
            inner ℂ
              (h3SpectralScalarRawFourierL2
                (U j) ξ)
              (h3RawFinLerayOuterProductDivergence
                U U j ξ)
          ).re)
        (
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) :=
    hNonlinFull.mono_measure
      Measure.restrict_le_self

  have hDiffSigned :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (-2 : ℝ)
            *
          (
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
          ))
        (
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) :=
    hDiff.const_mul (-2 : ℝ)

  have hNonlinSigned :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (-2 : ℝ)
            *
          (
            h3FourierGradientSquare ξ ^ 4
              *
            (
              inner ℂ
                (h3SpectralScalarRawFourierL2
                  (U j) ξ)
                (h3RawFinLerayOuterProductDivergence
                  U U j ξ)
            ).re
          ))
        (
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) :=
    hNonlin.const_mul (-2 : ℝ)

  have hPair' :
      2 *
          inner ℝ
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass R j t
            )
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                R W
            )
        =
      ∫ ξ : H3FourierPoint3,
        (
          (-2 : ℝ)
            *
          (
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
          )
        )
          +
        (
          (-2 : ℝ)
            *
          (
            h3FourierGradientSquare ξ ^ 4
              *
            (
              inner ℂ
                (h3SpectralScalarRawFourierL2
                  (U j) ξ)
                (h3RawFinLerayOuterProductDivergence
                  U U j ξ)
            ).re
          )
        )
        ∂(
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) := by

    calc
      2 *
          inner ℝ
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass R j t
            )
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                R W
            )
          =
        ∫ ξ : H3FourierPoint3,
          (
            (-2 : ℝ)
              *
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
          )
            +
          (
            (-2 : ℝ)
              *
            h3FourierGradientSquare ξ ^ 4
              *
            (
              inner ℂ
                (h3SpectralScalarRawFourierL2
                  (U j) ξ)
                (h3RawFinLerayOuterProductDivergence
                  U U j ξ)
            ).re
          )
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          ) := by
            simpa only [htAbs, U] using hPair

      _ =
        ∫ ξ : H3FourierPoint3,
          (
            (-2 : ℝ)
              *
            (
              h3FourierGradientSquare ξ ^ 5
                *
              ‖h3SpectralScalarRawFourierL2
                  (U j) ξ‖ ^ 2
            )
          )
            +
          (
            (-2 : ℝ)
              *
            (
              h3FourierGradientSquare ξ ^ 4
                *
              (
                inner ℂ
                  (h3SpectralScalarRawFourierL2
                    (U j) ξ)
                  (h3RawFinLerayOuterProductDivergence
                    U U j ξ)
              ).re
            )
          )
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          ) := by

            apply integral_congr_ae
            filter_upwards with ξ
            ring

  rw [
    integral_add hDiffSigned hNonlinSigned,
    integral_const_mul,
    integral_const_mul
  ] at hPair'

  unfold
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt

  dsimp only [htAbs, U]

  exact hPair'

/-! ## Three-coordinate diffusion recombination -/

/--
The sum of the three separate coordinate diffusion integrals is exactly the
named physical fifth-radial diffusion rate.
-/
theorem sum_h3TerminalPhysicalTopDissipationDiffusionCoordinateIntegrals_eq_diffusionRateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (
      ∑ j : Fin 3,
        (-2 : ℝ)
          *
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          )
    )
      =
    h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
      hH3 hClass ht R := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  let hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  have hRawEq :
      ∀ j : Fin 3,
        h3SpectralScalarRawFourierL2 (U j)
          =
        velocityH3BaseFourierAt
          u t hInt hMeas j := by

    intro j

    dsimp only [U]

    unfold
      h3TerminalVelocitySpectralStateAt
      velocityH3SpectralStateAt

    rw [
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        hFourier j
    ]

  have hEach :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2)
          (
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          ) := by

    intro j

    have hFull :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2)
          (volume : Measure H3FourierPoint3) := by

      simpa only [htAbs, U] using
        (
          integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
            hH3 hClass ht j
        )

    exact
      hFull.mono_measure
        Measure.restrict_le_self

  unfold
    h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
    h3TerminalPhysicalTopDissipationRadialTailFifthMassAt
    h3TerminalPhysicalFifthRadialDensityAt

  dsimp only

  unfold
    velocityH3FourierMassDensityAt

  change
    (
      ∑ j : Fin 3,
        (-2 : ℝ)
          *
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          )
    )
      =
    (-2 : ℝ)
      *
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 5
        *
      (
        ∑ j : Fin 3,
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖ ^ 2
      )
      ∂(
        (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow R)ᶜ
      )

  calc
    (
      ∑ j : Fin 3,
        (-2 : ℝ)
          *
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          )
    )
        =
      (-2 : ℝ)
        *
      (
        ∑ j : Fin 3,
          ∫ ξ : H3FourierPoint3,
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
            ∂(
              (volume : Measure H3FourierPoint3).restrict
                (h3TerminalRadialFrequencyBelow R)ᶜ
            )
      ) := by
        rw [Finset.mul_sum]

    _ =
      (-2 : ℝ)
        *
      ∫ ξ : H3FourierPoint3,
        (
          ∑ j : Fin 3,
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
        )
        ∂(
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) := by

      rw [
        integral_finset_sum
          (Finset.univ : Finset (Fin 3))
          (fun j _ => hEach j)
      ]

    _ =
      (-2 : ℝ)
        *
      ∫ ξ : H3FourierPoint3,
        h3FourierGradientSquare ξ ^ 5
          *
        (
          ∑ j : Fin 3,
            ‖velocityH3BaseFourierAt
                u t hInt hMeas j ξ‖ ^ 2
        )
        ∂(
          (volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow R)ᶜ
        ) := by

      congr 1

      apply integral_congr_ae

      filter_upwards with ξ

      rw [Finset.mul_sum]

      apply Finset.sum_congr rfl

      intro j hj

      rw [hRawEq j]

/-! ## Close the existing endpoint pairing contract -/

/--
The cutoff-independent terminal fourth-radial Hilbert derivative pairing
identifies the concrete localized diffusion and nonlinear-transfer rates
without any additional hypothesis.
-/
theorem h3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertPairingIdentifiesPDEAtEndpoint_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertPairingIdentifiesPDEAtEndpoint
      hH3 hClass := by

  intro t ht W hW n

  let R : ℝ :=
    (n : ℝ) + 1

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hComponent :
      ∀ j : Fin 3,
        2 *
            inner ℝ
              (
                h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                  hH3 hClass R j t
              )
              (
                h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                  R (W j)
              )
          =
        (-2 : ℝ)
          *
        ∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5
            *
          ‖h3SpectralScalarRawFourierL2
              (U j) ξ‖ ^ 2
          ∂(
            (volume : Measure H3FourierPoint3).restrict
              (h3TerminalRadialFrequencyBelow R)ᶜ
          )
          +
        h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
          hH3 hClass ht R j := by

    intro j

    simpa only [R, htAbs, U] using
      (
        h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_two_mul_inner_derivativeValue_eq_diffusion_plus_nonlinearCoordinate
          hH3 hClass ht j (W j) (hW j)
      )

  have hDiff :
      (
        ∑ j : Fin 3,
          (-2 : ℝ)
            *
          ∫ ξ : H3FourierPoint3,
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
            ∂(
              (volume : Measure H3FourierPoint3).restrict
                (h3TerminalRadialFrequencyBelow R)ᶜ
            )
      )
        =
      h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
        hH3 hClass ht R := by

    simpa only [R, htAbs, U] using
      (
        sum_h3TerminalPhysicalTopDissipationDiffusionCoordinateIntegrals_eq_diffusionRateAt
          (R := R)
          hH3 hClass ht
      )

  change
    (
      ∑ j : Fin 3,
        2 *
          inner ℝ
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass R j t
            )
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                R (W j)
            )
    )
      =
    h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
        hH3 hClass ht R
      +
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
      hH3 hClass ht R

  calc
    (
      ∑ j : Fin 3,
        2 *
          inner ℝ
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
                hH3 hClass R j t
            )
            (
              h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
                R (W j)
            )
    )
        =
      ∑ j : Fin 3,
        (
          (
            (-2 : ℝ)
              *
            ∫ ξ : H3FourierPoint3,
              h3FourierGradientSquare ξ ^ 5
                *
              ‖h3SpectralScalarRawFourierL2
                  (U j) ξ‖ ^ 2
              ∂(
                (volume : Measure H3FourierPoint3).restrict
                  (h3TerminalRadialFrequencyBelow R)ᶜ
              )
          )
            +
          h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
            hH3 hClass ht R j
        ) := by

      apply Finset.sum_congr rfl

      intro j hj

      exact hComponent j

    _ =
      (
        ∑ j : Fin 3,
          (-2 : ℝ)
            *
          ∫ ξ : H3FourierPoint3,
            h3FourierGradientSquare ξ ^ 5
              *
            ‖h3SpectralScalarRawFourierL2
                (U j) ξ‖ ^ 2
            ∂(
              (volume : Measure H3FourierPoint3).restrict
                (h3TerminalRadialFrequencyBelow R)ᶜ
            )
      )
        +
      (
        ∑ j : Fin 3,
          h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
            hH3 hClass ht R j
      ) := by

      rw [Finset.sum_add_distrib]

    _ =
      h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
          hH3 hClass ht R
        +
      h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
        hH3 hClass ht R := by

      rw [hDiff]

      rfl

/-! ## Exact localized PDE balance is now closed -/

/--
The natural sharp top-dissipation radial tails satisfy the exact localized
Navier--Stokes PDE balance at every strict preterminal time.
-/
theorem h3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint
      hH3 hClass := by

  exact
    naturalTopDissipationRadialTailLocalizedPDEBalanceAtEndpoint_of_globalFourthRadialHilbertDerivative
      hH3
      hClass
      (
        h3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertDerivativeAtEndpoint_closed
          hH3 hClass
      )
      (
        h3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertPairingIdentifiesPDEAtEndpoint_closed
          hH3 hClass
      )

end

end Euclidean
end Bridge
end PrimeTensor
