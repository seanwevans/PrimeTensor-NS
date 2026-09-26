import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualEndpointH3Criterion
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Strong H³ endpoint control also gives selected spatial equicontinuity

The previous endpoint criterion showed that strong spectral H³ convergence to
a terminal state implies the selected endpoint temporal modulus.

The same strong H³ control also removes the independent selected spatial
equicontinuity frontier.

Two ingredients suffice.

1. For a fixed weighted spectral H³ state, every first spatial derivative of
   its real physical representative is continuous and vanishes at infinity.
   Mathlib's cocompact Heine--Cantor theorem therefore upgrades it to a
   globally uniformly continuous function on `Point3`.

2. Along a strongly convergent H³ terminal sequence, sufficiently late states
   are uniformly close to the terminal H³ state in first-derivative sup norm,
   by the existing bounded derivative-evaluation estimate.  Only finitely many
   early slices remain, and a finite family of uniformly continuous functions
   has a common modulus.

Thus one strong H³ endpoint condition supplies both of the previously separate
analytic frontiers:

* endpoint temporal control;
* selected spatial equicontinuity.

The final theorem threads this into the terminal compact peak-locus
alternative.  This is a reduction of hypotheses, not a proof that the strong
H³ endpoint condition itself follows from the current continuation data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSpatialH3Criterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fixed H³ first derivatives are uniformly continuous -/

/--
A first spatial derivative of an arbitrary spectral H³ representative tends
to zero along the cocompact filter of `Point3`.
-/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_tendsto_zero_cocompact
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    Tendsto
      (
        spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
      )
      (cocompact Point3)
      (𝓝 0) := by

  let D : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourierCoordinateDerivative G i

  have hToFourier :
      Tendsto
        (WithLp.toLp 2 : Point3 → H3FourierPoint3)
        (cocompact Point3)
        (cocompact H3FourierPoint3) := by

    change
      Tendsto
        ⇑(
          (
            PiLp.homeomorph
              2
              (fun _ : PrimeTensor.Axis Depth.three => ℝ)
          ).symm
        )
        (cocompact Point3)
        (cocompact H3FourierPoint3)

    exact
      (
        (
          PiLp.homeomorph
            2
            (fun _ : PrimeTensor.Axis Depth.three => ℝ)
        ).symm
      ).toCocompactMap.cocompact_tendsto'

  have hComplex :
      Tendsto
        (
          fun x : Point3 =>
            FourierTransformInv.fourierInv
              D
              (
                (WithLp.toLp 2 : Point3 → H3FourierPoint3)
                  x
              )
        )
        (cocompact Point3)
        (𝓝 0) := by

    change
      Tendsto
        (
          (
            FourierTransformInv.fourierInv D
          ) ∘
          (WithLp.toLp 2 : Point3 → H3FourierPoint3)
        )
        (cocompact Point3)
        (𝓝 0)

    exact
      (
        h3SpectralScalarRawFourierCoordinateDerivative_fourierInv_tendsto_zero_cocompact
          G i
      ).comp
        hToFourier

  have hReal :
      Tendsto
        (
          fun x : Point3 =>
            (
              FourierTransformInv.fourierInv
                D
                (
                  (WithLp.toLp 2 : Point3 → H3FourierPoint3)
                    x
                )
            ).re
        )
        (cocompact Point3)
        (𝓝 0) := by

    have hRe :
        Tendsto
          (fun z : ℂ => z.re)
          (𝓝 (0 : ℂ))
          (𝓝 (0 : ℝ)) := by

      change
        ContinuousAt
          (fun z : ℂ => z.re)
          0

      exact
        Complex.continuous_re.continuousAt

    exact
      hRe.comp
        hComplex

  have hEq :
      spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        =
      (
        fun x : Point3 =>
          (
            FourierTransformInv.fourierInv
              D
              (
                (WithLp.toLp 2 : Point3 → H3FourierPoint3)
                  x
              )
          ).re
      ) := by

    funext x

    dsimp only [D]

    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
        G i x

  rw [hEq]

  exact
    hReal

/--
Every first spatial derivative of an arbitrary spectral H³ representative is
globally uniformly continuous on `Point3`.
-/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_uniformContinuous
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    UniformContinuous
      (
        spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
      ) := by

  have hContinuous :
      Continuous
        (
          spatial3.d
            (h3AxisOfFin3 i)
            (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        ) :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_continuous
      G
      (h3AxisOfFin3 i)

  have hZero :
      Tendsto
        (
          spatial3.d
            (h3AxisOfFin3 i)
            (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        )
        (cocompact Point3)
        (𝓝 0) :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_tendsto_zero_cocompact
      G i

  exact
    hContinuous.uniformContinuous_of_tendsto_cocompact
      hZero

/-! ## A finite family admits one common spatial modulus -/

/--
A finite prefix of uniformly continuous real fields on `Point3` admits one
common positive metric modulus.
-/
theorem finitePrefix_uniformSpatialModulus
    (F : ℕ → Point3 → ℝ)
    (hF :
      ∀ r : ℕ,
        UniformContinuous (F r))
    (x : ℕ → Point3)
    (N : ℕ)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ r : ℕ,
        r < N →
        ∀ m n : ℕ,
          dist (x m) (x n) < η →
          dist
            (F r (x m))
            (F r (x n))
            < ε := by

  induction N with

  | zero =>
      refine
        ⟨
          1,
          by norm_num,
          ?_
        ⟩

      intro r hr

      omega

  | succ N hInd =>
      obtain
        ⟨
          η₁,
          hη₁,
          hPrefix
        ⟩ :=
        hInd

      obtain
        ⟨
          η₂,
          hη₂,
          hLast
        ⟩ :=
        (
          Metric.uniformContinuous_iff.1
            (hF N)
        )
          ε
          hε

      refine
        ⟨
          min η₁ η₂,
          lt_min hη₁ hη₂,
          ?_
        ⟩

      intro r hr m n hmn

      by_cases hrOld :
          r < N

      · exact
          hPrefix
            r
            hrOld
            m
            n
            (
              lt_of_lt_of_le
                hmn
                (min_le_left η₁ η₂)
            )

      · have hrEq :
            r = N := by
          omega

        subst r

        exact
          hLast
            (
              lt_of_lt_of_le
                hmn
                (min_le_right η₁ η₂)
            )

/-! ## Strong H³ endpoint control implies selected spatial equicontinuity -/

/--
Strong selected H³ convergence to a terminal spectral state implies one
spatial modulus for the complementary first derivative over the entire
selected time family.

Late states are handled by H³ closeness to the terminal state.  The finitely
many early states are handled by their individual global uniform continuity.
-/
theorem selectedSpatialEquicontinuity_of_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    {x : ℕ → Point3}
    {p : H3TerminalCurlGradientPair}
    (hStrong :
      H3TerminalComplementGradientSelectedStrongH3Endpoint
        hH3 hTauStrict p) :
    H3TerminalComplementGradientSelectedSpatialEquicontinuity
      u p τ x := by

  obtain
    ⟨
      Ginf,
      _hTerminalRep,
      hH3Modulus
    ⟩ :=
    hStrong

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementDerivativeAxisForPair p)

  let K : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  have hK :
      0 ≤ K := by

    dsimp only [K]

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  have hAxis :
      h3AxisOfFin3 i
        =
      h3TerminalComplementDerivativeAxisForPair p := by

    dsimp only [i]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
        (h3TerminalComplementDerivativeAxisForPair p)

  let G : ℕ → H3SpectralScalarState :=
    fun r =>
      h3TerminalSelectedComplementSpectralState
        hH3 hTauStrict p r

  let J :
      H3SpectralScalarState → Point3 → ℝ :=
    fun H =>
      spatial3.d
        (h3TerminalComplementDerivativeAxisForPair p)
        (h3SpectralScalarRealC1RepresentativeOnPoint3 H)

  have hFieldEq :
      ∀ r : ℕ,
        (
          fun z : Point3 =>
            h3TerminalComplementGradientFieldForPair
              u p
              (τ r)
              z
        )
          =
        J (G r) := by

    intro r

    have hRep :=
      h3TerminalSelectedComplementSpectralState_representative_eq_loggedVelocityComponent
        hH3 hTauStrict p r

    funext z

    dsimp only [J, G]

    rw [hRep]

    rfl

  have hUniformG :
      ∀ r : ℕ,
        UniformContinuous
          (J (G r)) := by

    intro r

    have h :=
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_uniformContinuous
        (G r)
        i

    rw [hAxis] at h

    exact
      h

  have hUniformInf :
      UniformContinuous
        (J Ginf) := by

    have h :=
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_uniformContinuous
        Ginf
        i

    rw [hAxis] at h

    exact
      h

  intro ε hε

  have hThirdPos :
      0 < ε / 3 := by
    linarith

  have hKOne :
      0 < K + 1 := by
    linarith

  have hStateRadiusPos :
      0 < (ε / 3) / (K + 1) :=
    div_pos hThirdPos hKOne

  obtain
    ⟨
      ηTime,
      hηTime,
      hStateNear
    ⟩ :=
    hH3Modulus
      ((ε / 3) / (K + 1))
      hStateRadiusPos

  rw [Metric.tendsto_atTop] at hTau

  obtain
    ⟨
      N,
      hNearTerminal
    ⟩ :=
    hTau
      ηTime
      hηTime

  obtain
    ⟨
      ηInf,
      hηInf,
      hInfModulus
    ⟩ :=
    (
      Metric.uniformContinuous_iff.1
        hUniformInf
    )
      (ε / 3)
      hThirdPos

  obtain
    ⟨
      ηEarly,
      hηEarly,
      hEarly
    ⟩ :=
    finitePrefix_uniformSpatialModulus
      (fun r => J (G r))
      hUniformG
      x
      N
      ε
      hε

  refine
    ⟨
      min ηInf ηEarly,
      lt_min hηInf hηEarly,
      ?_
    ⟩

  intro r m n hmn

  by_cases hrEarly :
      r < N

  · have hmField :
        h3TerminalComplementGradientFieldForPair
            u p
            (τ r)
            (x m)
          =
        J (G r) (x m) :=
      congrFun
        (hFieldEq r)
        (x m)

    have hnField :
        h3TerminalComplementGradientFieldForPair
            u p
            (τ r)
            (x n)
          =
        J (G r) (x n) :=
      congrFun
        (hFieldEq r)
        (x n)

    rw [hmField, hnField]

    exact
      hEarly
        r
        hrEarly
        m
        n
        (
          lt_of_lt_of_le
            hmn
            (min_le_right ηInf ηEarly)
        )

  · have hrLate :
        N ≤ r := by
      omega

    have hTimeNear :
        dist (τ r) T < ηTime :=
      hNearTerminal
        r
        hrLate

    have hStateSmall :
        ‖G r - Ginf‖
          <
        (ε / 3) / (K + 1) := by

      dsimp only [G]

      exact
        hStateNear
          r
          hTimeNear

    have hFraction :
        K * ((ε / 3) / (K + 1))
          <
        ε / 3 := by

      have hRatio :
          K / (K + 1) < 1 :=
        (div_lt_one hKOne).2
          (by linarith)

      calc
        K * ((ε / 3) / (K + 1))
            =
          (ε / 3) * (K / (K + 1)) := by
            ring
        _ <
          (ε / 3) * 1 :=
            mul_lt_mul_of_pos_left
              hRatio
              hThirdPos
        _ =
          ε / 3 := by
            ring

    have hAtMRaw :=
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_sub_apply_le
        (G r)
        Ginf
        i
        (x m)

    have hAtNRaw :=
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_sub_apply_le
        (G r)
        Ginf
        i
        (x n)

    rw [hAxis] at hAtMRaw
    rw [hAxis] at hAtNRaw

    have hAtM :
        dist
            (J (G r) (x m))
            (J Ginf (x m))
          <
        ε / 3 := by

      have hBound :
          dist
              (J (G r) (x m))
              (J Ginf (x m))
            ≤
          K * ‖G r - Ginf‖ := by

        dsimp only [J, K]

        simpa only [
          Real.dist_eq,
          Real.norm_eq_abs
        ] using
          hAtMRaw

      have hUpper :
          K * ‖G r - Ginf‖
            ≤
          K * ((ε / 3) / (K + 1)) :=
        mul_le_mul_of_nonneg_left
          (le_of_lt hStateSmall)
          hK

      exact
        lt_of_le_of_lt
          hBound
          (
            lt_of_le_of_lt
              hUpper
              hFraction
          )

    have hAtN :
        dist
            (J Ginf (x n))
            (J (G r) (x n))
          <
        ε / 3 := by

      have hBound :
          dist
              (J (G r) (x n))
              (J Ginf (x n))
            ≤
          K * ‖G r - Ginf‖ := by

        dsimp only [J, K]

        simpa only [
          Real.dist_eq,
          Real.norm_eq_abs
        ] using
          hAtNRaw

      have hUpper :
          K * ‖G r - Ginf‖
            ≤
          K * ((ε / 3) / (K + 1)) :=
        mul_le_mul_of_nonneg_left
          (le_of_lt hStateSmall)
          hK

      have hForward :
          dist
              (J (G r) (x n))
              (J Ginf (x n))
            <
          ε / 3 :=
        lt_of_le_of_lt
          hBound
          (
            lt_of_le_of_lt
              hUpper
              hFraction
          )

      simpa only [dist_comm] using
        hForward

    have hMiddle :
        dist
            (J Ginf (x m))
            (J Ginf (x n))
          <
        ε / 3 :=
      hInfModulus
        (
          lt_of_lt_of_le
            hmn
            (min_le_left ηInf ηEarly)
        )

    have hTriangle₁ :
        dist
            (J (G r) (x m))
            (J Ginf (x n))
          ≤
        dist
            (J (G r) (x m))
            (J Ginf (x m))
          +
        dist
            (J Ginf (x m))
            (J Ginf (x n)) :=
      dist_triangle
        (J (G r) (x m))
        (J Ginf (x m))
        (J Ginf (x n))

    have hTriangle₂ :
        dist
            (J (G r) (x m))
            (J (G r) (x n))
          ≤
        dist
            (J (G r) (x m))
            (J Ginf (x n))
          +
        dist
            (J Ginf (x n))
            (J (G r) (x n)) :=
      dist_triangle
        (J (G r) (x m))
        (J Ginf (x n))
        (J (G r) (x n))

    have hFinal :
        dist
            (J (G r) (x m))
            (J (G r) (x n))
          <
        ε := by
      linarith

    have hmField :
        h3TerminalComplementGradientFieldForPair
            u p
            (τ r)
            (x m)
          =
        J (G r) (x m) :=
      congrFun
        (hFieldEq r)
        (x m)

    have hnField :
        h3TerminalComplementGradientFieldForPair
            u p
            (τ r)
            (x n)
          =
        J (G r) (x n) :=
      congrFun
        (hFieldEq r)
        (x n)

    rw [hmField, hnField]

    exact
      hFinal

/-! ## Collapse both analytic frontier hypotheses to strong H³ endpoint control -/

/--
Under strong H³ endpoint control, the compact peak-locus alternative no longer
requires separate endpoint-temporal or selected-spatial-equicontinuity
hypotheses.

The remaining explicit data are:

* the preterminal H³ path;
* strict selected terminal times converging to `T`;
* strong H³ endpoint control for the complementary component;
* the raw eventual complementary-log bound from the bounded cancellation
  branch;
* failure of the canonical factor.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast_of_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    {N : ℕ}
    {C : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hStrong :
      H3TerminalComplementGradientSelectedStrongH3Endpoint
        hH3 hTauStrict p)
    (hComplementBound :
      ∀ n : ℕ,
        N ≤ n →
        abs
          (
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ n)
                  (x n)
              )
          )
          ≤ C)
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    let hEndpoint :
        H3TerminalComplementGradientSelectedEndpointTemporalModulus
          u p τ x T :=
      selectedEndpointTemporalModulus_of_strongH3Endpoint
        hH3 hTauStrict hStrong
    let hSpatialEquicontinuity :
        H3TerminalComplementGradientSelectedSpatialEquicontinuity
          u p τ x :=
      selectedSpatialEquicontinuity_of_strongH3Endpoint
        hH3 hTauStrict hTau hStrong
    let hTerminalModulus :
        H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
          u p x T :=
      selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
        hTau
        hSpatialEquicontinuity
        hEndpoint
    H3TerminalNativeComplementHasPivotInfinityAndCompactPeakLocus
        u p τ x T hTerminalModulus
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  dsimp only

  let hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T :=
    selectedEndpointTemporalModulus_of_strongH3Endpoint
      hH3 hTauStrict hStrong

  let hSpatialEquicontinuity :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x :=
    selectedSpatialEquicontinuity_of_strongH3Endpoint
      hH3 hTauStrict hTau hStrong

  exact
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast_of_h3Path
      hH3
      hTauStrict
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hComplementBound
      hNoFactor

end

end Euclidean
end Bridge
end PrimeTensor
