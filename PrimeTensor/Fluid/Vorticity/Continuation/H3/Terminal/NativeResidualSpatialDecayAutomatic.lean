import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualBoundedBranchPeakLocus
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.SpatialDecay

/-!
# Derive selected terminal spatial decay from H³ and endpoint temporal control

The terminal geometry previously treated

    H3TerminalComplementGradientSelectedTerminalDecayAtInfinity

as an independent analytic frontier.

The fixed-slice Fourier analysis now removes that independence.

At every strict preterminal time of a `LoggedPreterminalH3PathAdmissible`
solution:

* the velocity slice has a weighted spectral H³ state;
* its canonical real `C¹` representative agrees pointwise with the old logged
  velocity component;
* every first coordinate derivative of that representative vanishes along
  every spatial escape by the Riemann--Lebesgue theorem proved in
  `H3.Real.C1.SpatialDecay`.

Hence the actual complementary first derivative vanishes at spatial infinity
at every strict time.

The selected endpoint temporal modulus is uniform over all selected spatial
points.  Given an escaping selected sequence and `ε > 0`, choose one fixed
selected strict time `τ N` sufficiently close to `T`.  At that fixed time the
H³/Riemann--Lebesgue theorem makes the complementary derivative small far out
in space, while the endpoint modulus makes its value uniformly close to the
actual terminal value.  A triangle estimate gives terminal decay.

Therefore terminal spatial decay is no longer an independent hypothesis once
the H³ path, strict selected times, terminal-time convergence, and the endpoint
temporal modulus are available.

The final theorem threads this into the compact peak-locus alternative, so the
remaining substantive frontiers are endpoint temporal control and selected
spatial equicontinuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualDecayAutomatic
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Strict-time decay of the actual complementary gradient -/

/--
At every strict time of an H³-path-admissible solution, the actual
complementary first velocity derivative vanishes along every spatially
escaping sequence.
-/
theorem terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    {p : H3TerminalCurlGradientPair}
    {y : ℕ → Point3}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T)
    (hEscape :
      Tendsto
        (
          fun n : ℕ =>
            dist
              (0 : Point3)
              (y n)
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalComplementGradientFieldForPair
            u p t (y n)
      )
      atTop
      (𝓝 0) := by

  let hNS :
      LoggedPreterminalNavierStokesAdmissible
        u T :=
    hH3.navier_stokes

  let hInt :
      VelocityH3IntegrableAt
        u t :=
    hH3.velocity_h3_integrable
      t ht

  let hMeas :
      VelocityH3MeasurableAt
        u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementDerivativeAxisForPair p)

  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)

  have hAE :
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          U
          j
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u t
        (h3AxisOfFin3 j) := by

    dsimp only [U]

    exact
      h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
        hFourier
        j

  have hSpectralContinuous :
      Continuous
        (
          h3SpectralVelocityRealC1RepresentativeOnPoint3
            U
            j
        ) := by

    change
      Continuous
        (
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (U j)
        )

    exact
      (
        h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
          (U j)
      ).continuous

  have hOldContinuous :
      Continuous
        (
          loggedVelocityComponent
            u t
            (h3AxisOfFin3 j)
        ) := by

    let pressure :
        ℝ → ScalarField3 :=
      Classical.choose hNS

    let hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          pressure
          T :=
      Classical.choose_spec hNS

    unfold loggedVelocityComponent

    exact
      (
        hPDE.regularity.velocity_spatial_three
          t ht
          (h3AxisOfFin3 j)
      ).continuous

  have hPointwise :
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          U
          j
        =
      loggedVelocityComponent
        u t
        (h3AxisOfFin3 j) :=
    MeasureTheory.Measure.eq_of_ae_eq
      hAE
      hSpectralContinuous
      hOldContinuous

  have hComponentAxis :
      h3AxisOfFin3 j
        =
      h3TerminalComplementComponentAxisForPair p := by

    dsimp only [j]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
        (h3TerminalComplementComponentAxisForPair p)

  have hDerivativeAxis :
      h3AxisOfFin3 i
        =
      h3TerminalComplementDerivativeAxisForPair p := by

    dsimp only [i]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
        (h3TerminalComplementDerivativeAxisForPair p)

  have hPointwise' :
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          U
          j
        =
      loggedVelocityComponent
        u t
        (h3TerminalComplementComponentAxisForPair p) := by

    rw [← hComponentAxis]

    exact
      hPointwise

  have hDerivativeEq :
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair p)
          (
            h3SpectralVelocityRealC1RepresentativeOnPoint3
              U
              j
          )
        =
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair p)
          (
            loggedVelocityComponent
              u t
              (h3TerminalComplementComponentAxisForPair p)
          ) :=
    congrArg
      (
        fun f : Point3 → ℝ =>
          spatial3.d
            (h3TerminalComplementDerivativeAxisForPair p)
            f
      )
      hPointwise'

  have hSpectralDecay :
      Tendsto
        (
          fun n : ℕ =>
            spatial3.d
              (h3AxisOfFin3 i)
              (
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (U j)
              )
              (y n)
        )
        atTop
        (𝓝 0) :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_tendsto_zero_of_escape
      (U j)
      i
      hEscape

  have hSpectralDecay' :
      Tendsto
        (
          fun n : ℕ =>
            spatial3.d
              (h3TerminalComplementDerivativeAxisForPair p)
              (
                h3SpectralVelocityRealC1RepresentativeOnPoint3
                  U
                  j
              )
              (y n)
        )
        atTop
        (𝓝 0) := by

    simpa only [
      hDerivativeAxis,
      h3SpectralVelocityRealC1RepresentativeOnPoint3
    ] using
      hSpectralDecay

  have hActualDecay :
      Tendsto
        (
          fun n : ℕ =>
            spatial3.d
              (h3TerminalComplementDerivativeAxisForPair p)
              (
                loggedVelocityComponent
                  u t
                  (h3TerminalComplementComponentAxisForPair p)
              )
              (y n)
        )
        atTop
        (𝓝 0) := by

    rw [← hDerivativeEq]

    exact
      hSpectralDecay'

  change
    Tendsto
      (
        fun n : ℕ =>
          spatial3.d
            (h3TerminalComplementDerivativeAxisForPair p)
            (
              loggedVelocityComponent
                u t
                (h3TerminalComplementComponentAxisForPair p)
            )
            (y n)
      )
      atTop
      (𝓝 0)

  exact
    hActualDecay

/-! ## Endpoint temporal control transfers strict-time decay to T -/

/--
If the selected times are strict preterminal times converging to `T`, then the
uniform selected endpoint temporal modulus transfers strict-time H³ spatial
decay to the actual terminal complementary-gradient field.

Thus `H3TerminalComplementGradientSelectedTerminalDecayAtInfinity` is derived,
not assumed.
-/
theorem selectedTerminalDecayAtInfinity_of_h3Path_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T) :
    H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
      u p x T := by

  intro k hSpatial

  rw [Metric.tendsto_atTop]

  intro ε hε

  have hHalfPos :
      0 < ε / 2 := by
    linarith

  obtain
    ⟨
      η,
      hη,
      hEndpointUniform
    ⟩ :=
    hEndpoint
      (ε / 2)
      hHalfPos

  rw [Metric.tendsto_atTop] at hTau

  obtain
    ⟨
      N,
      hNearN
    ⟩ :=
    hTau
      η
      hη

  have hTauN :
      τ N ∈ Set.Ioo (0 : ℝ) T :=
    hTauStrict
      N

  have hTimeNear :
      dist (τ N) T < η :=
    hNearN
      N
      le_rfl

  have hStrictDecay :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              (τ N)
              (x (k j))
        )
        atTop
        (𝓝 0) :=
    terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
      hH3
      hTauN
      hSpatial

  rw [Metric.tendsto_atTop] at hStrictDecay

  obtain
    ⟨
      J,
      hJ
    ⟩ :=
    hStrictDecay
      (ε / 2)
      hHalfPos

  refine
    ⟨
      J,
      ?_
    ⟩

  intro j hj

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x (k j))

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ N)
      (x (k j))

  have hBA :
      dist B A < ε / 2 := by

    dsimp only [A, B]

    exact
      hEndpointUniform
        (k j)
        N
        hTimeNear

  have hAB :
      dist A B < ε / 2 := by

    simpa only [dist_comm] using
      hBA

  have hB0 :
      dist B 0 < ε / 2 := by

    dsimp only [B]

    exact
      hJ
        j
        hj

  have hTriangle :
      dist A 0
        ≤
      dist A B + dist B 0 :=
    dist_triangle
      A B 0

  have hA0 :
      dist A 0 < ε := by
    linarith

  simpa only [A] using
    hA0

/-! ## Remove terminal decay from the peak-locus hypotheses -/

/--
Once the H³ path and strict selected terminal times are retained, terminal
spatial decay is automatic from fixed-slice Riemann--Lebesgue decay plus the
uniform endpoint temporal modulus.

Accordingly, the compact peak-locus no-canonical-factor alternative no longer
takes `H3TerminalComplementGradientSelectedTerminalDecayAtInfinity` as an
independent assumption.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast_of_h3Path
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
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hSpatialEquicontinuity :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x)
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

  have hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T :=
    selectedTerminalDecayAtInfinity_of_h3Path_of_endpointTemporalModulus
      hH3
      hTauStrict
      hTau
      hEndpoint

  exact
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast_of_complementBound
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hComplementBound
      hNoFactor

end

end Euclidean
end Bridge
end PrimeTensor
