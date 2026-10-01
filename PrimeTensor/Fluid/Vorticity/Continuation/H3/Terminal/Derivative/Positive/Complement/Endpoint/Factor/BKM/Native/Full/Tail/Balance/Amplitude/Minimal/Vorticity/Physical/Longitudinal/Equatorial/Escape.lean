import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Residual.Velocity.Component.Boundedness

/-!
# Identify the nonextension escape component with the longitudinal coordinate

Two independent reductions are now available.

* Hypothetical nonextension forces one fixed physical velocity component to
  have weighted spectral H³ norm tending to `+∞` along a strict terminal
  sequence.

* A pathwise strong-H³ endpoint for physical vorticity component `i` forces
  pathwise strong-H³ endpoints, hence eventual H³ boundedness, for the two
  transverse velocity coordinates `j ≠ i`.

Therefore, if physical vorticity component `i` survives under hypothetical
nonextension, the escaping velocity component cannot be transverse.  It is
exactly the same-index longitudinal component `i`.

This has three consequences.

1. The longitudinal spectral H³ norm tends to `+∞` along one strict terminal
   sequence.
2. The terminal-representation branch isolated previously is unavailable:
   there is no global longitudinal spectral H³ path limit at all.
3. Arbitrarily close to `T`, one can find two longitudinal spectral states
   separated by any prescribed positive H³ amount.  The angular mass theorem
   then forces a definite amount of that defect into the equatorial bad cone.

Thus, on the branch where one physical-vorticity endpoint survives,
hypothetical nonextension has a concrete quantitative equatorial escape
mechanism rather than a merely formal endpoint-representation mismatch.

All statements remain conditional necessary consequences of hypothetical
nonextension; no existence of a singular solution is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## The escaping component is longitudinal -/

/--
Under hypothetical nonextension, if physical vorticity component `i` has a
pathwise strong-H³ endpoint, then the fixed velocity component whose spectral
H³ norm tends to `+∞` is precisely the longitudinal component `i`.
-/
theorem exists_terminal_longitudinalVelocityComponentSpectralNorm_tendsto_atTop_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i) :
    ∃ τ : ℕ → ℝ,
      ∃ hTauStrict :
        ∀ n : ℕ,
          τ n ∈ Set.Ioo (0 : ℝ) T,
        (
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              norm
                (
                  h3TerminalVelocityComponentSpectralStateAt
                    hH3
                    i
                    (τ n)
                    (hTauStrict n)
                )
          )
          atTop
          atTop := by

  obtain
    ⟨
      j,
      τ,
      hTauStrict,
      hTauClass,
      hTau,
      hNorm
    ⟩ :=
    exists_terminal_velocityComponentSpectralNorm_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hji :
      j = i := by

    by_contra hne

    have hStrongJ :
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 j :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        hne
        hPhysical

    have hBoundedJ :
        H3TerminalVelocityComponentEventuallyBounded
          hH3 j :=
      velocityComponentEventuallyBounded_of_strongH3EndpointPath
        hH3
        hStrongJ

    obtain
      ⟨
        b,
        B,
        hbT,
        hBound
      ⟩ :=
      hBoundedJ

    have hTimeEventually :
        ∀ᶠ n : ℕ in atTop,
          b < τ n :=
      (tendsto_order.1 hTau).1
        b
        hbT

    have hNormEventually :
        ∀ᶠ n : ℕ in atTop,
          B
            <
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                hH3
                j
                (τ n)
                (hTauStrict n)
            ) :=
      hNorm.eventually
        (eventually_gt_atTop B)

    obtain
      ⟨
        n,
        hnTime,
        hnLarge
      ⟩ :=
      (
        hTimeEventually.and
          hNormEventually
      ).exists

    have hnBound :
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3
              j
              (τ n)
              (hTauStrict n)
          )
          ≤
        B :=
      hBound
        (τ n)
        (hTauStrict n)
        hnTime

    exact
      (not_lt_of_ge hnBound)
        hnLarge

  subst j

  exact
    ⟨
      τ,
      hTauStrict,
      hTauClass,
      hTau,
      hNorm
    ⟩

/-! ## The longitudinal component has no spectral path limit -/

/--
On the same branch, the longitudinal velocity component cannot possess any
global spectral H³ path limit.

Indeed, convergence to a finite `Ginf` would make the component norm eventually
bounded, contradicting the longitudinal norm escape sequence.
-/
theorem no_longitudinalVelocityComponentSpectralLimitPath_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i) :
    ¬
      H3TerminalVelocityComponentHasSpectralLimitPath
        hH3 i := by

  obtain
    ⟨
      τ,
      hTauStrict,
      _hTauClass,
      hTau,
      hNorm
    ⟩ :=
    exists_terminal_longitudinalVelocityComponentSpectralNorm_tendsto_atTop_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical

  intro hLimit

  obtain
    ⟨
      Ginf,
      hGinf
    ⟩ :=
    hLimit

  obtain
    ⟨
      η,
      hη,
      hClose
    ⟩ :=
    hGinf
      1
      zero_lt_one

  have hTauMetric :=
    hTau

  rw [Metric.tendsto_atTop] at hTauMetric

  obtain
    ⟨
      N,
      hNear
    ⟩ :=
    hTauMetric
      η
      hη

  have hNormLarge :
      ∀ᶠ n : ℕ in atTop,
        1 + ‖Ginf‖
          <
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3
              i
              (τ n)
              (hTauStrict n)
          ) :=
    hNorm.eventually
      (
        eventually_gt_atTop
          (1 + ‖Ginf‖)
      )

  obtain
    ⟨
      n,
      hnN,
      hnLarge
    ⟩ :=
    (
      (eventually_ge_atTop N).and
        hNormLarge
    ).exists

  let U :
      H3SpectralScalarState :=
    h3TerminalVelocityComponentSpectralStateAt
      hH3
      i
      (τ n)
      (hTauStrict n)

  have hCloseN :
      norm (U - Ginf) < 1 := by

    dsimp only [U]

    exact
      hClose
        (τ n)
        (hTauStrict n)
        (hNear n hnN)

  have hUpper :
      norm U < 1 + norm Ginf := by

    calc
      norm U
          =
        norm
          (
            (U - Ginf) + Ginf
          ) := by
            rw [sub_add_cancel]

      _ ≤
        norm (U - Ginf)
          +
        norm Ginf :=
          norm_add_le _ _

      _ <
        1 + norm Ginf := by
          linarith

  have hLower :
      1 + norm Ginf
        <
      norm U := by

    dsimp only [U]

    exact
      hnLarge

  exact
    (not_lt_of_ge
      (le_of_lt hLower))
      hUpper

/--
Hence the previous endpoint-mechanism disjunction collapses to the equatorial
spectral-limit obstruction on any surviving physical-vorticity branch.
-/
theorem longitudinalEquatorialSpectralLimitObstruction_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i) :
    H3TerminalLongitudinalEquatorialSpectralLimitObstruction
      hH3 i := by

  exact
    ⟨
      no_longitudinalVelocityComponentSpectralLimitPath_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical,
      longitudinalGoodConeCauchyControl_of_actualVorticityStrongH3EndpointPath
        hH3
        hPhysical
    ⟩

/-! ## Arbitrarily late longitudinal pairwise separation -/

/--
The longitudinal norm escape produces arbitrarily late pairs of strict times
whose longitudinal H³ spectral states are separated by any prescribed positive
amount.
-/
theorem exists_arbitrarilyLate_longitudinalVelocityComponentSpectralSeparation_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∀ η : ℝ,
      0 < η →
      ∃
        s : ℝ,
        ∃ hs : s ∈ Set.Ioo (0 : ℝ) T,
        ∃
          t : ℝ,
          ∃ ht : t ∈ Set.Ioo (0 : ℝ) T,
            dist s T < η
              ∧
            dist t T < η
              ∧
            ε
              ≤
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                    hH3 i s hs
                  -
                h3TerminalVelocityComponentSpectralStateAt
                    hH3 i t ht
              ) := by

  obtain
    ⟨
      τ,
      hTauStrict,
      _hTauClass,
      hTau,
      hNorm
    ⟩ :=
    exists_terminal_longitudinalVelocityComponentSpectralNorm_tendsto_atTop_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical

  intro η hη

  have hTauMetric :=
    hTau

  rw [Metric.tendsto_atTop] at hTauMetric

  obtain
    ⟨
      N,
      hNear
    ⟩ :=
    hTauMetric
      η
      hη

  let Ut :
      H3SpectralScalarState :=
    h3TerminalVelocityComponentSpectralStateAt
      hH3
      i
      (τ N)
      (hTauStrict N)

  have hNormLarge :
      ∀ᶠ n : ℕ in atTop,
        norm Ut + ε
          <
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3
              i
              (τ n)
              (hTauStrict n)
          ) :=
    hNorm.eventually
      (
        eventually_gt_atTop
          (norm Ut + ε)
      )

  obtain
    ⟨
      n,
      hnN,
      hnLarge
    ⟩ :=
    (
      (eventually_ge_atTop N).and
        hNormLarge
    ).exists

  let Us :
      H3SpectralScalarState :=
    h3TerminalVelocityComponentSpectralStateAt
      hH3
      i
      (τ n)
      (hTauStrict n)

  have hTriangle :
      norm Us
        ≤
      norm (Us - Ut)
        +
      norm Ut := by

    calc
      norm Us
          =
        norm
          (
            (Us - Ut) + Ut
          ) := by
            rw [sub_add_cancel]

      _ ≤
        norm (Us - Ut)
          +
        norm Ut :=
          norm_add_le _ _

  have hSeparation :
      ε
        ≤
      norm (Us - Ut) := by

    have hLarge' :
        norm Ut + ε
          <
        norm Us := by

      dsimp only [Us]

      exact
        hnLarge

    linarith

  refine
    ⟨
      τ n,
      hTauStrict n,
      τ N,
      hTauStrict N,
      hNear n hnN,
      hNear N (le_refl N),
      ?_
    ⟩

  dsimp only [Us, Ut] at hSeparation

  exact
    hSeparation

/-! ## Recurrent quantitative equatorial mass -/

/--
Under hypothetical nonextension and a surviving physical-vorticity endpoint,
equatorial longitudinal H³ defect mass recurs arbitrarily close to `T`.

For every aperture `κ > 0`, every separation scale `ε > 0`, and every terminal
radius `η > 0`, there are two strict times within `η` of `T` whose bad-cone
scaled square defect is larger than `κ² ε² / 2`.
-/
theorem exists_arbitrarilyLate_longitudinalBadConeScaledSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {κ ε : ℝ}
    (hκ : 0 < κ)
    (hε : 0 < ε) :
    ∀ η : ℝ,
      0 < η →
      ∃
        s : ℝ,
        ∃ hs : s ∈ Set.Ioo (0 : ℝ) T,
        ∃
          t : ℝ,
          ∃ ht : t ∈ Set.Ioo (0 : ℝ) T,
            dist s T < η
              ∧
            dist t T < η
              ∧
            (κ ^ 2 * ε ^ 2) / 2
              <
            h3TerminalLongitudinalBadConeScaledSquareDefect
              i κ
              (h3TerminalVelocitySpectralStateAt hH3 s hs)
              (h3TerminalVelocitySpectralStateAt hH3 t ht) := by

  obtain
    ⟨
      η₀,
      hη₀,
      hBadNear
    ⟩ :=
    longitudinalBadConeScaledSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath
      hH3
      hPhysical
      hκ
      hε

  intro η hη

  let ρ : ℝ :=
    min η η₀

  have hρ :
      0 < ρ := by

    dsimp only [ρ]

    exact
      lt_min
        hη
        hη₀

  obtain
    ⟨
      s,
      hs,
      t,
      ht,
      hsρ,
      htρ,
      hSep
    ⟩ :=
    exists_arbitrarilyLate_longitudinalVelocityComponentSpectralSeparation_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε
      ρ
      hρ

  have hsη :
      dist s T < η :=
    lt_of_lt_of_le
      hsρ
      (min_le_left _ _)

  have htη :
      dist t T < η :=
    lt_of_lt_of_le
      htρ
      (min_le_left _ _)

  have hsη₀ :
      dist s T < η₀ :=
    lt_of_lt_of_le
      hsρ
      (min_le_right _ _)

  have htη₀ :
      dist t T < η₀ :=
    lt_of_lt_of_le
      htρ
      (min_le_right _ _)

  have hMass :=
    hBadNear
      s hs
      t ht
      hsη₀
      htη₀
      hSep

  exact
    ⟨
      s,
      hs,
      t,
      ht,
      hsη,
      htη,
      hMass
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
