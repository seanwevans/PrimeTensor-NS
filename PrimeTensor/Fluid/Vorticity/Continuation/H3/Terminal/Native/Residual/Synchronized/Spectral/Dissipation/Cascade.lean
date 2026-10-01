import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Residual.Velocity.Energy.Boundedness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Full.Limit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Normalized.Cascade

/-!
# Synchronize fixed-component H³ escape with the terminal dissipation cascade

The fixed-component argument and the scalar terminal-rate argument were proved
by different routes.

The fixed-component theorem supplies one physical velocity coordinate `j` and
one strict sequence `τ n → T` such that

    ‖U_j(τ n)‖_{H³} → +∞.

Independently, hypothetical nonextension forces full left-terminal limits

    D(t) / E(t) → +∞,
    Λ₃(t) → +∞,
    ℓ₃(t) → 0.

Because the selected component state is one coordinate of the exact encoded
H³ velocity state,

    ‖U_j(t)‖ ≤ ‖U(t)‖ ≤ sqrt(E(t)).

Hence the fixed-component escape sequence also satisfies

    E(τ n) → +∞.

Since every `τ n` lies strictly below `T`, the same sequence tends to `T`
through the left-neighborhood filter, so all full-tail dissipation/frequency
limits may be composed with it.

The result is one synchronized terminal sequence carrying:

* a fixed physical component H³ norm escaping to infinity;
* full canonical H³ energy escaping to infinity;
* normalized full dissipation `D/E` escaping to infinity;
* top characteristic frequency escaping to infinity;
* top characteristic length collapsing to zero.

This is a necessary condition for hypothetical nonextension, not an assertion
that a nonextendible path exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalSynchronizedSpectralCascade
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## One component is controlled by the exact scalar H³ energy -/

/--
Every physical velocity-component spectral H³ state is bounded by the square
root of the exact normalized H³ energy at the same strict time.
-/
theorem norm_terminalVelocityComponentSpectralStateAt_le_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    norm
      (
        h3TerminalVelocityComponentSpectralStateAt
          hH3 j t ht
      )
      ≤
    Real.sqrt
      (velocityH3EnergyAt u t) := by

  let hInt :
      VelocityH3IntegrableAt
        u t :=
    hH3.velocity_h3_integrable
      t ht

  let hMeas :
      VelocityH3MeasurableAt
        u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      ht

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      ht
      hInt

  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier

  have hStateEq :
      h3TerminalVelocityComponentSpectralStateAt
          hH3 j t ht
        =
      U j := by
    rfl

  have hCoordinate :
      norm (U j)
        ≤
      norm U :=
    h3SpectralFinVector_coordinate_norm_le
      U j

  have hState :
      norm U
        ≤
      Real.sqrt
        (velocityH3EnergyAt u t) := by

    dsimp only [U]

    exact
      norm_velocityH3SpectralStateAt_le_sqrt_energy
        hFourier

  rw [hStateEq]

  exact
    hCoordinate.trans
      hState

/-! ## A strict terminal sequence tends through the left-neighborhood filter -/

/--
A sequence converging to `T` in the ordinary topology and staying strictly
below `T` also converges to the left-neighborhood filter `𝓝[<] T`.
-/
theorem tendsto_nhdsLT_of_tendsto_nhds_of_strict_lt
    {τ : ℕ → ℝ}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hStrict :
      ∀ n : ℕ,
        τ n < T) :
    Tendsto τ atTop (𝓝[<] T) := by

  exact
    tendsto_inf.2
      ⟨
        hTau,
        tendsto_principal.2
          (
            Eventually.of_forall
              (
                fun n =>
                  hStrict n
              )
          )
      ⟩

/-! ## Component escape forces scalar H³-energy escape on the same sequence -/

/--
If one fixed physical component spectral H³ norm tends to `+∞`, then the exact
canonical H³ energy tends to `+∞` along the same strict sequence.
-/
theorem velocityH3EnergyAt_comp_tendsto_atTop_of_componentSpectralNorm_tendsto_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hComponent :
      Tendsto
        (
          fun n : ℕ =>
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3
                  j
                  (τ n)
                  (hTauStrict n)
              )
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          velocityH3EnergyAt u (τ n)
      )
      atTop
      atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  let R : ℝ :=
    max 1 M

  have hComponentLarge :
      ∀ᶠ n : ℕ in atTop,
        R
          ≤
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3
              j
              (τ n)
              (hTauStrict n)
          ) :=
    hComponent.eventually
      (eventually_ge_atTop R)

  filter_upwards
    [hComponentLarge]
    with n hn

  let E : ℝ :=
    velocityH3EnergyAt u (τ n)

  let S : ℝ :=
    Real.sqrt E

  have hComponentBound :
      norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3
              j
              (τ n)
              (hTauStrict n)
          )
        ≤
      S := by

    dsimp only [S, E]

    exact
      norm_terminalVelocityComponentSpectralStateAt_le_sqrt_energy
        hH3
        j
        (hTauStrict n)

  have hEOne :
      1 ≤ E := by

    dsimp only [E]

    exact
      one_le_velocityH3EnergyAt
        u
        (τ n)

  have hENonneg :
      0 ≤ E := by
    linarith

  have hSNonneg :
      0 ≤ S := by

    dsimp only [S]

    exact
      Real.sqrt_nonneg E

  have hSSq :
      S ^ 2 = E := by

    dsimp only [S]

    exact
      Real.sq_sqrt
        hENonneg

  have hSOne :
      1 ≤ S := by

    have hRone :
        1 ≤ R := by

      dsimp only [R]

      exact
        le_max_left
          1 M

    exact
      hRone.trans
        (hn.trans hComponentBound)

  have hSLeE :
      S ≤ E := by
    nlinarith

  have hMLeR :
      M ≤ R := by

    dsimp only [R]

    exact
      le_max_right
        1 M

  exact
    hMLeR.trans
      (
        hn.trans
          (
            hComponentBound.trans
              hSLeE
          )
      )

/-! ## Synchronized fixed-component / dissipation / frequency cascade -/

/--
Hypothetical nonextension produces one fixed physical velocity component and
one strict terminal sequence on which all principal spectral and normalized
dissipative terminal pathologies occur simultaneously.
-/
theorem exists_terminal_velocityComponent_synchronizedSpectralDissipationCascade_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    ∃ j : Fin 3,
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
                      j
                      (τ n)
                      (hTauStrict n)
                  )
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3DissipationAt u (τ n)
                  /
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TopCharacteristicFrequencyAt
                  u
                  (τ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TopCharacteristicLengthAt
                  u
                  (τ n)
            )
            atTop
            (𝓝 0) := by

  obtain
    ⟨
      j,
      τ,
      hTauStrict,
      hTauClass,
      hTau,
      hComponent
    ⟩ :=
    exists_terminal_velocityComponentSpectralNorm_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hTauLT :
      Tendsto
        τ
        atTop
        (𝓝[<] T) :=
    tendsto_nhdsLT_of_tendsto_nhds_of_strict_lt
      hTau
      (fun n => (hTauStrict n).2)

  have hEnergy :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop :=
    velocityH3EnergyAt_comp_tendsto_atTop_of_componentSpectralNorm_tendsto_atTop
      hH3
      j
      hTauStrict
      hComponent

  have hDissipationRatio :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (τ n)
              /
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    exact
      (
        velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
      ).comp
        hTauLT

  have hFrequency :
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicFrequencyAt
              u
              (τ n)
        )
        atTop
        atTop := by

    exact
      (
        h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
      ).comp
        hTauLT

  have hLength :
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicLengthAt
              u
              (τ n)
        )
        atTop
        (𝓝 0) := by

    exact
      (
        h3TopCharacteristicLengthAt_tendsto_zero_nhdsLT_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
      ).comp
        hTauLT

  exact
    ⟨
      j,
      τ,
      hTauStrict,
      hTauClass,
      hTau,
      hComponent,
      hEnergy,
      hDissipationRatio,
      hFrequency,
      hLength
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
