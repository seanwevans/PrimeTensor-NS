import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Sequence
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Endpoint.Third.Jet.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy

/-!
# Terminal third-order H³ blowup

The previous terminal derivative theorem shows that a hypothetical
nonextendible H³ path must eject its blowup from the bounded kinetic block into

    E₁ + E₂ + E₃.

The existing spectral endpoint algebra is stronger.  At one fixed H³ slice,
the weighted H³ Fourier density satisfies

    W₃(ξ)² |F(ξ)|²
      ≤
    3 ( |F(ξ)|² + Σᵢₖₗ |mᵢₖₗ(ξ) F(ξ)|² ).

Fourier compatibility identifies the cubic symbols with the concrete ordered
third derivative slots.  Plancherel then gives the physical fixed-time bound

    E_H3(t) ≤ 1 + 3 (E₀(t) + E₃(t)).

Since the zeroth-order kinetic block is antitone on every H³ energy-class tail,
it remains uniformly bounded there.  Consequently any terminal sequence on
which the full H³ energy tends to `+∞` must also satisfy

    E₃(t_n) -> +∞.

Thus a hypothetical nonextendible path has genuine top-order H³ blowup; the
growth cannot remain confined to the first- and second-order blocks.

This remains a necessary-condition theorem.  It does not assert existence of a
nonextendible solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalThird
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fixed-time endpoint interpolation -/

/--
For one scalar velocity component, the complete weighted H³ spectral square
norm is controlled by only its zeroth and ordered third Fourier-jet squares.
-/
theorem norm_velocityH3SpectralScalarAt_sq_le_three_base_third
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ‖velocityH3SpectralScalarAt
        u t hInt hMeas hFourier j‖ ^ 2
      ≤
    3 *
      (
        ‖velocityH3FourierJetAt
            u t hInt hMeas (h3JetSlot0 j)‖ ^ 2
          +
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt
              u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2
      ) := by

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3SpectralScalarAt
              u t hInt hMeas hFourier j ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp
      (velocityH3SpectralScalarAt
        u t hInt hMeas hFourier j)).norm.integrable_sq

  have h0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3FourierJetAt
              u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt
        u t hInt hMeas (h3JetSlot0 j))).norm.integrable_sq

  have h3 :
      ∀ i k l : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2)
          volume := by
    intro i k l
    exact
      (MeasureTheory.Lp.memLp
        (velocityH3FourierJetAt
          u t hInt hMeas (h3JetSlot3 j i k l))).norm.integrable_sq

  have h3sum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2)
        volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    exact h3 i k l

  have hEndpoint :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖velocityH3FourierJetAt
              u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
            +
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2)
        volume :=
    h0.add h3sum

  have hRight :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          3 *
            (
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
                +
              ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                ‖velocityH3FourierJetAt
                    u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
            ))
        volume :=
    hEndpoint.const_mul 3

  have hAE :
      (fun ξ : H3FourierPoint3 =>
        ‖velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j ξ‖ ^ 2)
        ≤ᵐ[volume]
      (fun ξ : H3FourierPoint3 =>
        3 *
          (
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
              +
            ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
          )) := by

    filter_upwards
      [
        velocityH3SpectralScalarAt_ae hFourier j,
        velocityH3FourierCompatibleAt_orderThree_all_ae hFourier j
      ]
      with ξ hState hThird

    rw [hState]

    have hPoint :=
      h3SobolevFrequencyWeight_mul_sub_norm_sq_le_three_base_third_symbol
        ξ
        (velocityH3BaseFourierAt u t hInt hMeas j ξ)
        0

    simp only [
      sub_zero,
      mul_zero
    ] at hPoint

    unfold velocityH3WeightedBaseFourierRaw

    have hThirdNorm :
        ∀ i k l : Fin 3,
          ‖h3FourierDerivativeSymbol3 i k l ξ *
              velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2
            =
          ‖velocityH3FourierJetAt
              u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2 := by

      intro i k l

      exact
        congrArg
          (fun z : ℂ => ‖z‖ ^ 2)
          (hThird i k l).symm

    simp_rw [hThirdNorm] at hPoint

    simpa only [
      velocityH3BaseFourierAt
    ] using hPoint

  have hIntegral :=
    integral_mono_ae
      hLeft
      hRight
      hAE

  have h3int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt
              u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
        =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt
              u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume := by

    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt
              u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
            ∂volume := by

              simpa using
                (integral_finsetSum (μ := volume) Finset.univ
                  (fun i _ => by
                    apply integrable_finsetSum
                    intro k hk
                    apply integrable_finsetSum
                    intro l hl
                    exact h3 i k l))

      _ =
        ∑ i : Fin 3, ∑ k : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
            ∂volume := by

              apply Finset.sum_congr rfl
              intro i hi

              simpa using
                (integral_finsetSum (μ := volume) Finset.univ
                  (fun k _ => by
                    apply integrable_finsetSum
                    intro l hl
                    exact h3 i k l))

      _ =
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
          ∂volume := by

              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro k hk

              simpa using
                (integral_finsetSum (μ := volume) Finset.univ
                  (fun l _ => h3 i k l))

  rw [integral_const_mul] at hIntegral
  rw [integral_add h0 h3sum, h3int] at hIntegral

  simp_rw [
    ← h3FourierComplexL2_norm_sq_eq_integral_norm_sq
  ] at hIntegral

  exact hIntegral

/--
The full normalized physical H³ energy at one Fourier-compatible slice is
controlled by only the zeroth and third physical derivative blocks:

    E_H3 ≤ 1 + 3 (E₀ + E₃).
-/
theorem velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3EnergyAt u t
      ≤
    1
      +
    3 *
      (
        velocityH3Energy0At u t
          +
        velocityH3Energy3At u t
      ) := by

  have hComponent :
      ∀ j : Fin 3,
        ‖velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j‖ ^ 2
          ≤
        3 *
          (
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot0 j)‖ ^ 2
              +
            ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2
          ) := by

    intro j

    exact
      norm_velocityH3SpectralScalarAt_sq_le_three_base_third
        hFourier
        j

  have hSum :
      (∑ j : Fin 3,
        ‖velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j‖ ^ 2)
        ≤
      ∑ j : Fin 3,
        3 *
          (
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot0 j)‖ ^ 2
              +
            ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2
          ) :=
    Finset.sum_le_sum
      (fun j hj => hComponent j)

  have hSpectral :
      h3SpectralVelocitySquareEnergy
          (velocityH3SpectralStateAt
            u t hInt hMeas hFourier)
        ≤
      3 *
        (
          (∑ j : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot0 j)‖ ^ 2)
            +
          (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2)
        ) := by

    unfold
      h3SpectralVelocitySquareEnergy
      velocityH3SpectralStateAt

    calc
      (∑ j : Fin 3,
        ‖velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j‖ ^ 2)
          ≤
        ∑ j : Fin 3,
          3 *
            (
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot0 j)‖ ^ 2
                +
              ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
                ‖velocityH3FourierJetAt
                    u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2
            ) :=
        hSum

      _ =
        3 *
          (
            (∑ j : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot0 j)‖ ^ 2)
              +
            (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt
                  u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2)
          ) := by

        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib]

  have h0 :
      (∑ j : Fin 3,
        ‖velocityH3FourierJetAt
            u t hInt hMeas (h3JetSlot0 j)‖ ^ 2)
        =
      velocityH3Energy0At u t := by

    simp_rw [
      velocityH3FourierJetAt_apply,
      norm_h3ScalarFourierL2
    ]

    simpa only [h3JetSlot0] using
      (velocityH3L2JetAt_squareEnergy0_eq
        hInt hMeas)

  have h3 :
      (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ‖velocityH3FourierJetAt
            u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2)
        =
      velocityH3Energy3At u t := by

    simp_rw [
      velocityH3FourierJetAt_apply,
      norm_h3ScalarFourierL2
    ]

    simpa only [
      h3JetSlot3,
      Fintype.sum_prod_type
    ] using
      (velocityH3L2JetAt_squareEnergy3_eq
        hInt hMeas)

  have hExact :
      1
          +
        h3SpectralVelocitySquareEnergy
          (velocityH3SpectralStateAt
            u t hInt hMeas hFourier)
        =
      velocityH3EnergyAt u t :=
    one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
      hFourier

  calc
    velocityH3EnergyAt u t
        =
      1
        +
      h3SpectralVelocitySquareEnergy
        (velocityH3SpectralStateAt
          u t hInt hMeas hFourier) :=
      hExact.symm

    _ ≤
      1
        +
      3 *
        (
          (∑ j : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot0 j)‖ ^ 2)
            +
          (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt
                u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2)
        ) := by
      simpa only [add_comm] using
        (add_le_add_left hSpectral 1)

    _ =
      1
        +
      3 *
        (
          velocityH3Energy0At u t
            +
          velocityH3Energy3At u t
        ) := by
      rw [h0, h3]

/-- H³-path version of the zeroth/third endpoint interpolation. -/
theorem velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3EnergyAt u t
      ≤
    1
      +
    3 *
      (
        velocityH3Energy0At u t
          +
        velocityH3Energy3At u t
      ) := by

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

  exact
    velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3
      hFourier

/-! ## Terminal third-order concentration -/

/--
A hypothetical nonextendible admissible H³ path admits a terminal sequence
along which the *third-order physical H³ energy block itself* tends to `+∞`.
-/
theorem exists_velocityH3Energy3At_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ τ : ℕ → ℝ,
      (
        ∀ n : ℕ,
          τ n < T
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3Energy3At u (τ n))
        atTop
        atTop := by

  obtain
    ⟨τ, hτ, hτTendsto, hEnergyTendsto⟩ :=
    exists_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hTauAbove :
      ∀ᶠ n : ℕ in atTop,
        b < τ n :=
    (tendsto_order.1 hτTendsto).1
      b
      hb.2

  have hKineticBound :
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n)
          ≤
        velocityH3Energy0At u b := by

    filter_upwards [hTauAbove] with n hbn

    have hτMem :
        τ n ∈ Set.Ioo a T :=
      ⟨
        lt_trans hb.1 hbn,
        (hτ n).1.2
      ⟩

    exact
      hKineticAnti
        hb
        hτMem
        (le_of_lt hbn)

  have hEndpointBound :
      ∀ᶠ n : ℕ in atTop,
        velocityH3EnergyAt u (τ n)
          ≤
        1
          +
        3 *
          (
            velocityH3Energy0At u (τ n)
              +
            velocityH3Energy3At u (τ n)
          ) := by

    filter_upwards [hTauAbove] with n hbn

    have hτMem :
        τ n ∈ Set.Ioo a T :=
      ⟨
        lt_trans hb.1 hbn,
        (hτ n).1.2
      ⟩

    exact
      velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
        hH3
        hClass
        hτMem

  have hThirdTendsto :
      Tendsto
        (fun n : ℕ =>
          velocityH3Energy3At u (τ n))
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hEnergyLarge :
        ∀ᶠ n : ℕ in atTop,
          1
              +
            3 *
              (
                velocityH3Energy0At u b
                  +
                M
              )
            <
          velocityH3EnergyAt u (τ n) :=
      hEnergyTendsto.eventually
        (
          eventually_gt_atTop
            (
              1
                +
              3 *
                (
                  velocityH3Energy0At u b
                    +
                  M
                )
            )
        )

    filter_upwards
      [hEnergyLarge, hKineticBound, hEndpointBound]
      with n hLarge hE0 hEndpoint

    linarith

  exact
    ⟨
      τ,
      (fun n => (hτ n).1.2),
      hτTendsto,
      hThirdTendsto
    ⟩

/--
Equivalent near-terminal formulation: the third-order physical H³ energy is
arbitrarily large arbitrarily near a hypothetical nonextendible terminal time.
-/
theorem velocityH3Energy3At_arbitrarilyLarge_arbitrarilyNearTerminal_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ ε : ℝ,
      0 < ε →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo (T - ε) T
            ∧
          M < velocityH3Energy3At u t := by

  intro ε hε M

  obtain
    ⟨τ, hτT, hτTendsto, hThirdTendsto⟩ :=
    exists_velocityH3Energy3At_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hNear :
      ∀ᶠ n : ℕ in atTop,
        T - ε < τ n :=
    (tendsto_order.1 hτTendsto).1
      (T - ε)
      (by linarith)

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        M < velocityH3Energy3At u (τ n) :=
    hThirdTendsto.eventually
      (eventually_gt_atTop M)

  obtain ⟨n, hnNear, hnLarge⟩ :=
    (hNear.and hLarge).exists

  exact
    ⟨
      τ n,
      ⟨
        hnNear,
        hτT n
      ⟩,
      hnLarge
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
