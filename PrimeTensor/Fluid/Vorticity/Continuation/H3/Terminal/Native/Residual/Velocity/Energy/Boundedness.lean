import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Residual.Velocity.Component.Boundedness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Dichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Energy.Envelope

/-!
# Componentwise spectral boundedness is exactly terminal H³-energy boundedness

The terminal component branch has now reached its weakest useful endpoint:
eventual boundedness of the three physical velocity-component spectral H³
norms.

Because the encoded velocity state has exactly three coordinates and satisfies

    1 + ∑ j, ‖U_j(t)‖² = velocityH3EnergyAt u t,

this condition is equivalent to the standard scalar terminal H³-energy
boundedness criterion already used by the restart theorem.

This file proves both directions.

* If all three component spectral states are eventually bounded, synchronize
  their three terminal tails and take one common bound `B`.  Then

      velocityH3EnergyAt u t ≤ 1 + 3 B²

  on a common terminal tail.

* Conversely, a scalar H³-energy ceiling `M` bounds the complete encoded
  spectral velocity state by `sqrt M`, hence bounds each component.

Thus the fixed-component terminal analysis has not introduced a stronger
continuation hypothesis: it lands exactly on the canonical terminal H³-energy
boundedness frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalVelocityEnergyBoundedness
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Pointwise finite-coordinate energy estimate -/

/--
If all three scalar spectral component norms are bounded by one nonnegative
number `B` at one strict preterminal time, then the exact normalized H³ energy
is bounded by `1 + 3 B²`.
-/
theorem velocityH3EnergyAt_le_one_add_three_mul_sq_of_terminalComponentNormBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t B : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T)
    (hB :
      0 ≤ B)
    (hComponent :
      ∀ j : Fin 3,
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3 j t ht
          )
          ≤ B) :
    velocityH3EnergyAt u t
      ≤
    1 + 3 * B ^ 2 := by

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
      ∀ j : Fin 3,
        h3TerminalVelocityComponentSpectralStateAt
            hH3 j t ht
          =
        U j := by

    intro j

    rfl

  have hEach :
      ∀ j : Fin 3,
        norm (U j) ^ 2
          ≤
        B ^ 2 := by

    intro j

    have hNorm :
        norm (U j) ≤ B := by

      rw [← hStateEq j]

      exact
        hComponent j

    nlinarith [
      norm_nonneg (U j)
    ]

  have hSum :
      h3SpectralVelocitySquareEnergy U
        ≤
      3 * B ^ 2 := by

    unfold h3SpectralVelocitySquareEnergy

    calc
      (∑ j : Fin 3, norm (U j) ^ 2)
          ≤
        ∑ _j : Fin 3, B ^ 2 :=
        Finset.sum_le_sum
          (fun j _ => hEach j)

      _ =
        3 * B ^ 2 := by
        norm_num

  have hExact :
      1 + h3SpectralVelocitySquareEnergy U
        =
      velocityH3EnergyAt u t := by

    dsimp only [U]

    exact
      one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
        hFourier

  linarith

/-! ## Three component tails give one scalar H³-energy tail -/

/--
Eventual boundedness of the three physical spectral components produces one
finite scalar H³-energy ceiling on a common terminal tail.
-/
theorem exists_velocityH3EnergyBoundOnTail_of_velocityEventuallyBounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hBounded :
      H3TerminalVelocityEventuallyBounded
        hH3) :
    ∃ b M : ℝ,
      b ∈ Set.Ioo (0 : ℝ) T
        ∧
      1 ≤ M
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ico b T →
          velocityH3EnergyAt u t ≤ M := by

  obtain
    ⟨
      b0,
      B0,
      hb0T,
      h0
    ⟩ :=
    hBounded (0 : Fin 3)

  obtain
    ⟨
      b1,
      B1,
      hb1T,
      h1
    ⟩ :=
    hBounded (1 : Fin 3)

  obtain
    ⟨
      b2,
      B2,
      hb2T,
      h2
    ⟩ :=
    hBounded (2 : Fin 3)

  let c : ℝ :=
    max
      a
      (max b0 (max b1 b2))

  let b : ℝ :=
    (c + T) / 2

  let B : ℝ :=
    max
      0
      (max B0 (max B1 B2))

  let M : ℝ :=
    1 + 3 * B ^ 2

  have hcT :
      c < T := by

    dsimp only [c]

    exact
      max_lt
        hClass.terminal_start.2
        (
          max_lt
            hb0T
            (
              max_lt
                hb1T
                hb2T
            )
        )

  have hac :
      a ≤ c := by

    dsimp only [c]

    exact
      le_max_left _ _

  have hb0c :
      b0 ≤ c := by

    dsimp only [c]

    exact
      le_trans
        (le_max_left b0 (max b1 b2))
        (le_max_right a (max b0 (max b1 b2)))

  have hb1c :
      b1 ≤ c := by

    dsimp only [c]

    exact
      le_trans
        (
          le_trans
            (le_max_left b1 b2)
            (le_max_right b0 (max b1 b2))
        )
        (le_max_right a (max b0 (max b1 b2)))

  have hb2c :
      b2 ≤ c := by

    dsimp only [c]

    exact
      le_trans
        (
          le_trans
            (le_max_right b1 b2)
            (le_max_right b0 (max b1 b2))
        )
        (le_max_right a (max b0 (max b1 b2)))

  have hcb :
      c < b := by

    dsimp only [b]

    linarith

  have hbT :
      b < T := by

    dsimp only [b]

    linarith

  have hbPos :
      0 < b := by

    have haPos :
        0 < a :=
      hClass.terminal_start.1

    have hab :
        a < b :=
      lt_of_le_of_lt
        hac
        hcb

    exact
      lt_trans
        haPos
        hab

  have hB :
      0 ≤ B := by

    dsimp only [B]

    exact
      le_max_left _ _

  have hB0 :
      B0 ≤ B := by

    dsimp only [B]

    exact
      le_trans
        (
          le_trans
            (le_max_left B0 (max B1 B2))
            (le_max_right 0 (max B0 (max B1 B2)))
        )
        le_rfl

  have hB1 :
      B1 ≤ B := by

    dsimp only [B]

    exact
      le_trans
        (
          le_trans
            (
              le_trans
                (le_max_left B1 B2)
                (le_max_right B0 (max B1 B2))
            )
            (le_max_right 0 (max B0 (max B1 B2)))
        )
        le_rfl

  have hB2 :
      B2 ≤ B := by

    dsimp only [B]

    exact
      le_trans
        (
          le_trans
            (
              le_trans
                (le_max_right B1 B2)
                (le_max_right B0 (max B1 B2))
            )
            (le_max_right 0 (max B0 (max B1 B2)))
        )
        le_rfl

  have hM :
      1 ≤ M := by

    dsimp only [M]

    nlinarith [
      sq_nonneg B
    ]

  refine
    ⟨
      b,
      M,
      ⟨hbPos, hbT⟩,
      hM,
      ?_
    ⟩

  intro t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_of_lt_of_le
        hbPos
        ht.1,
      ht.2
    ⟩

  have hbt :
      b ≤ t :=
    ht.1

  have hb0t :
      b0 < t :=
    lt_of_le_of_lt
      hb0c
      (
        lt_of_lt_of_le
          hcb
          hbt
      )

  have hb1t :
      b1 < t :=
    lt_of_le_of_lt
      hb1c
      (
        lt_of_lt_of_le
          hcb
          hbt
      )

  have hb2t :
      b2 < t :=
    lt_of_le_of_lt
      hb2c
      (
        lt_of_lt_of_le
          hcb
          hbt
      )

  have hComponent :
      ∀ j : Fin 3,
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3 j t htAbs
          )
          ≤ B := by

    intro j

    fin_cases j

    · exact
        (h0 t htAbs hb0t).trans
          hB0

    · exact
        (h1 t htAbs hb1t).trans
          hB1

    · exact
        (h2 t htAbs hb2t).trans
          hB2

  have hEnergy :
      velocityH3EnergyAt u t
        ≤
      1 + 3 * B ^ 2 :=
    velocityH3EnergyAt_le_one_add_three_mul_sq_of_terminalComponentNormBound
      hH3
      htAbs
      hB
      hComponent

  simpa only [M] using
    hEnergy

/-! ## Scalar terminal H³ energy bound gives component bounds -/

/--
A finite scalar H³-energy ceiling on one terminal tail bounds every physical
spectral component on that tail by `sqrt M`.
-/
theorem velocityEventuallyBounded_of_velocityH3EnergyBoundOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (ha :
      a ∈ Set.Ioo (0 : ℝ) T)
    (_hM :
      1 ≤ M)
    (hEnergy :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          velocityH3EnergyAt u t ≤ M) :
    H3TerminalVelocityEventuallyBounded
      hH3 := by

  intro j

  refine
    ⟨
      a,
      Real.sqrt M,
      ha.2,
      ?_
    ⟩

  intro t ht hat

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt hat,
      ht.2
    ⟩

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
      Real.sqrt (velocityH3EnergyAt u t) := by

    dsimp only [U]

    exact
      norm_velocityH3SpectralStateAt_le_sqrt_energy
        hFourier

  have hEnergyT :
      velocityH3EnergyAt u t ≤ M :=
    hEnergy
      t htTail

  have hSqrt :
      Real.sqrt (velocityH3EnergyAt u t)
        ≤
      Real.sqrt M :=
    Real.sqrt_le_sqrt
      hEnergyT

  rw [hStateEq]

  exact
    hCoordinate.trans
      (hState.trans hSqrt)

/-! ## Exact equivalence of the two terminal boundedness formulations -/

/--
For an admissible H³ path with an energy-class tail, eventual boundedness of
the three physical spectral components is equivalent to existence of one
finite canonical H³-energy ceiling on some terminal tail.
-/
theorem velocityEventuallyBounded_iff_exists_velocityH3EnergyBoundOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    H3TerminalVelocityEventuallyBounded
        hH3
      ↔
    ∃ b M : ℝ,
      b ∈ Set.Ioo (0 : ℝ) T
        ∧
      1 ≤ M
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ico b T →
          velocityH3EnergyAt u t ≤ M := by

  constructor

  · intro hBounded

    exact
      exists_velocityH3EnergyBoundOnTail_of_velocityEventuallyBounded
        hH3
        hClass
        hBounded

  · rintro
      ⟨
        b,
        M,
        hb,
        hM,
        hEnergy
      ⟩

    exact
      velocityEventuallyBounded_of_velocityH3EnergyBoundOnTail
        hH3
        hb
        hM
        hEnergy

/-! ## Direct splice into the canonical restart theorem -/

/--
The componentwise boundedness continuation criterion factors through the
existing scalar terminal H³-energy restart criterion.
-/
theorem smoothContinuationExtension_of_velocityEventuallyBounded_via_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hBounded :
      H3TerminalVelocityEventuallyBounded
        hH3) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  obtain
    ⟨
      b,
      M,
      hb,
      hM,
      hEnergy
    ⟩ :=
    exists_velocityH3EnergyBoundOnTail_of_velocityEventuallyBounded
      hH3
      hClass
      hBounded

  exact
    h3PathExtension_of_velocityH3EnergyBoundOnTail
      hH3
      hb
      hM
      hEnergy

end

end Euclidean
end Bridge
end PrimeTensor
