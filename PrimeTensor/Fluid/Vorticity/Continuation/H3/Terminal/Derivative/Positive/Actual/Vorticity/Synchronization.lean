import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKM.Vorticity.Envelope.Divergence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Energy.Envelope

/-!
# Actual vorticity synchronized with the canonical positive-growth cascade

The preceding BKM frequency argument proves that every scalar vorticity
envelope diverges on the canonical positive-growth terminal sequence.  To turn
that statement into an actual vorticity-amplitude statement at the same times,
we introduce the minimal common componentwise upper bound at each time.

For fixed `u,t`, let

    S(u,t) =
      { M : ℝ |
          ∀ x,
            |ωₓ(t,x)| ≤ M ∧
            |ωᵧ(t,x)| ≤ M ∧
            |ω_z(t,x)| ≤ M }.

The H³ square-root-energy envelope proves `S(u,t)` is nonempty on every strict
preterminal slice.  Every member of `S(u,t)` is nonnegative, so the infimum

    Ω∞(u,t) = inf S(u,t)

is well-defined.  By `le_csInf`, every actual vorticity component magnitude is
bounded by `Ω∞(u,t)`, hence `Ω∞` itself is a vorticity envelope.

Conversely, if `M < Ω∞(u,t)`, then `M` cannot itself be a common upper bound.
Therefore some spatial point and some actual vorticity component exceeds `M`.

Applying the previous "every envelope diverges" theorem to `Ω∞` gives

    Ω∞(u,σ_n) -> +∞

on the canonical positive-growth sequence.  Choosing, at each `n`, an actual
component exceeding `Ω∞(u,σ_n) - 1` produces spatial points `y_n` for which

    max(|ωₓ|, |ωᵧ|, |ω_z|)(σ_n,y_n) -> +∞.

Thus the same sequence simultaneously carries:

    E(σ_n) -> +∞,
    D(σ_n)/E(σ_n) -> +∞,
    (-T_H3(σ_n))/E(σ_n) -> +∞,
    Λ₃(σ_n) -> +∞,
    actual vorticity amplitude -> +∞.

This synchronizes the physical curl blowup with the canonical positive-energy-
growth cascade.  It remains a necessary consequence of hypothetical
nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Minimal common vorticity upper bound -/

/--
The set of common scalar upper bounds for all three actual vorticity
components at one fixed time.
-/
def h3VorticityCommonUpperBoundsAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    Set ℝ :=
  {
    M : ℝ |
      ∀ x : Point3,
        abs
          (
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
          ≤
        M
          ∧
        abs
          (
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
          ≤
        M
          ∧
        abs
          (
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
          ≤
        M
  }

/--
The minimal common componentwise vorticity upper bound at one time.
-/
noncomputable def h3MinimalVorticityEnvelopeAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    ℝ :=
  sInf
    (h3VorticityCommonUpperBoundsAt u t)

/--
Every common vorticity upper bound is nonnegative.  Hence the upper-bound set
is bounded below by zero, independently of whether it is nonempty.
-/
theorem h3VorticityCommonUpperBoundsAt_bddBelow
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    BddBelow
      (h3VorticityCommonUpperBoundsAt u t) := by

  refine
    ⟨
      0,
      ?_
    ⟩

  intro M hM

  have hAt :
      abs
        (
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t
            (0 : Point3)
        )
        ≤
      M := by

    exact
      (
        show
          ∀ x : Point3,
            abs
              (
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
              ≤
            M
              ∧
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
              ≤
            M
              ∧
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
              ≤
            M
          from
            hM
      )
        (0 : Point3)
        |>.1

  exact
    le_trans
      (abs_nonneg _)
      hAt

/--
On every strict H³-path slice the common-upper-bound set is nonempty, because
the canonical square-root-energy vorticity envelope supplies one member.
-/
theorem h3VorticityCommonUpperBoundsAt_nonempty_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    (
      h3VorticityCommonUpperBoundsAt
        u t
    ).Nonempty := by

  let G : ℝ :=
    h3PathCanonicalVorticitySqrtEnergyEnvelope
      u t

  refine
    ⟨
      G,
      ?_
    ⟩

  have hEnvelope :
      VorticityEnvelope
        u
        (h3PathCanonicalVorticitySqrtEnergyEnvelope u)
        t :=
    h3PathCanonicalVorticitySqrtEnergyEnvelope_at
      hH3
      ht

  show
    ∀ x : Point3,
      abs
        (
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      G
        ∧
      abs
        (
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      G
        ∧
      abs
        (
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      G

  exact
    hEnvelope

/--
The minimal common vorticity envelope is nonnegative on every strict H³-path
slice.
-/
theorem h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    0
      ≤
    h3MinimalVorticityEnvelopeAt u t := by

  unfold h3MinimalVorticityEnvelopeAt

  apply
    le_csInf
      (
        h3VorticityCommonUpperBoundsAt_nonempty_of_h3Path
          hH3
          ht
      )

  intro M hM

  have hAt :
      abs
        (
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t
            (0 : Point3)
        )
        ≤
      M := by

    exact
      (
        show
          ∀ x : Point3,
            abs
              (
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
              ≤
            M
              ∧
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
              ≤
            M
              ∧
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
              ≤
            M
          from
            hM
      )
        (0 : Point3)
        |>.1

  exact
    le_trans
      (abs_nonneg _)
      hAt

/--
The infimum of all common upper bounds is itself a common upper bound, hence a
genuine vorticity envelope on every strict H³-path slice.
-/
theorem vorticityEnvelope_h3MinimalVorticityEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    VorticityEnvelope
      u
      (h3MinimalVorticityEnvelopeAt u)
      t := by

  have hNonempty :=
    h3VorticityCommonUpperBoundsAt_nonempty_of_h3Path
      hH3
      ht

  intro x

  constructor

  · unfold h3MinimalVorticityEnvelopeAt

    apply
      le_csInf
        hNonempty

    intro M hM

    exact
      (
        show
          ∀ y : Point3,
            abs
              (
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t y
              )
              ≤
            M
              ∧
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t y
              )
              ≤
            M
              ∧
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t y
              )
              ≤
            M
          from
            hM
      )
        x
        |>.1

  · constructor

    · unfold h3MinimalVorticityEnvelopeAt

      apply
        le_csInf
          hNonempty

      intro M hM

      exact
        (
          show
            ∀ y : Point3,
              abs
                (
                  realVorticityX
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t y
                )
                ≤
              M
                ∧
              abs
                (
                  realVorticityY
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t y
                )
                ≤
              M
                ∧
              abs
                (
                  realVorticityZ
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t y
                )
                ≤
              M
            from
              hM
        )
          x
          |>.2.1

    · unfold h3MinimalVorticityEnvelopeAt

      apply
        le_csInf
          hNonempty

      intro M hM

      exact
        (
          show
            ∀ y : Point3,
              abs
                (
                  realVorticityX
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t y
                )
                ≤
              M
                ∧
              abs
                (
                  realVorticityY
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t y
                )
                ≤
              M
                ∧
              abs
                (
                  realVorticityZ
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t y
                )
                ≤
              M
            from
              hM
        )
          x
          |>.2.2

/-! ## A strict lower threshold forces an actual component witness -/

/--
Any number strictly below the minimal common vorticity envelope is exceeded by
an actual vorticity component at some spatial point.
-/
theorem exists_actualVorticityComponent_gt_of_lt_h3MinimalVorticityEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t M : ℝ}
    (hM :
      M
        <
      h3MinimalVorticityEnvelopeAt u t) :
    ∃ x : Point3,
      (
        M
          <
        abs
          (
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
      )
        ∨
      (
        M
          <
        abs
          (
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
      )
        ∨
      (
        M
          <
        abs
          (
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
      ) := by

  by_contra hNo

  have hBound :
      M
        ∈
      h3VorticityCommonUpperBoundsAt
        u t := by

    show
      ∀ x : Point3,
        abs
          (
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
          ≤
        M
          ∧
        abs
          (
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
          ≤
        M
          ∧
        abs
          (
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
          ≤
        M

    intro x

    constructor

    · by_contra hNot

      have hGt :
          M
            <
          abs
            (
              realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            ) :=
        lt_of_not_ge
          hNot

      exact
        hNo
          ⟨
            x,
            Or.inl hGt
          ⟩

    · constructor

      · by_contra hNot

        have hGt :
            M
              <
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              ) :=
          lt_of_not_ge
            hNot

        exact
          hNo
            ⟨
              x,
              Or.inr
                (Or.inl hGt)
            ⟩

      · by_contra hNot

        have hGt :
            M
              <
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              ) :=
          lt_of_not_ge
            hNot

        exact
          hNo
            ⟨
              x,
              Or.inr
                (Or.inr hGt)
            ⟩

  have hInfLe :
      h3MinimalVorticityEnvelopeAt u t
        ≤
      M := by

    unfold h3MinimalVorticityEnvelopeAt

    exact
      csInf_le
        (
          h3VorticityCommonUpperBoundsAt_bddBelow
            u t
        )
        hBound

  exact
    (not_lt_of_ge hInfLe)
      hM

/-! ## Synchronization with the positive-growth cascade -/

/--
Under hypothetical nonextension, actual vorticity amplitude diverges on the
same canonical positive-growth sequence that carries the full H³
energy/dissipation/transport/frequency cascade.
-/
theorem exists_terminal_positiveGrowth_fullCascade_actualVorticity_tendsto_atTop_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
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
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
    ∃
      σ : ℕ → ℝ,
      ∃
        y : ℕ → Point3,
        (
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T
              ∧
            σ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
              ∧
            (n : ℝ)
              <
            deriv (velocityH3EnergyAt u) (σ n)
        )
          ∧
        Tendsto σ atTop (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3EnergyAt u (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3DissipationAt u (σ n)
                /
              velocityH3EnergyAt u (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              (
                - velocityH3TransportDerivativeAt u (σ n)
              )
                /
              velocityH3EnergyAt u (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TopCharacteristicFrequencyAt
                u
                (σ n)
          )
          atTop
          atTop
          ∧
        Tendsto
          (
            fun n : ℕ =>
              max
                (
                  abs
                    (
                      realVorticityX
                        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                        (σ n)
                        (y n)
                    )
                )
                (
                  max
                    (
                      abs
                        (
                          realVorticityY
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            (σ n)
                            (y n)
                        )
                    )
                    (
                      abs
                        (
                          realVorticityZ
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            (σ n)
                            (y n)
                        )
                    )
                )
          )
          atTop
          atTop := by

  let g : ℝ → ℝ :=
    h3MinimalVorticityEnvelopeAt u

  have hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope
            u g s := by

    intro s hs

    have hsAbs :
        s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans
          (
            lt_trans
              hClass.terminal_start.1
              hb.1
          )
          hs.1,
        hs.2
      ⟩

    dsimp only [g]

    exact
      vorticityEnvelope_h3MinimalVorticityEnvelopeAt
        hH3
        hsAbs

  obtain
    ⟨
      σ,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto,
      hFrequencyTendsto,
      hEnvelopeAbsTendsto
    ⟩ :=
    exists_terminal_positiveGrowth_fullCascade_vorticityEnvelope_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      hg

  have hEnvelopeNonneg :
      ∀ n : ℕ,
        0 ≤ g (σ n) := by

    intro n

    have hSigmaAbs :
        σ n ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans
          hClass.terminal_start.1
          (hσ n).1.1,
        (hσ n).1.2
      ⟩

    dsimp only [g]

    exact
      h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path
        hH3
        hSigmaAbs

  have hEnvelopeTendsto :
      Tendsto
        (
          fun n : ℕ =>
            g (σ n)
        )
        atTop
        atTop := by

    have hEq :
        (
          fun n : ℕ =>
            |g (σ n)|
        )
          =
        (
          fun n : ℕ =>
            g (σ n)
        ) := by

      funext n

      rw [
        abs_of_nonneg
          (hEnvelopeNonneg n)
      ]

    rw [hEq] at hEnvelopeAbsTendsto

    exact
      hEnvelopeAbsTendsto

  have hWitness :
      ∀ n : ℕ,
        ∃ x : Point3,
          (
            g (σ n) - 1
              <
            abs
              (
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  (σ n)
                  x
              )
          )
            ∨
          (
            g (σ n) - 1
              <
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  (σ n)
                  x
              )
          )
            ∨
          (
            g (σ n) - 1
              <
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  (σ n)
                  x
              )
          ) := by

    intro n

    apply
      exists_actualVorticityComponent_gt_of_lt_h3MinimalVorticityEnvelopeAt

    dsimp only [g]

    linarith

  choose y hy using
    hWitness

  have hMaxLower :
      ∀ n : ℕ,
        g (σ n) - 1
          <
        max
          (
            abs
              (
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  (σ n)
                  (y n)
              )
          )
          (
            max
              (
                abs
                  (
                    realVorticityY
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (σ n)
                      (y n)
                  )
              )
              (
                abs
                  (
                    realVorticityZ
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (σ n)
                      (y n)
                  )
              )
          ) := by

    intro n

    rcases hy n with hX | hY | hZ

    · exact
        lt_of_lt_of_le
          hX
          (le_max_left _ _)

    · exact
        lt_of_lt_of_le
          hY
          (
            le_trans
              (le_max_left _ _)
              (le_max_right _ _)
          )

    · exact
        lt_of_lt_of_le
          hZ
          (
            le_trans
              (le_max_right _ _)
              (le_max_right _ _)
          )

  have hActualVorticityTendsto :
      Tendsto
        (
          fun n : ℕ =>
            max
              (
                abs
                  (
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (σ n)
                      (y n)
                  )
              )
              (
                max
                  (
                    abs
                      (
                        realVorticityY
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (σ n)
                          (y n)
                      )
                  )
                  (
                    abs
                      (
                        realVorticityZ
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (σ n)
                          (y n)
                      )
                  )
              )
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hEnvelopeEventually :
        ∀ᶠ n : ℕ in atTop,
          M + 1
            ≤
          g (σ n) :=
      hEnvelopeTendsto.eventually
        (eventually_ge_atTop (M + 1))

    filter_upwards
      [
        hEnvelopeEventually
      ]
      with n hn

    have hThreshold :
        M
          ≤
        g (σ n) - 1 := by
      linarith

    exact
      le_of_lt
        (
          lt_of_le_of_lt
            hThreshold
            (hMaxLower n)
        )

  exact
    ⟨
      σ,
      y,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto,
      hFrequencyTendsto,
      hActualVorticityTendsto
    ⟩

/--
Neutral synchronized physical formulation: either smooth continuation exists,
or there is one positive-growth terminal sequence carrying the full scalar,
frequency, and actual-vorticity divergence package.
-/
theorem smoothContinuationExtension_or_terminal_positiveGrowth_fullCascade_actualVorticity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T
    )
      ∨
    (
      ∃
        σ : ℕ → ℝ,
        ∃
          y : ℕ → Point3,
          (
            ∀ n : ℕ,
              σ n ∈ Set.Ioo a T
                ∧
              σ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T
                ∧
              (n : ℝ)
                <
              deriv (velocityH3EnergyAt u) (σ n)
          )
            ∧
          Tendsto σ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3EnergyAt u (σ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3DissipationAt u (σ n)
                  /
                velocityH3EnergyAt u (σ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                (
                  - velocityH3TransportDerivativeAt u (σ n)
                )
                  /
                velocityH3EnergyAt u (σ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TopCharacteristicFrequencyAt
                  u
                  (σ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                max
                  (
                    abs
                      (
                        realVorticityX
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (σ n)
                          (y n)
                      )
                  )
                  (
                    max
                      (
                        abs
                          (
                            realVorticityY
                              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                              (σ n)
                              (y n)
                          )
                      )
                      (
                        abs
                          (
                            realVorticityZ
                              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                              (σ n)
                              (y n)
                          )
                      )
                  )
            )
            atTop
            atTop
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_terminal_positiveGrowth_fullCascade_actualVorticity_tendsto_atTop_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

end

end Euclidean
end Bridge
end PrimeTensor
