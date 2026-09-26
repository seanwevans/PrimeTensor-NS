import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualVelocityComponentEscape

/-!
# Fixed-component tail unboundedness and a boundedness continuation criterion

The previous increment proves that hypothetical nonextension produces one fixed
physical velocity component `j` and one strict terminal sequence `τ n -> T`
such that the weighted scalar spectral H³ norm of that component tends to
`+∞`.

This file records the two useful consequences.

First, the *same fixed component* is unbounded on every terminal tail.  Indeed,
for every `b < T` and every finite level `M`, convergence of `τ` to `T` and of
the component norm to `+∞` gives one common index `n` with

    b < τ n

and

    M < ‖G_j(τ n)‖.

Second, strong endpoint convergence is much more than is required for the
terminal contradiction.  It is enough that each of the three physical
component spectral H³ norms be eventually bounded near `T`, with component-
dependent bounds and component-dependent starting times.  The fixed-component
escape theorem then contradicts the bound for the escaping component.

Thus the endpoint target can be weakened from

    strong H³ convergence

to

    eventual H³ boundedness of the three physical velocity components.

No claim is made here that this boundedness follows automatically from the
Navier--Stokes hypotheses; that is the remaining analytic issue.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## One component is unbounded on every terminal tail -/

/--
Under hypothetical nonextension, there is one fixed physical velocity
component and one fixed terminal sequence along which the component spectral
H³ norm is arbitrarily large arbitrarily late.

The same sequence works simultaneously for every terminal cutoff and every
finite norm threshold.
-/
theorem exists_terminal_velocityComponentSpectralNorm_unboundedOnEveryTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
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
          (
            ∀ b : ℝ,
              b < T →
              ∀ M : ℝ,
                ∃ n : ℕ,
                  b < τ n
                    ∧
                  M
                    <
                  norm
                    (
                      h3TerminalVelocityComponentSpectralStateAt
                        hH3
                        j
                        (τ n)
                        (hTauStrict n)
                    )
          ) := by

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

  have hEveryTail :
      ∀ b : ℝ,
        b < T →
        ∀ M : ℝ,
          ∃ n : ℕ,
            b < τ n
              ∧
            M
              <
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3
                  j
                  (τ n)
                  (hTauStrict n)
              ) := by

    intro b hb M

    have hTimeEventually :
        ∀ᶠ n : ℕ in atTop,
          b < τ n :=
      (tendsto_order.1 hTau).1
        b hb

    have hNormEventually :
        ∀ᶠ n : ℕ in atTop,
          M
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
        (eventually_gt_atTop M)

    obtain
      ⟨
        n,
        hnTime,
        hnNorm
      ⟩ :=
      (hTimeEventually.and hNormEventually).exists

    exact
      ⟨
        n,
        hnTime,
        hnNorm
      ⟩

  exact
    ⟨
      j,
      τ,
      hTauStrict,
      hTauClass,
      hTau,
      hNorm,
      hEveryTail
    ⟩

/-! ## Weak endpoint target: eventual componentwise H³ boundedness -/

/--
One physical velocity component has an eventually bounded weighted spectral
H³ norm near the terminal time.

The bound and the start of the terminal tail may depend on the component.
-/
def H3TerminalVelocityComponentEventuallyBounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3) : Prop :=
  ∃ b B : ℝ,
    b < T
      ∧
    ∀
      (t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) T),
      b < t →
        norm
          (
            h3TerminalVelocityComponentSpectralStateAt
              hH3 j t ht
          )
          ≤ B

/--
All three physical velocity components are eventually bounded in weighted
spectral H³ near `T`.
-/
def H3TerminalVelocityEventuallyBounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T) : Prop :=
  ∀ j : Fin 3,
    H3TerminalVelocityComponentEventuallyBounded
      hH3 j

/-! ## Eventual boundedness already forces continuation -/

/--
Eventual weighted H³ boundedness of the three physical velocity components is
sufficient for smooth continuation.

This is strictly weaker than the previously used componentwise strong H³
terminal convergence condition: no terminal state and no Cauchy/convergence
property is assumed.
-/
theorem smoothContinuationExtension_of_velocityEventuallyBounded
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

  by_contra hNoExtension

  obtain
    ⟨
      j,
      τ,
      hTauStrict,
      _hTauClass,
      _hTau,
      _hNorm,
      hEveryTail
    ⟩ :=
    exists_terminal_velocityComponentSpectralNorm_unboundedOnEveryTail_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  obtain
    ⟨
      b,
      B,
      hbT,
      hBound
    ⟩ :=
    hBounded j

  obtain
    ⟨
      n,
      hnTime,
      hnLarge
    ⟩ :=
    hEveryTail
      b
      hbT
      B

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

/-! ## Strong endpoint convergence implies the weaker boundedness target -/

/--
The componentwise strong H³ endpoint path property implies eventual boundedness
of that component.  This records explicitly that the previous endpoint theorem
was stronger than necessary.
-/
theorem velocityComponentEventuallyBounded_of_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {j : Fin 3}
    (hStrong :
      H3TerminalVelocityComponentStrongH3EndpointPath
        hH3 j) :
    H3TerminalVelocityComponentEventuallyBounded
      hH3 j := by

  obtain
    ⟨
      Ginf,
      _hTerminalRep,
      hModulus
    ⟩ :=
    hStrong

  obtain
    ⟨
      η,
      hη,
      hClose
    ⟩ :=
    hModulus
      1
      zero_lt_one

  let b : ℝ :=
    T - η / 2

  refine
    ⟨
      b,
      1 + ‖Ginf‖,
      ?_,
      ?_
    ⟩

  · dsimp only [b]
    linarith

  · intro t ht hbt

    have hDistance :
        dist t T < η := by

      rw [Real.dist_eq]

      have htT :
          t < T :=
        ht.2

      have hLower :
          T - η / 2 < t := by
        simpa only [b] using hbt

      have hAbs :
          |t - T| = T - t := by
        rw [
          abs_of_nonpos
            (sub_nonpos.mpr
              (le_of_lt htT))
        ]
        ring

      rw [hAbs]

      linarith

    let U : H3SpectralScalarState :=
      h3TerminalVelocityComponentSpectralStateAt
        hH3 j t ht

    have hStateClose :
        norm (U - Ginf) < 1 := by

      dsimp only [U]

      exact
        hClose
          t
          ht
          hDistance

    change
      norm U ≤ 1 + norm Ginf

    calc
      norm U
          =
        norm ((U - Ginf) + Ginf) := by
          rw [sub_add_cancel]

      _ ≤
        norm (U - Ginf) + norm Ginf :=
        norm_add_le _ _

      _ ≤
        1 + norm Ginf := by
        linarith

/--
The three-component strong endpoint criterion factors through eventual
componentwise boundedness.
-/
theorem velocityEventuallyBounded_of_velocityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hStrong :
      H3TerminalVelocityStrongH3EndpointPath
        hH3) :
    H3TerminalVelocityEventuallyBounded
      hH3 := by

  intro j

  exact
    velocityComponentEventuallyBounded_of_strongH3EndpointPath
      hH3
      (hStrong j)

end

end Euclidean
end Bridge
end PrimeTensor
