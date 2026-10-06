import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Normalized.Vorticity.Radial.Split

/-!
# Freeze one radial regime on the synchronized final witness

The synchronized resolved-PDE witness now carries one fixed complementary
normalized-vorticity component with positive mass in a shrinking equatorial
cone.

For any fixed positive radial cutoff `ρ`, split that mass into

* the infrared region `|ξ| < ρ`, and
* its radial complement.

At every selected index one of these two pieces carries more than `ε²/64`.
A binary subsequence extraction freezes the radial alternative while retaining
the same original terminal witness `τ` and the same cofinal pair `p,q`.

No branch is preferred or excluded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

private theorem exists_strictMono_subsequence_all_left_or_all_right_finalWitness
    (P Q : ℕ → Prop)
    (hPQ : ∀ n : ℕ, P n ∨ Q n) :
    (
      ∃ s : ℕ → ℕ,
        StrictMono s
          ∧
        ∀ n : ℕ, P (s n)
    )
      ∨
    (
      ∃ s : ℕ → ℕ,
        StrictMono s
          ∧
        ∀ n : ℕ, Q (s n)
    ) := by

  classical

  by_cases hP :
      ∀ N : ℕ,
        ∃ n > N,
          P n

  · exact
      Or.inl
        (Nat.exists_strictMono_subsequence hP)

  · push Not at hP

    obtain ⟨N, hN⟩ :=
      hP

    let s : ℕ → ℕ :=
      fun n => N + n + 1

    have hSMono :
        StrictMono s := by

      intro a b hab

      dsimp only [s]

      omega

    refine
      Or.inr
        ⟨
          s,
          hSMono,
          ?_
        ⟩

    intro n

    have hNS :
        N < s n := by

      dsimp only [s]

      omega

    exact
      (hPQ (s n)).resolve_left
        (hN (s n) hNS)

/--
For every fixed positive radial cutoff, the synchronized final witness admits
a strictly increasing subsequence on which its fixed complementary normalized
vorticity component stays in one fixed radial regime.

The original `τ`, `p`, and `q` are unchanged.  The returned `k` indexes those
same synchronized states.
-/
theorem exists_fixed_terminalSequence_with_fixed_complementary_normalizedVorticity_fixedRadialBranch_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε ρ : ℝ}
    (hε : 0 < ε)
    (_hρ : 0 < ρ) :
    ∃ j₀ : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hτ :
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T,
          ∃ p q : ℕ → ℕ,
            (∀ n : ℕ, n ≤ p n)
              ∧
            (∀ n : ℕ, p n ≤ q n)
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ =>
                velocityH3EnergyAt u (τ n))
              atTop atTop
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
                        ⟨
                          lt_trans hClass.terminal_start.1 (hτ n).1.1,
                          (hτ n).1.2
                        ⟩
                    )
              )
              atTop
              atTop
              ∧
            ∃ r : Fin 3,
              r ≠ i
                ∧
              ∃ k : ℕ → ℕ,
                StrictMono k
                  ∧
                Tendsto
                  (fun n : ℕ => τ (p (k n)))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (fun n : ℕ => τ (q (k n)))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
                  )
                  atTop
                  (𝓝 0)
                  ∧
                (
                  (
                    ∀ n : ℕ,
                      ε ^ 2 / 64
                        <
                      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
                        i r
                        ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                        ρ
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (τ (q (k n)))
                          ⟨
                            lt_trans hClass.terminal_start.1
                              (hτ (q (k n))).1.1,
                            (hτ (q (k n))).1.2
                          ⟩)
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (τ (p (k n)))
                          ⟨
                            lt_trans hClass.terminal_start.1
                              (hτ (p (k n))).1.1,
                            (hτ (p (k n))).1.2
                          ⟩)
                  )
                    ∨
                  (
                    ∀ n : ℕ,
                      ε ^ 2 / 64
                        <
                      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
                        i r
                        ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                        ρ
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (τ (q (k n)))
                          ⟨
                            lt_trans hClass.terminal_start.1
                              (hτ (q (k n))).1.1,
                            (hτ (q (k n))).1.2
                          ⟩)
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (τ (p (k n)))
                          ⟨
                            lt_trans hClass.terminal_start.1
                              (hτ (p (k n))).1.1,
                            (hτ (p (k n))).1.2
                          ⟩)
                  )
                ) := by

  classical

  obtain
    ⟨
      j₀,
      τ,
      hτ,
      p,
      q,
      hnp,
      hpq,
      hTau,
      hEnergyTop,
      hLongTop,
      m,
      hMMono,
      hTauP,
      hTauQ,
      hAperture,
      r,
      hrNe,
      hMass
    ⟩ :=
    exists_fixed_terminalSequence_with_fixed_complementary_normalizedVorticityEquatorialConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  let P : ℕ → Prop :=
    fun n =>
      ε ^ 2 / 64
        <
      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
        i r
        ((1 : ℝ) / (((m n : ℕ) : ℝ) + 1))
        ρ
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (m n)))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ (q (m n))).1.1,
            (hτ (q (m n))).1.2
          ⟩)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (m n)))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ (p (m n))).1.1,
            (hτ (p (m n))).1.2
          ⟩)

  let Q : ℕ → Prop :=
    fun n =>
      ε ^ 2 / 64
        <
      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
        i r
        ((1 : ℝ) / (((m n : ℕ) : ℝ) + 1))
        ρ
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (m n)))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ (q (m n))).1.1,
            (hτ (q (m n))).1.2
          ⟩)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (m n)))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ (p (m n))).1.1,
            (hτ (p (m n))).1.2
          ⟩)

  have hPQ :
      ∀ n : ℕ,
        P n ∨ Q n := by

    intro n

    have hOne :=
      normalizedVorticityComponentBadCone_lowRadial_or_highRadial_gt_half
        i
        r
        ((1 : ℝ) / (((m n : ℕ) : ℝ) + 1))
        ρ
        (ε ^ 2 / 32)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (m n)))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ (q (m n))).1.1,
            (hτ (q (m n))).1.2
          ⟩)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (m n)))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ (p (m n))).1.1,
            (hτ (p (m n))).1.2
          ⟩)
        (hMass n)

    simpa only [P, Q] using
      (by
        convert hOne using 1 <;> ring_nf)

  have hFrozen :=
    exists_strictMono_subsequence_all_left_or_all_right_finalWitness
      P Q hPQ

  rcases hFrozen with hLow | hHigh

  · obtain
      ⟨
        s,
        hSMono,
        hSLow
      ⟩ :=
      hLow

    let k : ℕ → ℕ :=
      fun n =>
        m (s n)

    have hKMono :
        StrictMono k := by

      simpa only [k, Function.comp_def] using
        hMMono.comp hSMono

    have hSTop :
        Tendsto s atTop atTop :=
      hSMono.tendsto_atTop

    have hTauPK :
        Tendsto
          (fun n : ℕ => τ (p (k n)))
          atTop
          (𝓝 T) := by

      simpa only [k, Function.comp_def] using
        hTauP.comp hSTop

    have hTauQK :
        Tendsto
          (fun n : ℕ => τ (q (k n)))
          atTop
          (𝓝 T) := by

      simpa only [k, Function.comp_def] using
        hTauQ.comp hSTop

    have hApertureK :
        Tendsto
          (
            fun n : ℕ =>
              (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
          )
          atTop
          (𝓝 0) := by

      simpa only [k, Function.comp_def] using
        hAperture.comp hSTop

    have hLowK :
        ∀ n : ℕ,
          ε ^ 2 / 64
            <
          h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
            i r
            ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
            ρ
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (q (k n)))
              ⟨
                lt_trans hClass.terminal_start.1
                  (hτ (q (k n))).1.1,
                (hτ (q (k n))).1.2
              ⟩)
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (p (k n)))
              ⟨
                lt_trans hClass.terminal_start.1
                  (hτ (p (k n))).1.1,
                (hτ (p (k n))).1.2
              ⟩) := by

      intro n

      simpa only [P, k] using
        hSLow n

    exact
      ⟨
        j₀,
        τ,
        hτ,
        p,
        q,
        hnp,
        hpq,
        hTau,
        hEnergyTop,
        hLongTop,
        r,
        hrNe,
        k,
        hKMono,
        hTauPK,
        hTauQK,
        hApertureK,
        Or.inl hLowK
      ⟩

  · obtain
      ⟨
        s,
        hSMono,
        hSHigh
      ⟩ :=
      hHigh

    let k : ℕ → ℕ :=
      fun n =>
        m (s n)

    have hKMono :
        StrictMono k := by

      simpa only [k, Function.comp_def] using
        hMMono.comp hSMono

    have hSTop :
        Tendsto s atTop atTop :=
      hSMono.tendsto_atTop

    have hTauPK :
        Tendsto
          (fun n : ℕ => τ (p (k n)))
          atTop
          (𝓝 T) := by

      simpa only [k, Function.comp_def] using
        hTauP.comp hSTop

    have hTauQK :
        Tendsto
          (fun n : ℕ => τ (q (k n)))
          atTop
          (𝓝 T) := by

      simpa only [k, Function.comp_def] using
        hTauQ.comp hSTop

    have hApertureK :
        Tendsto
          (
            fun n : ℕ =>
              (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
          )
          atTop
          (𝓝 0) := by

      simpa only [k, Function.comp_def] using
        hAperture.comp hSTop

    have hHighK :
        ∀ n : ℕ,
          ε ^ 2 / 64
            <
          h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
            i r
            ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
            ρ
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (q (k n)))
              ⟨
                lt_trans hClass.terminal_start.1
                  (hτ (q (k n))).1.1,
                (hτ (q (k n))).1.2
              ⟩)
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (p (k n)))
              ⟨
                lt_trans hClass.terminal_start.1
                  (hτ (p (k n))).1.1,
                (hτ (p (k n))).1.2
              ⟩) := by

      intro n

      simpa only [Q, k] using
        hSHigh n

    exact
      ⟨
        j₀,
        τ,
        hτ,
        p,
        q,
        hnp,
        hpq,
        hTau,
        hEnergyTop,
        hLongTop,
        r,
        hrNe,
        k,
        hKMono,
        hTauPK,
        hTauQK,
        hApertureK,
        Or.inr hHighK
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
