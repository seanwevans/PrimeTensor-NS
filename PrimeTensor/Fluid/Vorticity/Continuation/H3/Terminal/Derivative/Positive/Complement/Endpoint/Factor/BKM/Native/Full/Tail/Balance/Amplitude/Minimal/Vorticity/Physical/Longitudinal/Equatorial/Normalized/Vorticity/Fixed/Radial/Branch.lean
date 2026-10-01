import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Normalized.Vorticity.Radial.Split

/-!
# Freeze the radial branch of the normalized-vorticity obstruction

For every fixed positive radial cutoff `ρ`, the previous checkpoint gives at
each shrinking-cone index a dichotomy:

* normalized-vorticity mass `> ε²/64` below `ρ`, or
* normalized-vorticity mass `> ε²/64` on the complementary radial region.

This file freezes that moving dichotomy.  Either the infrared alternative
occurs arbitrarily far out, in which case a strictly increasing subsequence is
extracted, or it eventually stops, in which case the complementary radial
alternative holds on the whole remaining tail.

Thus, for every fixed `ρ > 0`, hypothetical nonextension forces one fixed
complementary normalized-vorticity component into one fixed radial regime
along an explicit terminal subsequence.

No branch is preferred or excluded here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedVorticityFixedRadialBranch
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Generic two-branch subsequence extraction -/

private theorem exists_strictMono_subsequence_all_left_or_all_right
    (P Q : ℕ → Prop)
    (hPQ :
      ∀ n : ℕ,
        P n ∨ Q n) :
    (
      ∃ r : ℕ → ℕ,
        StrictMono r
          ∧
        ∀ n : ℕ,
          P (r n)
    )
      ∨
    (
      ∃ r : ℕ → ℕ,
        StrictMono r
          ∧
        ∀ n : ℕ,
          Q (r n)
    ) := by

  classical

  by_cases hP :
      ∀ N : ℕ,
        ∃ n > N,
          P n

  · left

    exact
      Nat.exists_strictMono_subsequence
        hP

  · push Not at hP

    obtain
      ⟨
        N,
        hN
      ⟩ :=
      hP

    right

    let r : ℕ → ℕ :=
      fun n =>
        N + n + 1

    have hRMono :
        StrictMono r := by

      intro a b hab

      dsimp only [r]

      omega

    refine
      ⟨
        r,
        hRMono,
        ?_
      ⟩

    intro n

    have hNR :
        N < r n := by

      dsimp only [r]

      omega

    have hNotP :
        ¬ P (r n) :=
      hN
        (r n)
        hNR

    exact
      (hPQ (r n)).resolve_left
        hNotP

/-! ## Freeze the physical radial alternative -/

/--
For every fixed `ρ > 0`, under hypothetical nonextension with one surviving
actual-vorticity strong-H³ endpoint, one fixed complementary normalized
vorticity component admits a terminal shrinking-cone subsequence on which
exactly one of the two radial regimes is fixed:

* every selected index has infrared mass `> ε²/64`, or
* every selected index has complementary radial mass `> ε²/64`.
-/
theorem exists_fixed_complementary_normalizedVorticityComponent_shrinkingEquatorialCone_fixedRadialBranch_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    {ε ρ : ℝ}
    (hε : 0 < ε)
    (hρ : 0 < ρ) :
    ∃ s t : ℕ → ℝ,
      ∃ hs :
        ∀ n : ℕ,
          s n ∈ Set.Ioo (0 : ℝ) T,
        ∃ ht :
          ∀ n : ℕ,
            t n ∈ Set.Ioo (0 : ℝ) T,
          ∃ q : Fin 3,
            q ≠ i
              ∧
            ∃ p : ℕ → ℕ,
              StrictMono p
                ∧
              Tendsto
                (fun n : ℕ => s (p n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (fun n : ℕ => t (p n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    (1 : ℝ) / (((p n : ℕ) : ℝ) + 2)
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
                        i q
                        ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
                        ρ
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (s (p n))
                          (hs (p n)))
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (t (p n))
                          (ht (p n)))
                )
                  ∨
                (
                  ∀ n : ℕ,
                    ε ^ 2 / 64
                        <
                      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
                        i q
                        ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
                        ρ
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (s (p n))
                          (hs (p n)))
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (t (p n))
                          (ht (p n)))
                )
              ) := by

  obtain
    ⟨
      s,
      t,
      hs,
      ht,
      q,
      hqNe,
      m,
      hMMono,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      hSplit
    ⟩ :=
    exists_fixed_complementary_normalizedVorticityComponent_shrinkingEquatorialCone_radialSplit_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε
      hρ

  let P : ℕ → Prop :=
    fun n =>
      ε ^ 2 / 64
        <
      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
        i q
        ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
        ρ
        (h3TerminalVelocitySpectralStateAt
          hH3
          (s (m n))
          (hs (m n)))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (t (m n))
          (ht (m n)))

  let Q : ℕ → Prop :=
    fun n =>
      ε ^ 2 / 64
        <
      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
        i q
        ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
        ρ
        (h3TerminalVelocitySpectralStateAt
          hH3
          (s (m n))
          (hs (m n)))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (t (m n))
          (ht (m n)))

  have hPQ :
      ∀ n : ℕ,
        P n ∨ Q n := by

    intro n

    simpa only [P, Q] using
      hSplit n

  have hFrozen :=
    exists_strictMono_subsequence_all_left_or_all_right
      P Q hPQ

  rcases hFrozen with hLow | hHigh

  · obtain
      ⟨
        r,
        hRMono,
        hRLow
      ⟩ :=
      hLow

    let p : ℕ → ℕ :=
      fun n =>
        m (r n)

    have hPMono :
        StrictMono p := by

      simpa only [p, Function.comp_def] using
        hMMono.comp hRMono

    have hRTop :
        Tendsto r atTop atTop :=
      hRMono.tendsto_atTop

    have hSTendstoP :
        Tendsto
          (fun n : ℕ => s (p n))
          atTop
          (𝓝 T) := by

      simpa only [p, Function.comp_def] using
        hSTendsto.comp hRTop

    have hTTendstoP :
        Tendsto
          (fun n : ℕ => t (p n))
          atTop
          (𝓝 T) := by

      simpa only [p, Function.comp_def] using
        hTTendsto.comp hRTop

    have hApertureTendstoP :
        Tendsto
          (
            fun n : ℕ =>
              (1 : ℝ) / (((p n : ℕ) : ℝ) + 2)
          )
          atTop
          (𝓝 0) := by

      simpa only [p, Function.comp_def] using
        hApertureTendsto.comp hRTop

    have hLowP :
        ∀ n : ℕ,
          ε ^ 2 / 64
              <
            h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
              i q
              ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
              ρ
              (h3TerminalVelocitySpectralStateAt
                hH3
                (s (p n))
                (hs (p n)))
              (h3TerminalVelocitySpectralStateAt
                hH3
                (t (p n))
                (ht (p n))) := by

      intro n

      simpa only [P, p] using
        hRLow n

    exact
      ⟨
        s,
        t,
        hs,
        ht,
        q,
        hqNe,
        p,
        hPMono,
        hSTendstoP,
        hTTendstoP,
        hApertureTendstoP,
        Or.inl hLowP
      ⟩

  · obtain
      ⟨
        r,
        hRMono,
        hRHigh
      ⟩ :=
      hHigh

    let p : ℕ → ℕ :=
      fun n =>
        m (r n)

    have hPMono :
        StrictMono p := by

      simpa only [p, Function.comp_def] using
        hMMono.comp hRMono

    have hRTop :
        Tendsto r atTop atTop :=
      hRMono.tendsto_atTop

    have hSTendstoP :
        Tendsto
          (fun n : ℕ => s (p n))
          atTop
          (𝓝 T) := by

      simpa only [p, Function.comp_def] using
        hSTendsto.comp hRTop

    have hTTendstoP :
        Tendsto
          (fun n : ℕ => t (p n))
          atTop
          (𝓝 T) := by

      simpa only [p, Function.comp_def] using
        hTTendsto.comp hRTop

    have hApertureTendstoP :
        Tendsto
          (
            fun n : ℕ =>
              (1 : ℝ) / (((p n : ℕ) : ℝ) + 2)
          )
          atTop
          (𝓝 0) := by

      simpa only [p, Function.comp_def] using
        hApertureTendsto.comp hRTop

    have hHighP :
        ∀ n : ℕ,
          ε ^ 2 / 64
              <
            h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
              i q
              ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
              ρ
              (h3TerminalVelocitySpectralStateAt
                hH3
                (s (p n))
                (hs (p n)))
              (h3TerminalVelocitySpectralStateAt
                hH3
                (t (p n))
                (ht (p n))) := by

      intro n

      simpa only [Q, p] using
        hRHigh n

    exact
      ⟨
        s,
        t,
        hs,
        ht,
        q,
        hqNe,
        p,
        hPMono,
        hSTendstoP,
        hTTendstoP,
        hApertureTendstoP,
        Or.inr hHighP
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
