import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Normalized.Curl.Channel

/-!
# Fixed normalized curl channel on an explicit shrinking-cone subsequence

The preceding checkpoint froze one normalized longitudinal curl channel on a
cofinal set of indices of the shrinking equatorial concentration sequence.

This file converts that cofinal recurrence into an explicit strictly increasing
subsequence.  Along that subsequence,

* the two selected strict times still converge to `T`;
* the angular aperture still converges to zero;
* the same fixed normalized curl channel carries more than `ε² / 32` square
  mass on every selected bad cone.

This remains a conditional necessary mechanism under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedCurlChannelSubsequence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Under hypothetical nonextension and one surviving physical-vorticity
strong-H³ endpoint, there are strict terminal sequences, one fixed normalized
curl channel, and a strictly increasing index subsequence along which the
channel bad-cone square mass stays above `ε²/32` while the aperture tends to
zero.
-/
theorem exists_fixed_normalizedLongitudinalCurlChannel_shrinkingEquatorialCone_subsequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ∃ s t : ℕ → ℝ,
      ∃ hs :
        ∀ n : ℕ,
          s n ∈ Set.Ioo (0 : ℝ) T,
        ∃ ht :
          ∀ n : ℕ,
            t n ∈ Set.Ioo (0 : ℝ) T,
          ∃ k : Fin 2,
            ∃ m : ℕ → ℕ,
              StrictMono m
                ∧
              Tendsto
                (fun n : ℕ => s (m n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (fun n : ℕ => t (m n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    (1 : ℝ) / (((m n : ℕ) : ℝ) + 2)
                )
                atTop
                (𝓝 0)
                ∧
              (
                ∀ n : ℕ,
                  ε ^ 2 / 32
                    <
                  h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
                    i k
                    ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (s (m n))
                      (hs (m n)))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (t (m n))
                      (ht (m n)))
              ) := by

  obtain
    ⟨
      s,
      t,
      hs,
      ht,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      k,
      hCofinal
    ⟩ :=
    exists_cofinally_recurrent_normalizedLongitudinalCurlChannel_on_shrinkingEquatorialCone_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  have hStrictlyCofinal :
      ∀ N : ℕ,
        ∃ n > N,
          ε ^ 2 / 32
            <
          h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
            i k
            ((1 : ℝ) / ((n : ℝ) + 2))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (s n)
              (hs n))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (t n)
              (ht n)) := by

    intro N

    obtain
      ⟨
        n,
        hn,
        hMass
      ⟩ :=
      hCofinal
        (N + 1)

    refine
      ⟨
        n,
        ?_,
        hMass
      ⟩

    exact
      lt_of_lt_of_le
        (Nat.lt_succ_self N)
        hn

  obtain
    ⟨
      m,
      hMMono,
      hMassSub
    ⟩ :=
    Nat.exists_strictMono_subsequence
      hStrictlyCofinal

  have hMTop :
      Tendsto m atTop atTop :=
    hMMono.tendsto_atTop

  have hSTendstoSub :
      Tendsto
        (fun n : ℕ => s (m n))
        atTop
        (𝓝 T) := by

    exact
      hSTendsto.comp
        hMTop

  have hTTendstoSub :
      Tendsto
        (fun n : ℕ => t (m n))
        atTop
        (𝓝 T) := by

    exact
      hTTendsto.comp
        hMTop

  have hApertureTendstoSub :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((m n : ℕ) : ℝ) + 2)
        )
        atTop
        (𝓝 0) := by

    exact
      hApertureTendsto.comp
        hMTop

  exact
    ⟨
      s,
      t,
      hs,
      ht,
      k,
      m,
      hMMono,
      hSTendstoSub,
      hTTendstoSub,
      hApertureTendstoSub,
      hMassSub
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
