import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealCoherentIntegralTube244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGradientFourierBridge244
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Actual seven-derivative gradient Fourier multiplier of the real Schwartz packet

The last checkpoint localized arbitrary cubic Fourier amplitudes of the actual
real divergence-free Schwartz velocity. We now identify a genuine 3+3+1
physical-gradient Fourier slot with its seven-frequency multiplier and the
three recovered Fourier amplitudes, on the real Hilbert-frequency carrier.

Every such integrand vanishes outside the coherent twelve-center tube, and
its actual absolutely convergent global integral equals the tube-localized
integral. Unlike a generic weighted-trilinear theorem, the multiplier below
is exactly the one from `thirdGradientSchwartzKernel244` (three derivatives,
three derivatives, one derivative) and retains its physical component slots.

This file does not assert signed noncancellation after summing the four
physical gradient patterns, the five axis sums, and the 3+2+2 interpolation
channel. The local -192 polynomial coefficient by itself cannot establish
that global sign.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap FourierTransform Topology

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev Pair244 := Freq244 × Freq244
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeRealGradient244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact conversion of Fourier amplitudes between the Euclidean Hilbert
carrier and the coordinate spectrum of the REAL physical velocity. -/
theorem thirdFullAxisRealSchwartzSpectrum_at_hilbert244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j : A3) (ξ : V3) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C (WithLp.ofLp ξ) j =
      𝓕 (h3SchwartzComplexify
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j)) ξ := by
  change 𝓕 (h3SchwartzComplexify
    (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j))
      (WithLp.toLp 2 (WithLp.ofLp ξ)) = _
  rw [WithLp.toLp_ofLp]

/-- The dependent second frequency commutes with the exact PiLp carrier
transport, including the leading minus sign of conservation. -/
theorem thirdFullMiddleFrequency_ofLp_pair244 (z : V3 × V3) :
    thirdFullMiddleFrequency244 (WithLp.ofLp z.1, WithLp.ofLp z.2) =
      WithLp.ofLp (-(z.1 + z.2)) := by
  funext j
  simp only [thirdFullMiddleFrequency244, WithLp.ofLp_neg,
    WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]

/-- Exactly seven directional-frequency factors, with the existing
Fourier normalization intentionally left outside the algebraic weight. -/
noncomputable def thirdFullGradientSevenWeight244
    (a b c d e k v : V3) (z : V3 × V3) : ℂ :=
  let p := z.1
  let q := -(z.1 + z.2)
  let r := z.2
  (((inner ℝ p a : ℂ) * (inner ℝ p b : ℂ) * (inner ℝ p c : ℂ)) *
    ((inner ℝ q d : ℂ) * (inner ℝ q e : ℂ) * (inner ℝ q k : ℂ))) *
    (inner ℝ r v : ℂ)

/-- One literal 3+3+1 gradient slot of the already constructed real
Schwartz velocity, rather than an auxiliary or model Fourier kernel. -/
noncomputable def thirdFullAxisRealGradientSlot244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j m n : A3) (a b c d e k v : V3) (z : V3 × V3) : ℂ :=
  let f := thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C
  thirdGradientSchwartzKernel244
    (h3SchwartzComplexify (f j))
    (h3SchwartzComplexify (f m))
    (h3SchwartzComplexify (f n)) a b c d e k v z

/-- The ACTUAL Schwartz Fourier gradient slot equals its polynomial seven-
derivative multiplier times precisely three REAL-velocity Fourier amplitudes.
No replacement of the physical gradient kernel by the finite symbol is used. -/
theorem thirdFullAxisRealGradientSlot_factor244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j m n : A3) (a b c d e k v : V3) (z : V3 × V3) :
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j m n a b c d e k v z =
      thirdFullGradientSevenWeight244 a b c d e k v z *
        ((thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
            (WithLp.ofLp z.1) j *
          thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
            (thirdFullMiddleFrequency244
              (WithLp.ofLp z.1, WithLp.ofLp z.2)) m) *
          thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
            (WithLp.ofLp z.2) n) := by
  have hp := (thirdFullAxisRealSchwartzSpectrum_at_hilbert244
    ρ hρ A B C j z.1).symm
  have hq := (thirdFullAxisRealSchwartzSpectrum_at_hilbert244
    ρ hρ A B C m (-(z.1 + z.2))).symm
  have hr := (thirdFullAxisRealSchwartzSpectrum_at_hilbert244
    ρ hρ A B C n z.2).symm
  -- `unfold` alone leaves the `let f`, `let p`, `let q`, `let r`
  -- bindings of the Fourier kernel in the target. Simplification performs
  -- zeta reduction so that the three exact spectral identities can rewrite.
  rw [thirdFullMiddleFrequency_ofLp_pair244]
  simp only [thirdFullAxisRealGradientSlot244,
    thirdGradientSchwartzKernel244, thirdFullGradientSevenWeight244]
  rw [hp, hq, hr]
  ring

/-- Every literal gradient-slot kernel is absolutely integrable, since all
three factors are Schwartz and all seven derivatives are Schwartz stable. -/
theorem thirdFullAxisRealGradientSlot_integrable244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j m n : A3) (a b c d e k v : V3) :
    Integrable
      (thirdFullAxisRealGradientSlot244 ρ hρ A B C j m n a b c d e k v)
      (volume.prod volume) := by
  exact thirdGradientSchwartzKernel_integrable244 _ _ _ a b c d e k v

/-- Pointwise SUPPORT EXCLUSION for the genuine seven-derivative gradient
Fourier integrand: every product of three amplitudes is zero outside the
same twelve-center coherent tube already proved for the real velocity. -/
theorem thirdFullAxisRealGradientSlot_zero_off_coherent_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ)
    (A B C : Freq244) (j m n : A3)
    (a b c d e k v : V3) (z : V3 × V3)
    (hz : (WithLp.ofLp z.1, WithLp.ofLp z.2) ∉
      Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244) :
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j m n a b c d e k v z = 0 := by
  let zAxis : Pair244 := (WithLp.ofLp z.1, WithLp.ofLp z.2)
  have hAway : zAxis ∉
      Metric.thickening ρ thirdFullAxisCoherentPairCenterSet244 := by
    intro hNear
    exact hz ((Metric.thickening_subset_cthickening_of_le hρδ
      thirdFullAxisCoherentPairCenterSet244) hNear)
  have hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C zAxis = 0 :=
    thirdFullAxisRealSchwartzTripleMass_zero_off_tube244
      ρ hρ hSmall A B C zAxis hAway
  have hTriple := thirdFullAxisRealSchwartzTripleComponent_zero_of_mass244
    ρ hρ A B C zAxis hMass j m n
  rw [thirdFullAxisRealGradientSlot_factor244]
  change thirdFullGradientSevenWeight244 a b c d e k v z *
    ((thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C zAxis.1 j *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
        (thirdFullMiddleFrequency244 zAxis) m) *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C zAxis.2 n) = 0
  rw [hTriple]
  ring

/-- The exact global integral of one PHYSICAL 3+3+1 Fourier slot equals
its coherent-tube indicator integral, with no claimed sign or Jacobian. -/
theorem thirdFullAxisRealGradientSlot_integral_eq_coherent_tube244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ)
    (A B C : Freq244) (j m n : A3)
    (a b c d e k v : V3) :
    (∫ z : V3 × V3,
      thirdFullAxisRealGradientSlot244 ρ hρ A B C j m n a b c d e k v z
      ∂(volume.prod volume)) =
    ∫ z : V3 × V3,
      {z | (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈
        Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244}.indicator
        (thirdFullAxisRealGradientSlot244 ρ hρ A B C j m n a b c d e k v) z
      ∂(volume.prod volume) := by
  classical
  apply integral_congr_ae
  filter_upwards with z
  -- The set in the indicator is a preimage under the PiLp coordinate map.
  -- Expose its literal if/then/else rather than simplifying the definition
  -- of `Metric.cthickening` (which expands into `infEDist`).
  change thirdFullAxisRealGradientSlot244 ρ hρ A B C
      j m n a b c d e k v z =
    if (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈
        Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244 then
      thirdFullAxisRealGradientSlot244 ρ hρ A B C
        j m n a b c d e k v z
    else 0
  split_ifs with hz
  · rfl
  · exact thirdFullAxisRealGradientSlot_zero_off_coherent_tube244
      ρ hρ hSmall δ hρδ A B C j m n a b c d e k v z hz

/-- The same width can be selected *before* choosing any real velocity
polarizations, component slots or seven derivative directions. -/
theorem thirdFullAxisRealGradientSlot_exists_integral_tube244
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ) ∧
      ∀ (A B C : Freq244) (j m n : A3) (a b c d e k v : V3),
        (∫ z : V3 × V3,
          thirdFullAxisRealGradientSlot244 ρ hρ A B C j m n a b c d e k v z
          ∂(volume.prod volume)) =
        ∫ z : V3 × V3,
          {z | (WithLp.ofLp z.1, WithLp.ofLp z.2) ∈
            Metric.cthickening δ thirdFullAxisCoherentPairCenterSet244}.indicator
            (thirdFullAxisRealGradientSlot244 ρ hρ A B C j m n a b c d e k v) z
          ∂(volume.prod volume) := by
  let σ := lowNormalSixCenterSeparationRadius (1 : ℝ)
  have hσ : 0 < σ :=
    lowNormalSixCenterSeparationRadius_pos (1 : ℝ) (by norm_num)
  let ρ := min δ σ / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hσ)
  have hSmall : ρ ≤ σ := by
    dsimp [ρ]
    linarith [min_le_right δ σ]
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    linarith [min_le_left δ σ]
  refine ⟨ρ, hρ, hSmall, ?_⟩
  intro A B C j m n a b c d e k v
  exact thirdFullAxisRealGradientSlot_integral_eq_coherent_tube244
    ρ hρ hSmall δ hρδ A B C j m n a b c d e k v

end
end PrimeTensor.FirstMonomialTriad
