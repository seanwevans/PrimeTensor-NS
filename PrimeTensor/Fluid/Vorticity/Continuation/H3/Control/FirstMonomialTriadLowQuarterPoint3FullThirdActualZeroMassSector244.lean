import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPositiveSectorHermitianBridge244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Full-third Schwartz Fourier coefficient on the zero-spectral-mass branch

The previous six-sector / Hermitian bridge is an *unconditional polynomial*
identity, but the earlier actual Schwartz Fourier identification was made
only on a coherent sector with nonzero triple spectral mass. This module
closes the other branch by expanding the true Fourier kernel: each of its
four 3+3+1 gradient slots is a multiplier times three recovered Fourier
amplitudes, while the actual 3+2+2 interpolation kernel already has a
proved zero-mass theorem.

Consequently the whole, unphased full-third Fourier kernel vanishes when
any of the three recovered Fourier vectors has zero mass. This yields an
unconditional mass-gated physical-sector formula and an exact identity for
the *actual* positive-six-sector integral, with no division by spectral mass
and no implicit almost-everywhere nondegeneracy assumption.

The mass gate has NOT yet been removed from the transported six-polynomial
sum. Thus this does not claim that the real Schwartz integral equals the
ungated common-window Hermitian integral or has a strict sign.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypeActualZeroMass244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- One genuine seven-derivative gradient slot vanishes when a recovered
Fourier vector at one of the three triad frequencies vanishes. The seven
coordinate multipliers are unchanged. -/
theorem thirdFullAxisRealGradientSlot_zero_of_tripleMass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0)
    (j m n : A3) (a b c d e k v : V3) :
    thirdFullAxisRealGradientSlot244 ρ hρ A B C
      j m n a b c d e k v z = 0 := by
  have hTriple := thirdFullAxisRealSchwartzTripleComponent_zero_of_mass244
    ρ hρ A B C (WithLp.ofLp z.1, WithLp.ofLp z.2) hMass j m n
  rw [thirdFullAxisRealGradientSlot_factor244]
  change thirdFullGradientSevenWeight244 a b c d e k v z *
    ((thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
        (WithLp.ofLp z.1) j *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
        (thirdFullMiddleFrequency244
          (WithLp.ofLp z.1, WithLp.ofLp z.2)) m) *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
        (WithLp.ofLp z.2) n) = 0
  rw [hTriple]
  ring

/-- The sum of all four original physical 3+3+1 gradient patterns for a
fixed five-index choice vanishes on the zero-triple-mass branch. -/
theorem thirdFullAxisRealGradientAxisUnphased_zero_of_tripleMass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0)
    (j i k l r : A3) :
    thirdFullAxisRealGradientAxisUnphased244
      ρ hρ A B C j i k l r z = 0 := by
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection r
  -- `unfold` leaves a nested `have a := ...; have b := ...` zeta block.
  -- Normalize it to the literal four-slot sum before using the zero lemmas;
  -- otherwise `rw` does not see the slot applications syntactically.
  change (2 : ℂ) *
    (thirdFullAxisRealGradientSlot244 ρ hρ A B C
         j r j a b c a b c d z +
     thirdFullAxisRealGradientSlot244 ρ hρ A B C
         j j r a b c a b d c z +
     thirdFullAxisRealGradientSlot244 ρ hρ A B C
         j j r a b c a d c b z +
     thirdFullAxisRealGradientSlot244 ρ hρ A B C
         j j r a b c d b c a z) = 0
  rw [thirdFullAxisRealGradientSlot_zero_of_tripleMass244
        ρ hρ A B C z hMass j r j a b c a b c d,
      thirdFullAxisRealGradientSlot_zero_of_tripleMass244
        ρ hρ A B C z hMass j j r a b c a b d c,
      thirdFullAxisRealGradientSlot_zero_of_tripleMass244
        ρ hρ A B C z hMass j j r a b c a d c b,
      thirdFullAxisRealGradientSlot_zero_of_tripleMass244
        ρ hρ A B C z hMass j j r a b c d b c a]
  ring

/-- All five original physical derivative-axis sums vanish, with no
reordering or omission of their coefficients. -/
theorem thirdFullAxisRealGradientTotalUnphased_zero_of_tripleMass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0) :
    thirdFullAxisRealGradientTotalUnphased244 ρ hρ A B C z = 0 := by
  unfold thirdFullAxisRealGradientTotalUnphased244
  simp_rw [thirdFullAxisRealGradientAxisUnphased_zero_of_tripleMass244
    ρ hρ A B C z hMass]
  simp

/-- Crucial zero-mass branch for the COMPLETE real Schwartz 3+3+1 plus
3+2+2 Fourier kernel. This is not merely a zero theorem for a surrogate
polynomial or for the first interpolation monomial. -/
theorem thirdFullAxisRealThirdUnphasedKernel_zero_of_tripleMass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0) :
    thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z = 0 := by
  unfold thirdFullAxisRealThirdUnphasedKernel244
  rw [thirdFullAxisRealGradientTotalUnphased_zero_of_tripleMass244
        ρ hρ A B C z hMass,
      thirdFullAxisRealInterpolationKernel_zero_of_mass244
        ρ hρ A B C z hMass]
  ring

/-- Even its signed imaginary density vanishes on the entire zero-mass
branch, not only outside the known twelve-sector support tube. -/
theorem thirdFullAxisRealThirdImag_zero_of_tripleMass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im = 0 := by
  rw [thirdFullAxisRealThirdUnphasedKernel_zero_of_tripleMass244
    ρ hρ A B C z hMass]
  rfl

/-- A nonzero actual physical Fourier density automatically has nonzero
triple mass, so nondegeneracy need not be added as a new assumption. -/
theorem thirdFullAxisRealThirdImag_nonzero_tripleMass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244)
    (hKernel : (thirdFullAxisRealThirdUnphasedKernel244
      ρ hρ A B C z).im ≠ 0) :
    thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0 := by
  intro hMass
  exact hKernel (thirdFullAxisRealThirdImag_zero_of_tripleMass244
    ρ hρ A B C z hMass)

/-- The exact physical polynomial on a positive sector, with a guard
rather than an illicit assumption that its three Fourier vectors are
nonzero everywhere. No quotient or inverse occurs at zero. -/
noncomputable def thirdFullPositiveSectorMassGatedPhysical244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) : ℝ :=
  if thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0 then
    thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
      thirdFullPositiveSectorPhysicalCore244 A B C n z
  else 0

/-- Actual Fourier density, on EVERY point of a supported positive sector,
is the mass-gated windowed five-index physical coefficient. This combines
the established nonzero-mass equality with the new zero-mass theorem. -/
theorem thirdFullPositiveSectorActualImag_eq_massGated244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im =
      thirdFullPositiveSectorMassGatedPhysical244 ρ hρ A B C n z := by
  by_cases hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0
  · unfold thirdFullPositiveSectorMassGatedPhysical244
    rw [if_pos hMass]
    exact thirdFullPositiveSectorActualImag_window_core244
      ρ hρ hSmall δ hDisj A B C n z hSector hMass
  · have hZero : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
        (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0 := by
      by_contra hNe
      exact hMass hNe
    unfold thirdFullPositiveSectorMassGatedPhysical244
    rw [if_neg hMass]
    exact thirdFullAxisRealThirdImag_zero_of_tripleMass244
      ρ hρ A B C z hZero

/-- An integral identity on each actual, measurable positive sector; the
mass gate is evaluated INSIDE the original sector, before permutation. -/
theorem thirdFullPositiveSectorActualIntegral_eq_massGated244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) :
    (∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
        ∂volume.prod volume) =
      ∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
        thirdFullPositiveSectorMassGatedPhysical244 ρ hρ A B C n z
        ∂volume.prod volume := by
  let S : Set PairV244 := thirdFullHilbertCoherentSector244 (false, n) δ
  have hMeas : MeasurableSet S :=
    thirdFullHilbertCoherentSector_measurable244 (false, n) δ
  calc
    _ = ∫ z : PairV244,
          S.indicator (fun w =>
            (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C w).im) z
            ∂volume.prod volume := (integral_indicator hMeas).symm
    _ = ∫ z : PairV244,
          S.indicator (thirdFullPositiveSectorMassGatedPhysical244
            ρ hρ A B C n) z ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ S
      · simp only [Set.indicator_of_mem hz]
        exact thirdFullPositiveSectorActualImag_eq_massGated244
          ρ hρ hSmall δ hDisj A B C n z hz
      · simp only [Set.indicator_of_notMem hz]
    _ = _ := integral_indicator hMeas

/-- Exact positive-sector integral of the actual Schwartz velocity, with
all zero-mass points included. This is not a claim about a polynomial
integral outside its original positive-sector domain. -/
theorem thirdFullPositiveSixSectorIntegral_eq_massGated244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    thirdFullPositiveSixSectorIntegral244 ρ hρ A B C δ =
      ∑ n : Fin 6,
        ∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
          thirdFullPositiveSectorMassGatedPhysical244 ρ hρ A B C n z
          ∂volume.prod volume := by
  unfold thirdFullPositiveSixSectorIntegral244
  apply Finset.sum_congr rfl
  intro n _
  exact thirdFullPositiveSectorActualIntegral_eq_massGated244
    ρ hρ hSmall δ hDisj A B C n

/-- The COMPLETE actual real divergence-free Schwartz H3 commutator,
including the physical `(2π)^7` normalization and Hermitian orientation
factor 2, has an exact six-sector formula with no nonzero-mass hypothesis. -/
theorem thirdFullAxisRealThirdCommutator_eq_massGated_six244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
      2 * (2 * Real.pi) ^ 7 *
        (∑ n : Fin 6,
          ∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
            thirdFullPositiveSectorMassGatedPhysical244 ρ hρ A B C n z
            ∂volume.prod volume) := by
  rw [thirdFullAxisRealThirdCommutator_eq_global_six_sectors244
        ρ hρ hSmall δ hρδ hDisj A B C,
      thirdFullPositiveSixSectorIntegral_eq_massGated244
        ρ hρ hSmall δ hDisj A B C]

end
end PrimeTensor.FirstMonomialTriad
