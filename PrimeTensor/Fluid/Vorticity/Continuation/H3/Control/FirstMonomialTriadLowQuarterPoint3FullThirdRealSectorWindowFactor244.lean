import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorGradientPolynomial244
import Mathlib.Tactic

/-!
# Common scalar Fourier-window factor for the actual full H3 physical coefficient

Separate the three compact Schwartz cutoffs from the genuinely variable,
frequency-dependent, exactly transverse polarization germs.  The complete
five-index 3+3+1 gradient polynomial and the true 3+2+2 interpolation term
share one common scalar window product.  All identities in this file are
algebraic and preserve the complete physical seven-derivative weights.

The scalar factor is extracted from the six *positive* orientations.  The
full real Schwartz commutator still requires the proved reflected-sector
symmetry and an independent strict sign bound.  No pointwise sign for the
moving-polarization polynomial is asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeWindowFactor244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- One real transverse polynomial germ, with its scalar cutoff REMOVED.
It depends on the actual Fourier momentum, not just the sharp center. -/
noncomputable def thirdFullPositiveSectorBareGerm244
    (A B C : Freq244) (i : Fin 6) (ξ : Freq244) : Freq244 :=
  thirdFullFixedCenterTransverseGerm244
    (thirdFullAxisSixCenter244 i) ξ
    (thirdFullPositiveWindowPolarization244 A B C i)

/-- Product of the three distinct, correctly ordered real Schwartz windows.
All six permutations have their own actual momenta p, q=-p-r, r. -/
noncomputable def thirdFullPositiveSectorWindowProduct244
    (ρ : ℝ) (hρ : 0 < ρ) (n : Fin 6) (z : PairV244) : ℝ :=
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  ((thirdFullAxisWindowBump244 ρ hρ labels.1 : Freq244 → ℝ) p) *
    ((thirdFullAxisWindowBump244 ρ hρ middle : Freq244 → ℝ) q) *
    ((thirdFullAxisWindowBump244 ρ hρ labels.2 : Freq244 → ℝ) r)

/-- The remaining real Fourier triple, containing all three actual moving
transverse germs but NO compact window amplitude. -/
noncomputable def thirdFullPositiveSectorBareTriple244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (a b c : A3) : ℝ :=
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  (thirdFullPositiveSectorBareGerm244 A B C labels.1 p a *
    thirdFullPositiveSectorBareGerm244 A B C middle q b) *
    thirdFullPositiveSectorBareGerm244 A B C labels.2 r c

/-- Exact cutoff extraction from each already proved physical triple.
Purely algebraic: no coherence or nonzero-mass assumptions are needed. -/
theorem thirdFullPositiveSectorRealTripleFactor_window244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) (a b c : A3) :
    thirdFullPositiveSectorRealTripleFactor244 ρ hρ A B C n z a b c =
      thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
        thirdFullPositiveSectorBareTriple244 A B C n z a b c := by
  dsimp [thirdFullPositiveSectorRealTripleFactor244,
    thirdFullPositiveSectorWindowProduct244,
    thirdFullPositiveSectorBareTriple244,
    thirdFullPositiveSectorBareGerm244]
  ring

/-- Unwindowed physical 3+3+1 polynomial at one genuine five-index label.
The four seven-derivative patterns and the energy coefficient TWO are kept. -/
noncomputable def thirdFullPositiveSectorGradientAxisCore244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (j i k l t : A3) : ℝ :=
  let a := h3FourierAxisDirection i
  let b := h3FourierAxisDirection k
  let c := h3FourierAxisDirection l
  let d := h3FourierAxisDirection t
  2 * (((
    (thirdFullGradientSevenWeight244 a b c a b c d z).re *
      thirdFullPositiveSectorBareTriple244 A B C n z j t j +
    (thirdFullGradientSevenWeight244 a b c a b d c z).re *
      thirdFullPositiveSectorBareTriple244 A B C n z j j t) +
    (thirdFullGradientSevenWeight244 a b c a d c b z).re *
      thirdFullPositiveSectorBareTriple244 A B C n z j j t) +
    (thirdFullGradientSevenWeight244 a b c d b c a z).re *
      thirdFullPositiveSectorBareTriple244 A B C n z j j t)

/-- The true four-pattern axis polynomial is one scalar window product
times its cutoff-free variable-frequency polynomial. -/
theorem thirdFullPositiveSectorGradientAxis_window244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) (j i k l t : A3) :
    thirdFullPositiveSectorGradientAxisReal244 ρ hρ A B C n z j i k l t =
      thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
        thirdFullPositiveSectorGradientAxisCore244 A B C n z j i k l t := by
  dsimp only [thirdFullPositiveSectorGradientAxisReal244,
    thirdFullPositiveSectorGradientAxisCore244]
  simp_rw [thirdFullPositiveSectorRealTripleFactor_window244]
  ring

/-- Complete five-index gradient core. -/
noncomputable def thirdFullPositiveSectorGradientTotalCore244
    (A B C : Freq244) (n : Fin 6) (z : PairV244) : ℝ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ t : A3,
    thirdFullPositiveSectorGradientAxisCore244 A B C n z j i k l t

/-- Pull the common scalar window factor through ALL FIVE finite sums.
No selected gradient slot is privileged. -/
theorem thirdFullPositiveSectorGradientTotal_window244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) :
    thirdFullPositiveSectorGradientTotalReal244 ρ hρ A B C n z =
      thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
        thirdFullPositiveSectorGradientTotalCore244 A B C n z := by
  unfold thirdFullPositiveSectorGradientTotalReal244
    thirdFullPositiveSectorGradientTotalCore244
  simp_rw [thirdFullPositiveSectorGradientAxis_window244]
  simp only [Finset.mul_sum]

/-- Real dot of a scalar-multiplied polarization. -/
private theorem thirdFullSectorDotWindowRight244
    (u v : Freq244) (w : ℝ) :
    dot u (fun d => w * v d) = w * dot u v := by
  unfold dot
  calc
    (∑ d : A3, u d * (w * v d)) =
      ∑ d : A3, w * (u d * v d) := by
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ = _ := by
      rw [Finset.mul_sum]

/-- Dual scalar-multiplication identity for the non-Hermitian real dot. -/
private theorem thirdFullSectorDotWindowLeft244
    (u v : Freq244) (w : ℝ) :
    dot (fun d => w * u d) v = w * dot u v := by
  unfold dot
  calc
    (∑ d : A3, (w * u d) * v d) =
      ∑ d : A3, w * (u d * v d) := by
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ = _ := by
      rw [Finset.mul_sum]

/-- The frequency-side dot contracts the actual named windowed germ.
Do not expect `rw` to beta-reduce this named vector definition implicitly. -/
private theorem thirdFullSectorDotNamedWindowRight244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a ξ u : Freq244) :
    dot u (thirdFullSectorRealWindowGerm244 ρ hρ i a ξ) =
      (thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ *
        dot u (thirdFullFixedCenterTransverseGerm244
          (thirdFullAxisSixCenter244 i) ξ a) := by
  unfold thirdFullSectorRealWindowGerm244
  exact thirdFullSectorDotWindowRight244 _ _ _

/-- The vector-side dot contracts the named windowed germ in its first
argument, preserving the physical bilinear (not Hermitian) order. -/
private theorem thirdFullSectorDotNamedWindowLeft244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a ξ u : Freq244) :
    dot (thirdFullSectorRealWindowGerm244 ρ hρ i a ξ) u =
      (thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ *
        dot (thirdFullFixedCenterTransverseGerm244
          (thirdFullAxisSixCenter244 i) ξ a) u := by
  unfold thirdFullSectorRealWindowGerm244
  exact thirdFullSectorDotWindowLeft244 _ _ _

/-- Genuine 3+2+2 interpolation polynomial after removing ONLY the three
scalar windows. Both physical dot contractions retain their correct order. -/
noncomputable def thirdFullPositiveSectorInterpolationCore244
    (A B C : Freq244) (n : Fin 6) (z : PairV244) : ℝ :=
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  let gp := thirdFullPositiveSectorBareGerm244 A B C labels.1 p
  let gq := thirdFullPositiveSectorBareGerm244 A B C middle q
  let gr := thirdFullPositiveSectorBareGerm244 A B C labels.2 r
  dot p r * (dot p q) ^ 2 * dot r gq * dot gp gr

/-- The ACTUAL interpolation real polynomial shares precisely the same
three-window scalar factor as every seven-derivative gradient slot. -/
theorem thirdFullPositiveSectorInterpolation_window244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) :
    thirdFullPositiveSectorInterpolationReal244 ρ hρ A B C n z =
      thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
        thirdFullPositiveSectorInterpolationCore244 A B C n z := by
  -- Keep the *named* windowed germs visible until the specialized dot
  -- lemmas have extracted each scalar window from its own frequency.
  dsimp only [thirdFullPositiveSectorInterpolationReal244,
    thirdFullPositiveSectorWindowProduct244,
    thirdFullPositiveSectorInterpolationCore244,
    thirdFullPositiveSectorBareGerm244]
  rw [thirdFullSectorDotNamedWindowRight244,
      thirdFullSectorDotNamedWindowLeft244,
      thirdFullSectorDotNamedWindowRight244]
  ring

/-- The complete seven-derivative real polynomial, with its TWO and SIX,
now has NO frequency-window cutoffs at all. All actual moving transverse
germs and all five derivative-axis sums survive unchanged. -/
noncomputable def thirdFullPositiveSectorPhysicalCore244
    (A B C : Freq244) (n : Fin 6) (z : PairV244) : ℝ :=
  thirdFullPositiveSectorGradientTotalCore244 A B C n z +
    6 * thirdFullPositiveSectorInterpolationCore244 A B C n z

/-- Complete physical polynomial = common three-window product times
one genuine, cutoff-free variable-frequency five-index real coefficient.
This is an UNCONDITIONAL algebraic identity in the three actual windows. -/
theorem thirdFullPositiveSectorPhysicalPolynomial_window244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) :
    thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z =
      thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
        thirdFullPositiveSectorPhysicalCore244 A B C n z := by
  unfold thirdFullPositiveSectorPhysicalPolynomial244
    thirdFullPositiveSectorPhysicalCore244
  rw [thirdFullPositiveSectorGradientTotal_window244,
    thirdFullPositiveSectorInterpolation_window244]
  ring

/-- Link the unconditional factorization directly to the ACTUAL physical
Schwartz Fourier kernel on a coherent sector with nonzero triple mass. -/
theorem thirdFullPositiveSectorActualImag_window_core244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im =
      thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
        thirdFullPositiveSectorPhysicalCore244 A B C n z := by
  rw [thirdFullPositiveSector_full_imag_eq_physical_polynomial244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass]
  exact thirdFullPositiveSectorPhysicalPolynomial_window244 ρ hρ A B C n z

end
end PrimeTensor.FirstMonomialTriad
