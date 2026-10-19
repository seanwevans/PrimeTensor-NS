import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSixWindowPermutation244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalVariableSixOrbit244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# The transported six-sector genuine physical core and corrected ordered orbit

The six physical real Schwartz windows have already been shown to become one
identical cutoff after the six measure-preserving Fourier-pair permutations.
Here we retain the ACTUAL full five-index 3+3+1 gradient plus 3+2+2
interpolation core in each sector and transport its order simultaneously.

This module proves an unconditional pointwise physical polynomial factorization
and an exact integral identity for the six transported cores. The corrected
ordered symbols retain their three distinct moving transverse germs.

The remaining, independent analytic obligation is to identify this corrected
ordered six-term sum with the projected Hermitian six-orbit with a SINGLE
assignment of original sharp center and polarization labels. A strict sign of
an individual Fourier sector is not claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3
private abbrev PairV244 := V3 × V3

noncomputable local instance axisFintypePhysicalTransportedCore244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Six ACTUAL cutoff-free full-third physical coefficients after their own
correct measure-preserving positive-sector momentum permutations. -/
noncomputable def thirdFullPositivePhysicalSixTransportedCore244
    (A B C : Freq244) (z : PairV244) : ℝ :=
  ∑ n : Fin 6,
    thirdFullPositiveSectorPhysicalCore244 A B C n
      (thirdFullPositivePairPermutationEquiv244 n z)

/-- A symbol-level expression with all original moving solenoidal germs
and the ORIGINAL physical momentum order for each sector. This is not the
older fixed-polarization six-symbol substituted into an individual slot. -/
noncomputable def thirdFullPositivePhysicalSixTransportedCorrected244
    (A B C : Freq244) (z : PairV244) : ℝ :=
  ∑ n : Fin 6,
    let w := thirdFullPositivePairPermutationEquiv244 n z
    let p : Freq244 := WithLp.ofLp w.1
    let r : Freq244 := WithLp.ofLp w.2
    let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    let middle := thirdFullPositiveMiddleLabel244 n
    let U := thirdFullPositiveSectorBareGerm244 A B C labels.1 p
    let V := thirdFullPositiveSectorBareGerm244 A B C middle q
    let W := thirdFullPositiveSectorBareGerm244 A B C labels.2 r
    thirdFullPhysicalOrderedSymbol244 p q r U V W

/-- An unconditional comparison of all six TRUE physical ordered cores
with their corrected ordered polynomial, including each sector's different
moving transverse germs. All five physical derivative indices have already
been contracted by the imported theorem; no center or mass restriction. -/
theorem thirdFullPositivePhysicalSixTransportedCore_eq_twice_corrected244
    (A B C : Freq244) (z : PairV244) :
    thirdFullPositivePhysicalSixTransportedCore244 A B C z =
      2 * thirdFullPositivePhysicalSixTransportedCorrected244 A B C z := by
  unfold thirdFullPositivePhysicalSixTransportedCore244
    thirdFullPositivePhysicalSixTransportedCorrected244
  calc
    (∑ n : Fin 6,
        thirdFullPositiveSectorPhysicalCore244 A B C n
          (thirdFullPositivePairPermutationEquiv244 n z)) =
      ∑ n : Fin 6, 2 *
        (let w := thirdFullPositivePairPermutationEquiv244 n z
         let p : Freq244 := WithLp.ofLp w.1
         let r : Freq244 := WithLp.ofLp w.2
         let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
         let labels := lowNormalQuarterCoherentLabelPair false n
         let middle := thirdFullPositiveMiddleLabel244 n
         let U := thirdFullPositiveSectorBareGerm244 A B C labels.1 p
         let V := thirdFullPositiveSectorBareGerm244 A B C middle q
         let W := thirdFullPositiveSectorBareGerm244 A B C labels.2 r
         thirdFullPhysicalOrderedSymbol244 p q r U V W) := by
      apply Finset.sum_congr rfl
      intro n _
      exact thirdFullPositiveSectorPhysicalCore_eq_twice_corrected_variable244
        A B C n (thirdFullPositivePairPermutationEquiv244 n z)
    _ = _ := by rw [Finset.mul_sum]

/-- EXACT pointwise identity for six REAL full-third physical ordered
polynomials: the transported true windowed seven-derivative expression is
ONE actual nonnegative three-window scalar times the full six-term core.
No hypotheses on mass or sector support are required for the polynomial. -/
theorem thirdFullPositivePhysicalSixPolynomials_common_window244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    (∑ n : Fin 6,
       thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n
         (thirdFullPositivePairPermutationEquiv244 n z)) =
      thirdFullPositiveCommonThreeWindow244 ρ hρ z *
        thirdFullPositivePhysicalSixTransportedCore244 A B C z := by
  unfold thirdFullPositivePhysicalSixTransportedCore244
  calc
    _ = ∑ n : Fin 6,
          thirdFullPositiveCommonThreeWindow244 ρ hρ z *
            thirdFullPositiveSectorPhysicalCore244 A B C n
              (thirdFullPositivePairPermutationEquiv244 n z) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [thirdFullPositiveSectorPhysicalPolynomial_window244,
        thirdFullPositiveSectorWindowProduct_permuted244]
    _ = _ := by rw [Finset.mul_sum]

/-- The same unconditional factorization, but entirely in terms of the
corrected ordered six-sector polynomial and the genuine Schwartz cutoffs. -/
theorem thirdFullPositivePhysicalSixPolynomials_corrected_window244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : PairV244) :
    (∑ n : Fin 6,
       thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n
         (thirdFullPositivePairPermutationEquiv244 n z)) =
      thirdFullPositiveCommonThreeWindow244 ρ hρ z *
        (2 * thirdFullPositivePhysicalSixTransportedCorrected244 A B C z) := by
  rw [thirdFullPositivePhysicalSixPolynomials_common_window244,
    thirdFullPositivePhysicalSixTransportedCore_eq_twice_corrected244]

/-- Exact integration of the SIX ACTUAL physical polynomials, not a bare
sharp surrogate. Integrability is explicit because these are the separately
labeled (rather than support-restricted) polynomial expressions. This does
not assert their integrals equal the full physical Fourier density without
the sector/support and zero-triple-mass identities. -/
theorem thirdFullPositivePhysicalSixPolynomialIntegrals_corrected244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (hInt : ∀ n : Fin 6,
      Integrable
        (thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n)
        (volume.prod volume)) :
    (∑ n : Fin 6,
      ∫ z : PairV244,
        thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
        ∂volume.prod volume) =
      ∫ z : PairV244,
        thirdFullPositiveCommonThreeWindow244 ρ hρ z *
          (2 * thirdFullPositivePhysicalSixTransportedCorrected244 A B C z)
        ∂volume.prod volume := by
  have hWeighted (n : Fin 6) :
      Integrable (fun z : PairV244 =>
        thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
          thirdFullPositiveSectorPhysicalCore244 A B C n z)
        (volume.prod volume) := by
    have hEq :
        (fun z : PairV244 =>
          thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
            thirdFullPositiveSectorPhysicalCore244 A B C n z) =
          thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n := by
      funext z
      exact (thirdFullPositiveSectorPhysicalPolynomial_window244
        ρ hρ A B C n z).symm
    rw [hEq]
    exact hInt n
  calc
    _ = ∑ n : Fin 6,
        ∫ z : PairV244,
          thirdFullPositiveSectorWindowProduct244 ρ hρ n z *
            thirdFullPositiveSectorPhysicalCore244 A B C n z
          ∂volume.prod volume := by
      apply Finset.sum_congr rfl
      intro n _
      apply integral_congr_ae
      filter_upwards with z
      exact thirdFullPositiveSectorPhysicalPolynomial_window244
        ρ hρ A B C n z
    _ = ∫ z : PairV244,
          thirdFullPositiveCommonThreeWindow244 ρ hρ z *
            thirdFullPositivePhysicalSixTransportedCore244 A B C z
          ∂volume.prod volume := by
      exact thirdFullPositiveSixWindowWeighted_integral244 ρ hρ
        (fun n z => thirdFullPositiveSectorPhysicalCore244 A B C n z)
        hWeighted
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [thirdFullPositivePhysicalSixTransportedCore_eq_twice_corrected244]

end
end PrimeTensor.FirstMonomialTriad
