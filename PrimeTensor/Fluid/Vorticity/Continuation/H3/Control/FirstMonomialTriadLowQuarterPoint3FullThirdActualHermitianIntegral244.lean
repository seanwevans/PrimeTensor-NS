import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalMassGateRemoval244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Exact full-third physical Schwartz commutator as a common-window Hermitian integral

The previous mass-gate theorem identifies the ACTUAL Fourier density with
its complete five-index polynomial on each of the six supported sectors.
The next task is not a sign argument: it is to prove that the windowed
polynomial has no support outside its own coherent Fourier-pair sector.

We use only its two exterior compact scalar windows. If the complete
polynomial is nonzero, these two windows are nonzero, so the first and last
frequencies lie in their own radius-ρ center balls. For ρ < δ this places
the pair inside the original measurable positive sector. Thus the sector
integral and the unrestricted polynomial integral are IDENTICAL.

The already formalized six-product-volume-preserving pair permutations and
the true five-index Hermitian bridge now identify the entire Schwartz
commutator with ONE actual compact three-window factor times the projected
Hermitian six-orbit. No sign or endpoint-regularity statement is inferred.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeActualHermitianIntegral244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- If the complete windowed five-index polynomial is nonzero, its two
exterior windows are both nonzero. The central window and the moving
polarizations remain completely arbitrary. -/
theorem thirdFullPositiveSectorPhysicalPolynomial_outerWindows_nonzero244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244)
    (hP : thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z ≠ 0) :
    let p : Freq244 := WithLp.ofLp z.1
    let r : Freq244 := WithLp.ofLp z.2
    let labels := lowNormalQuarterCoherentLabelPair false n
    (thirdFullAxisWindowBump244 ρ hρ labels.1 : Freq244 → ℝ) p ≠ 0 ∧
    (thirdFullAxisWindowBump244 ρ hρ labels.2 : Freq244 → ℝ) r ≠ 0 := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  let wp : ℝ := (thirdFullAxisWindowBump244 ρ hρ labels.1 : Freq244 → ℝ) p
  let wq : ℝ := (thirdFullAxisWindowBump244 ρ hρ middle : Freq244 → ℝ) q
  let wr : ℝ := (thirdFullAxisWindowBump244 ρ hρ labels.2 : Freq244 → ℝ) r
  have hWindow : thirdFullPositiveSectorWindowProduct244 ρ hρ n z ≠ 0 := by
    intro hZero
    apply hP
    rw [thirdFullPositiveSectorPhysicalPolynomial_window244, hZero]
    ring
  have hWin : (wp * wq) * wr ≠ 0 := hWindow
  have hwp : wp ≠ 0 := by
    intro hz
    apply hWin
    simp [hz]
  have hwr : wr ≠ 0 := by
    intro hz
    apply hWin
    simp [hz]
  exact ⟨hwp, hwr⟩

/-- The ACTUAL windowed full-third polynomial is supported in the
original axis-coordinate sup-metric coherent sector. The radius is that
of the compact windows; no Hilbert L2 ball is substituted. -/
theorem thirdFullPositiveSectorPhysicalPolynomial_mem_sector_of_nonzero244
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hρδ : ρ ≤ δ)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hP : thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z ≠ 0) :
    z ∈ thirdFullHilbertCoherentSector244 (false, n) δ := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let labels := lowNormalQuarterCoherentLabelPair false n
  obtain ⟨hwp, hwr⟩ :=
    thirdFullPositiveSectorPhysicalPolynomial_outerWindows_nonzero244
      ρ hρ A B C n z hP
  have hp : dist p (thirdFullAxisSixCenter244 labels.1) < ρ :=
    thirdFullAxisWindowBump_nonzero_ball244 ρ hρ labels.1 p hwp
  have hr : dist r (thirdFullAxisSixCenter244 labels.2) < ρ :=
    thirdFullAxisWindowBump_nonzero_ball244 ρ hρ labels.2 r hwr
  have hpδ : dist p (thirdFullAxisSixCenter244 labels.1) < δ :=
    lt_of_lt_of_le hp hρδ
  have hrδ : dist r (thirdFullAxisSixCenter244 labels.2) < δ :=
    lt_of_lt_of_le hr hρδ
  change dist (p,r)
    (thirdFullAxisSixCenter244 labels.1,
     thirdFullAxisSixCenter244 labels.2) < δ
  rw [Prod.dist_eq]
  exact max_lt_iff.mpr ⟨hpδ, hrδ⟩

/-- Contrapositive support exclusion for each of the six genuine windowed
physical polynomials, without any assumption on the recovered triple mass. -/
theorem thirdFullPositiveSectorPhysicalPolynomial_zero_off_sector244
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hρδ : ρ ≤ δ)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hz : z ∉ thirdFullHilbertCoherentSector244 (false, n) δ) :
    thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z = 0 := by
  by_contra hP
  exact hz (thirdFullPositiveSectorPhysicalPolynomial_mem_sector_of_nonzero244
    ρ hρ δ hρδ A B C n z hP)

/-- Every windowed physical polynomial is globally integrable. The proof
uses the actual Schwartz imaginary kernel, rather than presuming that a
cutoff-free high-degree polynomial is integrable. -/
theorem thirdFullPositiveSectorPhysicalPolynomial_integrable244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) :
    Integrable
      (thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n)
      (volume.prod volume) := by
  let S : Set PairV244 := thirdFullHilbertCoherentSector244 (false, n) δ
  let f : PairV244 → ℝ := fun z =>
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
  have hMeas : MeasurableSet S :=
    thirdFullHilbertCoherentSector_measurable244 (false, n) δ
  have hInt : Integrable f (volume.prod volume) :=
    thirdFullAxisImagKernel_integrable_global244 ρ hρ A B C
  have hEq : thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n =
      S.indicator f := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      exact (thirdFullPositiveSectorActualImag_eq_physicalPolynomial244
        ρ hρ hSmall δ hDisj A B C n z hz).symm
    · simp only [Set.indicator_of_notMem hz]
      exact thirdFullPositiveSectorPhysicalPolynomial_zero_off_sector244
        ρ hρ δ hρδ A B C n z hz
  rw [hEq]
  exact hInt.indicator hMeas

/-- An original positive-sector integral of the actual windowed polynomial
is exactly its FULL product-volume integral. This is the missing support
step before applying the proven six-permutation measure change. -/
theorem thirdFullPositiveSectorPhysicalPolynomial_integral_unrestrict244
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hρδ : ρ ≤ δ)
    (A B C : Freq244) (n : Fin 6) :
    (∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
      thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
      ∂volume.prod volume) =
    ∫ z : PairV244,
      thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
      ∂volume.prod volume := by
  let S : Set PairV244 := thirdFullHilbertCoherentSector244 (false, n) δ
  have hMeas : MeasurableSet S :=
    thirdFullHilbertCoherentSector_measurable244 (false, n) δ
  calc
    _ = ∫ z : PairV244,
        S.indicator (thirdFullPositiveSectorPhysicalPolynomial244
          ρ hρ A B C n) z ∂volume.prod volume :=
      (integral_indicator hMeas).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ S
      · simp only [Set.indicator_of_mem hz]
      · simp only [Set.indicator_of_notMem hz]
        exact (thirdFullPositiveSectorPhysicalPolynomial_zero_off_sector244
          ρ hρ δ hρδ A B C n z hz).symm

/-- The six physical-sector polynomial integrals, already identified with
the entire actual real Schwartz commutator, can now be integrated over the
whole Fourier-pair carrier without changing their value. -/
theorem thirdFullPositiveSixSectorIntegral_eq_unrestrictedPolynomials244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ ≤ δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    thirdFullPositiveSixSectorIntegral244 ρ hρ A B C δ =
      ∑ n : Fin 6,
        ∫ z : PairV244,
          thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
          ∂volume.prod volume := by
  rw [thirdFullPositiveSixSectorIntegral_eq_physicalPolynomials244
    ρ hρ hSmall δ hDisj A B C]
  apply Finset.sum_congr rfl
  intro n _
  exact thirdFullPositiveSectorPhysicalPolynomial_integral_unrestrict244
    ρ hρ δ hρδ A B C n

/-- Exact complete TRUE physical Schwartz H3 third commutator as the
common compact three-window product times the projected Hermitian kernel.
All reflected sectors, actual gradient and interpolation terms, and both
Fourier / spatial normalization factors have already been accounted for. -/
theorem thirdFullAxisRealThirdCommutator_eq_commonWindowHermitian244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
      2 * (2 * Real.pi) ^ 7 *
        (∫ z : PairV244,
          thirdFullPositiveCommonThreeWindow244 ρ hρ z *
            thirdFullProjectedHermitianKernel244
              (thirdFullAxisSixCenter244 0)
              (thirdFullAxisSixCenter244 1)
              (thirdFullAxisSixCenter244 2) A B C
              (WithLp.ofLp z.1, WithLp.ofLp z.2)
            ∂volume.prod volume) := by
  have hρle : ρ ≤ δ := le_of_lt hρδ
  have hInt : ∀ n : Fin 6,
      Integrable (thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n)
        (volume.prod volume) := by
    intro n
    exact thirdFullPositiveSectorPhysicalPolynomial_integrable244
      ρ hρ hSmall δ hρle hDisj A B C n
  have hSum :
      (∑ n : Fin 6,
        ∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
          thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
          ∂volume.prod volume) =
      (∑ n : Fin 6,
        ∫ z : PairV244,
          thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
          ∂volume.prod volume) := by
    apply Finset.sum_congr rfl
    intro n _
    exact thirdFullPositiveSectorPhysicalPolynomial_integral_unrestrict244
      ρ hρ δ hρle A B C n
  calc
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
        2 * (2 * Real.pi) ^ 7 *
          (∑ n : Fin 6,
            ∫ z in thirdFullHilbertCoherentSector244 (false, n) δ,
              thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
              ∂volume.prod volume) :=
        thirdFullAxisRealThirdCommutator_eq_physicalPolynomial_six244
          ρ hρ hSmall δ hρδ hDisj A B C
    _ = 2 * (2 * Real.pi) ^ 7 *
          (∑ n : Fin 6,
            ∫ z : PairV244,
              thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
              ∂volume.prod volume) := by
        rw [hSum]
    _ = _ := by
      rw [thirdFullPositivePhysicalSixPolynomialIntegrals_hermitian244
        ρ hρ A B C hInt]

end
end PrimeTensor.FirstMonomialTriad
