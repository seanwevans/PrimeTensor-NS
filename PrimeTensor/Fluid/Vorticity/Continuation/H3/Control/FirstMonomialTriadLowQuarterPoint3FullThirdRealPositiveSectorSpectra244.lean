import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSingleWindowIsolation244
import Mathlib.Tactic

/-!
# Exact triple-spectrum identification in every positive coherent sector

The global full-third physical H3 commutator is twice a sum of six actual
positive-orientation sector integrals. The individual Fourier windows are
already isolated near the six centers. Here we identify, at each of the SIX
positive momentum-pair orientations, which three window labels survive when
the actual real Schwartz Fourier triple mass is nonzero.

The dependent middle momentum is q = -p-r. We do NOT presume that proximity
of p and r alone implies q belongs to its window: nonvanishing of the actual
triple mass supplies that missing spectral fact, and the committed twelve-
center zero-momentum classification forces the unique remaining positive
middle label. The resulting triple product is an exact physical Schwartz
Fourier identity retaining phases 1, 1, I and the moving transverse germs.

No sign estimate or pointwise equivalence of the full physical commutator to
the earlier six-order sharp polynomial is assumed in this module.
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

noncomputable local instance axisFintypePositiveSectorSpectra244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The middle frequency of each of the six ordered positive pairs has the
remaining one of the three positive center labels. -/
def thirdFullPositiveMiddleLabel244 (n : Fin 6) : Fin 6 :=
  match n.val with
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | _ => 2

/-- All six ordered positive center triples have precisely their asserted
middle labels, and the finite resonance classification forces uniqueness. -/
theorem thirdFullPositiveMiddleLabel_unique244 (n j : Fin 6)
    (hCoherent : lowNormalCoherentCenters
      (lowNormalQuarterCoherentLabelPair false n).1 j
      (lowNormalQuarterCoherentLabelPair false n).2) :
    j = thirdFullPositiveMiddleLabel244 n := by
  -- Do not simplify a symbolic Fin equality with Fin.ext_iff: that can
  -- trigger the middle-label equation compiler's recursive simp rule.
  -- Instead close each of the 36 *ground* finite propositions by kernel
  -- computation.  The variables a and b are introduced before fin_cases,
  -- so the branches contain no references to eliminated local variables.
  have hCases :
      ∀ (a b : Fin 6),
        lowNormalCoherentCenters
          (lowNormalQuarterCoherentLabelPair false a).1 b
          (lowNormalQuarterCoherentLabelPair false a).2 →
        b = thirdFullPositiveMiddleLabel244 a := by
    intro a b
    -- Unfold the named coherence predicate BEFORE invoking `decide`.
    -- Otherwise Lean cannot synthesize a Decidable instance for the opaque
    -- `lowNormalCoherentCenters` application in each ground case.
    -- `dsimp` computes the concrete Fin indices and the middle-label match
    -- without introducing `Fin.ext_iff` as a simplifier rewrite rule.
    fin_cases a <;> fin_cases b <;>
      (dsimp [lowNormalCoherentCenters,
        lowNormalQuarterCoherentLabelPair,
        thirdFullPositiveMiddleLabel244] <;> decide)
  exact hCases n j hCoherent

/-- Every outer and middle window selected by a positive coherent sector
belongs to the positive three-center orientation, not its reflected mate. -/
theorem thirdFullPositiveLabels_primary244 (n : Fin 6) :
    ((lowNormalQuarterCoherentLabelPair false n).1 = 0 ∨
      (lowNormalQuarterCoherentLabelPair false n).1 = 1 ∨
      (lowNormalQuarterCoherentLabelPair false n).1 = 2) ∧
    (thirdFullPositiveMiddleLabel244 n = 0 ∨
      thirdFullPositiveMiddleLabel244 n = 1 ∨
      thirdFullPositiveMiddleLabel244 n = 2) ∧
    ((lowNormalQuarterCoherentLabelPair false n).2 = 0 ∨
      (lowNormalQuarterCoherentLabelPair false n).2 = 1 ∨
      (lowNormalQuarterCoherentLabelPair false n).2 = 2) := by
  fin_cases n <;>
    simp [thirdFullPositiveMiddleLabel244, lowNormalQuarterCoherentLabelPair]

/-- The prescribed Fourier polarization for one of the three positive labels.
Keeping this as a function of the label makes the six permutations literal. -/
def thirdFullPositiveWindowPolarization244
    (A B C : Freq244) (i : Fin 6) : Freq244 :=
  if i = 0 then A else if i = 1 then B else C

/-- The essential imaginary phase is attached to r, irrespective of which
slot of the ordered momentum pair it occupies. -/
def thirdFullPositiveWindowPhase244 (i : Fin 6) : ℂ :=
  if i = 2 then Complex.I else 1

/-- The six permutations change which frequency carries the imaginary
phase, but never the total phase product: exactly one of the three labels is
2, so their cubic phase is always I. No cyclic-sign assumption is used. -/
theorem thirdFullPositiveSector_phase_product244 (n : Fin 6) :
    thirdFullPositiveWindowPhase244
        (lowNormalQuarterCoherentLabelPair false n).1 *
      thirdFullPositiveWindowPhase244 (thirdFullPositiveMiddleLabel244 n) *
      thirdFullPositiveWindowPhase244
        (lowNormalQuarterCoherentLabelPair false n).2 = Complex.I := by
  -- After fixing the finite orientation, simplify *both* levels of the
  -- nested `if i = 2` expressions; `norm_num` alone left the `ite`s intact.
  fin_cases n <;>
    simp [thirdFullPositiveWindowPhase244,
      thirdFullPositiveMiddleLabel244, lowNormalQuarterCoherentLabelPair]

/-- Uniform version of the three previously established one-window spectral
identities; the positive label determines its exact phase and germ. -/
theorem thirdFullAxisRealSpectrum_isolated_primary_label244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (i : Fin 6)
    (hi : i = 0 ∨ i = 1 ∨ i = 2) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 i) < ρ) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C ξ =
      thirdFullAxisComplexWindowPacket244 ρ hρ i
        (thirdFullPositiveWindowPolarization244 A B C i)
        (thirdFullPositiveWindowPhase244 i) ξ := by
  rcases hi with rfl | rfl | rfl
  · simpa [thirdFullPositiveWindowPolarization244,
      thirdFullPositiveWindowPhase244] using
      (thirdFullAxisRealSchwartzSpectrum_isolated_zero244
        ρ hρ hSep A B C ξ hNear)
  · simpa [thirdFullPositiveWindowPolarization244,
      thirdFullPositiveWindowPhase244] using
      (thirdFullAxisRealSchwartzSpectrum_isolated_one244
        ρ hρ hSep A B C ξ hNear)
  · simpa [thirdFullPositiveWindowPolarization244,
      thirdFullPositiveWindowPhase244] using
      (thirdFullAxisRealSchwartzSpectrum_isolated_two244
        ρ hρ hSep A B C ξ hNear)

/-- A nonzero physical triple mass forces each of the three recovered Fourier
vectors to be nonzero; this is stronger than a bare sector-membership claim. -/
theorem thirdFullActualTripleMass_nonzero_factors244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (p r : Freq244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C (p, r) ≠ 0) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p ≠ 0 ∧
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 (p, r)) ≠ 0 ∧
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r ≠ 0 := by
  constructor
  · intro h
    apply hMass
    simp [thirdFullAxisRealSchwartzTripleMass244, h]
  constructor
  · intro h
    apply hMass
    simp [thirdFullAxisRealSchwartzTripleMass244, h]
  · intro h
    apply hMass
    simp [thirdFullAxisRealSchwartzTripleMass244, h]

/-- Physical sector membership, combined with nonzero Schwartz triple mass,
uniquely determines the THREE individual surviving Fourier window labels.
In particular the dependent middle frequency cannot come from a reflected
or differently permuted Fourier window. -/
theorem thirdFullPositiveSector_three_center_labels244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    dist p (thirdFullAxisSixCenter244 labels.1) < ρ ∧
    dist q (thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n)) < ρ ∧
    dist r (thirdFullAxisSixCenter244 labels.2) < ρ := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  have hSep : 2 * ρ ≤ 1 :=
    thirdFullAxisWindowBump_width_sep_of_nonresonance244 ρ hSmall
  have hSectorPair :
      dist (p,r) (thirdFullCoherentPairLabel244 (false,n)) < δ := by
    exact hSector
  have hSectorBoth :
      dist p (thirdFullAxisSixCenter244 labels.1) < δ ∧
      dist r (thirdFullAxisSixCenter244 labels.2) < δ := by
    change dist (p,r)
      (thirdFullAxisSixCenter244 labels.1,
       thirdFullAxisSixCenter244 labels.2) < δ at hSectorPair
    simpa only [Prod.dist_eq, max_lt_iff] using hSectorPair
  have hSectorP := hSectorBoth.1
  have hSectorR := hSectorBoth.2
  obtain ⟨hp, hq, hr⟩ :=
    thirdFullActualTripleMass_nonzero_factors244 ρ hρ A B C p r hMass
  rw [thirdFullAxisRealSchwartzSpectrum_eq_packet244] at hp hq hr
  obtain ⟨i, hi⟩ := thirdFullAxisSixFourierPacket_nonzero_center244
    ρ hρ A B C p hp
  obtain ⟨j, hj⟩ := thirdFullAxisSixFourierPacket_nonzero_center244
    ρ hρ A B C q hq
  obtain ⟨k, hk⟩ := thirdFullAxisSixFourierPacket_nonzero_center244
    ρ hρ A B C r hr
  have hiLabel : i = labels.1 := by
    by_contra hn
    have hGap := thirdFullSixAxisCenters_dist_gap244 i labels.1 hn
    have hTri := dist_triangle (thirdFullAxisSixCenter244 i) p
      (thirdFullAxisSixCenter244 labels.1)
    have hi' : dist (thirdFullAxisSixCenter244 i) p < ρ := by
      simpa only [dist_comm] using hi
    linarith
  have hkLabel : k = labels.2 := by
    by_contra hn
    have hGap := thirdFullSixAxisCenters_dist_gap244 k labels.2 hn
    have hTri := dist_triangle (thirdFullAxisSixCenter244 k) r
      (thirdFullAxisSixCenter244 labels.2)
    have hk' : dist (thirdFullAxisSixCenter244 k) r < ρ := by
      simpa only [dist_comm] using hk
    linarith
  have hCoordinate (i : Fin 6) (ξ : Freq244)
      (hNear : dist ξ (thirdFullAxisSixCenter244 i) < ρ) :
      ∀ a : A3, |ξ a - thirdFullAxisSixCenter244 i a| <
        lowNormalSixCenterSeparationRadius (1 : ℝ) := by
    intro a
    have hc : |ξ a - thirdFullAxisSixCenter244 i a| ≤
        dist ξ (thirdFullAxisSixCenter244 i) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply, dist_eq_norm] using
        (norm_le_pi_norm (ξ - thirdFullAxisSixCenter244 i) a)
    exact lt_of_le_of_lt hc (lt_of_lt_of_le hNear hSmall)
  have hCoherent : lowNormalCoherentCenters i j k := by
    apply thirdFullAxisSixCenter_coordinateBall_zero_sum_coherent244
      i j k p q r (hCoordinate i p hi)
        (hCoordinate j q hj) (hCoordinate k r hk)
    intro a
    dsimp [q, thirdFullMiddleFrequency244]
    ring
  have hMiddleLabel : j = thirdFullPositiveMiddleLabel244 n := by
    apply thirdFullPositiveMiddleLabel_unique244 n j
    simpa only [hiLabel, hkLabel] using hCoherent
  change dist p (thirdFullAxisSixCenter244 labels.1) < ρ ∧
    dist q (thirdFullAxisSixCenter244 (thirdFullPositiveMiddleLabel244 n)) < ρ ∧
    dist r (thirdFullAxisSixCenter244 labels.2) < ρ
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hiLabel] using hi
  · simpa only [hMiddleLabel] using hj
  · simpa only [hkLabel] using hk

/-- Every nonzero actual physical three-frequency product on a positive
coherent sector is EXACTLY the prescribed ordered product of THREE isolated
windowed transverse germs, with the phase I attached to label two. This is
not merely a sharp-center identity: all Fourier frequencies remain variable. -/
theorem thirdFullPositiveSector_actual_triple_spectra244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p =
      thirdFullAxisComplexWindowPacket244 ρ hρ labels.1
        (thirdFullPositiveWindowPolarization244 A B C labels.1)
        (thirdFullPositiveWindowPhase244 labels.1) p ∧
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C q =
      thirdFullAxisComplexWindowPacket244 ρ hρ
        (thirdFullPositiveMiddleLabel244 n)
        (thirdFullPositiveWindowPolarization244 A B C
          (thirdFullPositiveMiddleLabel244 n))
        (thirdFullPositiveWindowPhase244
          (thirdFullPositiveMiddleLabel244 n)) q ∧
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r =
      thirdFullAxisComplexWindowPacket244 ρ hρ labels.2
        (thirdFullPositiveWindowPolarization244 A B C labels.2)
        (thirdFullPositiveWindowPhase244 labels.2) r := by
  have hNear := thirdFullPositiveSector_three_center_labels244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
  have hLabels := thirdFullPositiveLabels_primary244 n
  dsimp only at hNear ⊢
  constructor
  · exact thirdFullAxisRealSpectrum_isolated_primary_label244
      ρ hρ (thirdFullAxisWindowBump_width_sep_of_nonresonance244 ρ hSmall)
      A B C _ hLabels.1 _ hNear.1
  constructor
  · exact thirdFullAxisRealSpectrum_isolated_primary_label244
      ρ hρ (thirdFullAxisWindowBump_width_sep_of_nonresonance244 ρ hSmall)
      A B C _ hLabels.2.1 _ hNear.2.1
  · exact thirdFullAxisRealSpectrum_isolated_primary_label244
      ρ hρ (thirdFullAxisWindowBump_width_sep_of_nonresonance244 ρ hSmall)
      A B C _ hLabels.2.2 _ hNear.2.2

/-- The trilinear Fourier component entering every one of the 3+3+1
physical gradient slots is the product of the actual isolated windowed
germs. This keeps the three ordered frequency positions and phase I exact. -/
theorem thirdFullPositiveSector_actual_triple_component244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (a b c : A3) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    let middle := thirdFullPositiveMiddleLabel244 n
    (thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p a *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C q b) *
      thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r c =
    (thirdFullAxisComplexWindowPacket244 ρ hρ labels.1
        (thirdFullPositiveWindowPolarization244 A B C labels.1)
        (thirdFullPositiveWindowPhase244 labels.1) p a *
      thirdFullAxisComplexWindowPacket244 ρ hρ middle
        (thirdFullPositiveWindowPolarization244 A B C middle)
        (thirdFullPositiveWindowPhase244 middle) q b) *
      thirdFullAxisComplexWindowPacket244 ρ hρ labels.2
        (thirdFullPositiveWindowPolarization244 A B C labels.2)
        (thirdFullPositiveWindowPhase244 labels.2) r c := by
  obtain ⟨hP, hQ, hR⟩ := thirdFullPositiveSector_actual_triple_spectra244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
  dsimp only at hP hQ hR ⊢
  rw [hP, hQ, hR]

/-- One complete ACTUAL seven-derivative 3+3+1 gradient slot is the physical
seven-frequency weight times the three precisely isolated moving-germ
Fourier factors. This does not replace that weight by an auxiliary symbol. -/
theorem thirdFullPositiveSector_actual_gradient_slot244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0)
    (j m t : A3) (a b c d e k v : H3FourierPoint3) :
    let p := WithLp.ofLp z.1
    let r := WithLp.ofLp z.2
    let q := thirdFullMiddleFrequency244 (p, r)
    let labels := lowNormalQuarterCoherentLabelPair false n
    let middle := thirdFullPositiveMiddleLabel244 n
    thirdFullAxisRealGradientSlot244 ρ hρ A B C j m t a b c d e k v z =
    thirdFullGradientSevenWeight244 a b c d e k v z *
      ((thirdFullAxisComplexWindowPacket244 ρ hρ labels.1
          (thirdFullPositiveWindowPolarization244 A B C labels.1)
          (thirdFullPositiveWindowPhase244 labels.1) p j *
        thirdFullAxisComplexWindowPacket244 ρ hρ middle
          (thirdFullPositiveWindowPolarization244 A B C middle)
          (thirdFullPositiveWindowPhase244 middle) q m) *
        thirdFullAxisComplexWindowPacket244 ρ hρ labels.2
          (thirdFullPositiveWindowPolarization244 A B C labels.2)
          (thirdFullPositiveWindowPhase244 labels.2) r t) := by
  rw [thirdFullAxisRealGradientSlot_factor244]
  exact congrArg
    (fun w : ℂ => thirdFullGradientSevenWeight244 a b c d e k v z * w)
    (thirdFullPositiveSector_actual_triple_component244
      ρ hρ hSmall δ hDisj A B C n z hSector hMass j m t)

end
end PrimeTensor.FirstMonomialTriad
