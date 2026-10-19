import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdActualZeroMassSector244
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Remove the full-third physical Fourier mass gate without division

The actual real Schwartz triple mass can vanish because a scalar cutoff
vanishes OR because an actual moving transverse polarization vanishes.
The previous theorem treated the true Fourier density but guarded the
physical polynomial by nonzero triple mass. This module shows that the
windowed physical polynomial itself vanishes on the zero-mass branch.

The key is the already proved exact five-index contraction to the physical
ordered symbol, trilinear in the THREE actual, variable-frequency germs.
When all three scalar cutoffs are nonzero, isolation of the recovered
Schwartz spectrum and its phase forces any zero Fourier vector to have
zero corresponding transverse germ. No inverse frequency or assumption
about pointwise Fourier nondegeneracy occurs.

All sector formulas below remain supported-sector formulas, not yet a claim
that an unrestricted polynomial integral equals a sector integral.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev PairV244 := H3FourierPoint3 × H3FourierPoint3

noncomputable local instance axisFintypeMassGateRemoval244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- In the corrected genuine seven-derivative ordered symbol, each velocity
polarization occurs linearly. The two physical dot contractions retain their
original order. -/
theorem thirdFullPhysicalOrderedSymbol_zero_first244
    (p q r U V W : Freq244) (hU : U = 0) :
    thirdFullPhysicalOrderedSymbol244 p q r U V W = 0 := by
  have hUW : thirdTriadAxisDot244 U W = 0 := by
    rw [hU]
    simp [thirdTriadAxisDot244]
  have hUV : thirdTriadAxisDot244 U V = 0 := by
    rw [hU]
    simp [thirdTriadAxisDot244]
  simp [thirdFullPhysicalOrderedSymbol244, hUW, hUV]

theorem thirdFullPhysicalOrderedSymbol_zero_middle244
    (p q r U V W : Freq244) (hV : V = 0) :
    thirdFullPhysicalOrderedSymbol244 p q r U V W = 0 := by
  have hVr : thirdTriadAxisDot244 V r = 0 := by
    rw [hV]
    simp [thirdTriadAxisDot244]
  have hUV : thirdTriadAxisDot244 U V = 0 := by
    rw [hV]
    simp [thirdTriadAxisDot244]
  simp [thirdFullPhysicalOrderedSymbol244, hVr, hUV]

theorem thirdFullPhysicalOrderedSymbol_zero_last244
    (p q r U V W : Freq244) (hW : W = 0) :
    thirdFullPhysicalOrderedSymbol244 p q r U V W = 0 := by
  have hUW : thirdTriadAxisDot244 U W = 0 := by
    rw [hW]
    simp [thirdTriadAxisDot244]
  have hWq : thirdTriadAxisDot244 W q = 0 := by
    rw [hW]
    simp [thirdTriadAxisDot244]
  simp [thirdFullPhysicalOrderedSymbol244, hUW, hWq]

/-- TRUE five-index physical core, not only one monomial, vanishes if any
of the three cut-off-free actual Schwartz germs is the zero vector. -/
theorem thirdFullPositiveSectorPhysicalCore_zero_of_bareGerm244
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hZero :
      thirdFullPositiveSectorBareGerm244 A B C
        (lowNormalQuarterCoherentLabelPair false n).1 (WithLp.ofLp z.1) = 0 ∨
      thirdFullPositiveSectorBareGerm244 A B C
        (thirdFullPositiveMiddleLabel244 n)
        (thirdFullMiddleFrequency244 (WithLp.ofLp z.1, WithLp.ofLp z.2)) = 0 ∨
      thirdFullPositiveSectorBareGerm244 A B C
        (lowNormalQuarterCoherentLabelPair false n).2 (WithLp.ofLp z.2) = 0) :
    thirdFullPositiveSectorPhysicalCore244 A B C n z = 0 := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let U := thirdFullPositiveSectorBareGerm244 A B C labels.1 p
  let V := thirdFullPositiveSectorBareGerm244 A B C
    (thirdFullPositiveMiddleLabel244 n) q
  let W := thirdFullPositiveSectorBareGerm244 A B C labels.2 r
  have hForm : thirdFullPositiveSectorPhysicalCore244 A B C n z =
      2 * thirdFullPhysicalOrderedSymbol244 p q r U V W :=
    thirdFullPositiveSectorPhysicalCore_eq_twice_corrected_variable244 A B C n z
  rcases hZero with hU | hV | hW
  · rw [hForm, thirdFullPhysicalOrderedSymbol_zero_first244 p q r U V W hU]
    ring
  · rw [hForm, thirdFullPhysicalOrderedSymbol_zero_middle244 p q r U V W hV]
    ring
  · rw [hForm, thirdFullPhysicalOrderedSymbol_zero_last244 p q r U V W hW]
    ring

/-- A nonzero primary cutoff exposes the actual Fourier packet at that
frequency. Its nonzero scalar cutoff and nonzero phase imply that a zero
recovered Fourier vector has a zero REAL, moving transverse germ. -/
theorem thirdFullActualSpectrum_zero_bareGerm_of_window244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (i : Fin 6)
    (hi : i = 0 ∨ i = 1 ∨ i = 2) (ξ : Freq244)
    (hw : (thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ ≠ 0)
    (hSpec : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C ξ = 0) :
    thirdFullPositiveSectorBareGerm244 A B C i ξ = 0 := by
  have hNear := thirdFullAxisWindowBump_nonzero_ball244 ρ hρ i ξ hw
  have hPacket := thirdFullAxisRealSpectrum_isolated_primary_label244
    ρ hρ hSep A B C i hi ξ hNear
  have hPhase : thirdFullPositiveWindowPhase244 i ≠ 0 := by
    fin_cases i <;> simp [thirdFullPositiveWindowPhase244]
  have hWC : ((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℂ) ≠ 0 := by
    exact_mod_cast hw
  funext d
  have hComp := congrFun (hPacket.symm.trans hSpec) d
  change (((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℂ) *
    thirdFullPositiveWindowPhase244 i *
    (thirdFullPositiveSectorBareGerm244 A B C i ξ d : ℂ)) = 0 at hComp
  have hWCPhase : (((thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ : ℂ) *
    thirdFullPositiveWindowPhase244 i) ≠ 0 := mul_ne_zero hWC hPhase
  have hRealZero : (thirdFullPositiveSectorBareGerm244 A B C i ξ d : ℂ) = 0 :=
    (mul_eq_zero.mp hComp).resolve_left hWCPhase
  exact_mod_cast hRealZero

/-- Zero of the actual triple spectral mass means that at least ONE of
its three full Fourier vectors vanishes. This includes zeros produced by
actual transverse polarizations, not merely zeros of scalar cutoffs. -/
theorem thirdFullActualTripleMass_zero_vector_alt244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (p r : Freq244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C (p,r) = 0) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p = 0 ∨
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 (p,r)) = 0 ∨
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r = 0 := by
  change (‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C p‖ *
    ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 (p,r))‖) *
    ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C r‖ = 0 at hMass
  rcases mul_eq_zero.mp hMass with hLeft | hRight
  · rcases mul_eq_zero.mp hLeft with hP | hQ
    · exact Or.inl (norm_eq_zero.mp hP)
    · exact Or.inr (Or.inl (norm_eq_zero.mp hQ))
  · exact Or.inr (Or.inr (norm_eq_zero.mp hRight))

/-- The windowed FULL five-index physical polynomial vanishes on the
actual zero-mass branch WITHOUT assuming the three window values vanish.
This is the key step previously missing from the physical Fourier bridge. -/
theorem thirdFullPositiveSectorPhysicalPolynomial_zero_of_tripleMass244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0) :
    thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z = 0 := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p,r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  let wp : ℝ := (thirdFullAxisWindowBump244 ρ hρ labels.1 : Freq244 → ℝ) p
  let wq : ℝ := (thirdFullAxisWindowBump244 ρ hρ middle : Freq244 → ℝ) q
  let wr : ℝ := (thirdFullAxisWindowBump244 ρ hρ labels.2 : Freq244 → ℝ) r
  rw [thirdFullPositiveSectorPhysicalPolynomial_window244]
  by_cases hWindow : thirdFullPositiveSectorWindowProduct244 ρ hρ n z = 0
  · rw [hWindow]
    ring
  have hWin : (wp * wq) * wr ≠ 0 := hWindow
  -- Extract each cutoff's nonvanishing by contradiction.  Do not use
  -- `mul_ne_zero.mp`: that decomposition lemma is not in this Mathlib API.
  have hwp : wp ≠ 0 := by
    intro hz
    apply hWin
    simp [hz]
  have hwq : wq ≠ 0 := by
    intro hz
    apply hWin
    simp [hz]
  have hwr : wr ≠ 0 := by
    intro hz
    apply hWin
    simp [hz]
  obtain ⟨hPrimaryP, hPrimaryQ, hPrimaryR⟩ :=
    thirdFullPositiveLabels_primary244 n
  have hSep : 2 * ρ ≤ 1 :=
    thirdFullAxisWindowBump_width_sep_of_nonresonance244 ρ hSmall
  obtain hSpecP | hSpecQ | hSpecR :=
    thirdFullActualTripleMass_zero_vector_alt244 ρ hρ A B C p r hMass
  · have hU := thirdFullActualSpectrum_zero_bareGerm_of_window244
      ρ hρ hSep A B C labels.1 hPrimaryP p hwp hSpecP
    have hCore := thirdFullPositiveSectorPhysicalCore_zero_of_bareGerm244
      A B C n z (Or.inl hU)
    rw [hCore]
    ring
  · have hV := thirdFullActualSpectrum_zero_bareGerm_of_window244
      ρ hρ hSep A B C middle hPrimaryQ q hwq hSpecQ
    have hCore := thirdFullPositiveSectorPhysicalCore_zero_of_bareGerm244
      A B C n z (Or.inr (Or.inl hV))
    rw [hCore]
    ring
  · have hW := thirdFullActualSpectrum_zero_bareGerm_of_window244
      ρ hρ hSep A B C labels.2 hPrimaryR r hwr hSpecR
    have hCore := thirdFullPositiveSectorPhysicalCore_zero_of_bareGerm244
      A B C n z (Or.inr (Or.inr hW))
    rw [hCore]
    ring

/-- Exactly the prior guarded sector density, now equal to its ungated
physical seven-derivative polynomial at EVERY frequency. -/
theorem thirdFullPositiveSectorMassGated_eq_physicalPolynomial244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (A B C : Freq244) (n : Fin 6) (z : PairV244) :
    thirdFullPositiveSectorMassGatedPhysical244 ρ hρ A B C n z =
      thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z := by
  by_cases hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0
  · unfold thirdFullPositiveSectorMassGatedPhysical244
    rw [if_pos hMass]
    exact (thirdFullPositiveSectorPhysicalPolynomial_window244 ρ hρ A B C n z).symm
  · have hZero : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
        (WithLp.ofLp z.1, WithLp.ofLp z.2) = 0 := by
      by_contra hn
      exact hMass hn
    rw [thirdFullPositiveSectorPhysicalPolynomial_zero_of_tripleMass244
      ρ hρ hSmall A B C n z hZero]
    unfold thirdFullPositiveSectorMassGatedPhysical244
    rw [if_neg hMass]

/-- The complete actual imaginary Fourier density equals the UNGATED
physical five-index polynomial on the genuine positive sector. -/
theorem thirdFullPositiveSectorActualImag_eq_physicalPolynomial244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false,n) δ) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im =
      thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z := by
  rw [thirdFullPositiveSectorActualImag_eq_massGated244
    ρ hρ hSmall δ hDisj A B C n z hSector]
  exact thirdFullPositiveSectorMassGated_eq_physicalPolynomial244
    ρ hρ hSmall A B C n z

/-- Integral on one supported physical Schwartz sector: no mass gate. -/
theorem thirdFullPositiveSectorActualIntegral_eq_physicalPolynomial244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) :
    (∫ z in thirdFullHilbertCoherentSector244 (false,n) δ,
      (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im
      ∂volume.prod volume) =
      ∫ z in thirdFullHilbertCoherentSector244 (false,n) δ,
        thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
        ∂volume.prod volume := by
  calc
    _ = ∫ z in thirdFullHilbertCoherentSector244 (false,n) δ,
        thirdFullPositiveSectorMassGatedPhysical244 ρ hρ A B C n z
        ∂volume.prod volume :=
      thirdFullPositiveSectorActualIntegral_eq_massGated244
        ρ hρ hSmall δ hDisj A B C n
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      exact thirdFullPositiveSectorMassGated_eq_physicalPolynomial244
        ρ hρ hSmall A B C n z

/-- The physically correct SIX sector integrals now carry the ungated
polynomial that is known to equal the projected Hermitian orbit in sum. -/
theorem thirdFullPositiveSixSectorIntegral_eq_physicalPolynomials244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    thirdFullPositiveSixSectorIntegral244 ρ hρ A B C δ =
      ∑ n : Fin 6,
        ∫ z in thirdFullHilbertCoherentSector244 (false,n) δ,
          thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
          ∂volume.prod volume := by
  rw [thirdFullPositiveSixSectorIntegral_eq_massGated244
      ρ hρ hSmall δ hDisj A B C]
  apply Finset.sum_congr rfl
  intro n _
  apply integral_congr_ae
  filter_upwards with z
  exact thirdFullPositiveSectorMassGated_eq_physicalPolynomial244
    ρ hρ hSmall A B C n z

/-- Actual real divergence-free Schwartz commutator equals the six
sector-restricted, UNGATED physical polynomials. No global integral
unrestriction and no static sign conclusion are presumed. -/
theorem thirdFullAxisRealThirdCommutator_eq_physicalPolynomial_six244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hρδ : ρ < δ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) :
    fullSchwartzThirdCommutator244
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
      2 * (2 * Real.pi) ^ 7 *
        (∑ n : Fin 6,
          ∫ z in thirdFullHilbertCoherentSector244 (false,n) δ,
            thirdFullPositiveSectorPhysicalPolynomial244 ρ hρ A B C n z
            ∂volume.prod volume) := by
  rw [thirdFullAxisRealThirdCommutator_eq_global_six_sectors244
    ρ hρ hSmall δ hρδ hDisj A B C,
    thirdFullPositiveSixSectorIntegral_eq_physicalPolynomials244
      ρ hρ hSmall δ hDisj A B C]

end
end PrimeTensor.FirstMonomialTriad
