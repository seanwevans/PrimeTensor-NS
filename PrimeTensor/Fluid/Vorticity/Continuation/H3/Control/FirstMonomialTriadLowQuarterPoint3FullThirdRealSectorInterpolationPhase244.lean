import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealSectorPhaseFactor244
import Mathlib.Tactic

/-!
# Actual 3+2+2 interpolation: exact real coefficient and cubic Fourier phase

The previous six-sector calculation extracted the single imaginary cubic phase
of each actual 3+3+1 gradient slot. Here we do the SAME calculation for the
literal interpolation kernel `complexCoefficient * amplitudeDot`, using its
existing two contractions rather than an independently assumed symbol.

Both contractions are bilinear and contain NO complex conjugate. Their
separate phases multiply to exactly I in each positive coherent sector.
Consequently the true interpolation kernel is I times a REAL coefficient at
every point where the recovered Schwartz triple mass is nonzero. The entire
unphased third-order kernel is then the old five-index gradient imaginary
part plus six times this real interpolation coefficient.

No pointwise sign or global noncancellation of the six sectors is assumed.
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

noncomputable local instance axisFintypeSectorInterpPhase244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pull a constant complex phase out of the exact *bilinear*, not
Hermitian, frequency-polarization contraction used by the true physical
interpolation kernel. -/
theorem thirdFullSectorMixedDot_real_phase244
    (r v : Freq244) (β : ℂ) :
    mixedDot r (fun d => (v d : ℂ) * β) = (dot r v : ℂ) * β := by
  unfold mixedDot dot
  calc
    (∑ d : A3, (r d : ℂ) * ((v d : ℂ) * β)) =
        ∑ d : A3, ((r d * v d : ℝ) : ℂ) * β := by
          apply Finset.sum_congr rfl
          intro d _
          push_cast
          ring
    _ = (∑ d : A3, ((r d * v d : ℝ) : ℂ)) * β := by
          rw [Finset.sum_mul]
    _ = ((∑ d : A3, r d * v d : ℝ) : ℂ) * β := by
          push_cast; rfl

/-- Pull two independent constant phases out of the ACTUAL bilinear outer
polarization contraction. This is not an inner product with conjugation. -/
theorem thirdFullSectorAmplitudeDot_real_phases244
    (u w : Freq244) (α γ : ℂ) :
    amplitudeDot (fun d => (u d : ℂ) * α) (fun d => (w d : ℂ) * γ) =
      (dot u w : ℂ) * (α * γ) := by
  unfold amplitudeDot dot
  calc
    (∑ d : A3, ((u d : ℂ) * α) * ((w d : ℂ) * γ)) =
        ∑ d : A3, ((u d * w d : ℝ) : ℂ) * (α * γ) := by
          apply Finset.sum_congr rfl
          intro d _
          push_cast
          ring
    _ = (∑ d : A3, ((u d * w d : ℝ) : ℂ)) * (α * γ) := by
          rw [Finset.sum_mul]
    _ = ((∑ d : A3, u d * w d : ℝ) : ℂ) * (α * γ) := by
          push_cast; rfl

/-- The TRUE 3+2+2 interpolation coefficient with three real moving
polarizations is the physical real frequency polynomial times their two
real contractions, multiplied by the THREE prescribed complex phases. -/
theorem thirdFullSectorInterpolation_real_phase244
    (p q r u v w : Freq244) (α β γ : ℂ) :
    complexCoefficient p q r (fun d => (v d : ℂ) * β) *
      amplitudeDot (fun d => (u d : ℂ) * α)
        (fun d => (w d : ℂ) * γ) =
      (((dot p r * (dot p q) ^ 2 * dot r v * dot u w : ℝ) : ℂ) *
        (α * β * γ)) := by
  unfold complexCoefficient
  rw [thirdFullSectorMixedDot_real_phase244,
    thirdFullSectorAmplitudeDot_real_phases244]
  push_cast; ring

/-- A real window times a real transverse polynomial germ has precisely
the original complex window-packet phase, pointwise in each axis. -/
noncomputable def thirdFullSectorRealWindowGerm244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a ξ : Freq244) : Freq244 :=
  fun d =>
    (thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ *
      thirdFullFixedCenterTransverseGerm244
        (thirdFullAxisSixCenter244 i) ξ a d

/-- Exact real-germ representation of each preexisting complex window.
The equality holds globally, not only at its center. -/
theorem thirdFullAxisComplexWindowPacket_real_germ_phase244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6)
    (a : Freq244) (α : ℂ) (ξ : Freq244) :
    thirdFullAxisComplexWindowPacket244 ρ hρ i a α ξ =
      fun d => (thirdFullSectorRealWindowGerm244 ρ hρ i a ξ d : ℂ) * α := by
  funext d
  unfold thirdFullAxisComplexWindowPacket244 thirdFullSectorRealWindowGerm244
  push_cast; ring

/-- The real 3+2+2 coefficient that survives the precise cubic I phase.
The dot products are exactly those in `complexCoefficient` and
`amplitudeDot`, evaluated at the three separate moving transverse germs.
No artificial conjugation or six-permutation symmetrization is inserted. -/
noncomputable def thirdFullPositiveSectorInterpolationReal244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (n : Fin 6) (z : PairV244) : ℝ :=
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  let gp := thirdFullSectorRealWindowGerm244 ρ hρ labels.1
    (thirdFullPositiveWindowPolarization244 A B C labels.1) p
  let gq := thirdFullSectorRealWindowGerm244 ρ hρ middle
    (thirdFullPositiveWindowPolarization244 A B C middle) q
  let gr := thirdFullSectorRealWindowGerm244 ρ hρ labels.2
    (thirdFullPositiveWindowPolarization244 A B C labels.2) r
  dot p r * (dot p q) ^ 2 * dot r gq * dot gp gr

/-- On a positive coherent sector with actual nonzero Fourier triple mass,
the TRUE physical 3+2+2 interpolation kernel has phase I times the exact
real frequency/moving-polarization coefficient above. -/
theorem thirdFullPositiveSector_interpolation_eq_real_mul_I244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z =
      (thirdFullPositiveSectorInterpolationReal244 ρ hρ A B C n z : ℂ) *
        Complex.I := by
  let p : Freq244 := WithLp.ofLp z.1
  let r : Freq244 := WithLp.ofLp z.2
  let q : Freq244 := thirdFullMiddleFrequency244 (p, r)
  let labels := lowNormalQuarterCoherentLabelPair false n
  let middle := thirdFullPositiveMiddleLabel244 n
  let gp := thirdFullSectorRealWindowGerm244 ρ hρ labels.1
    (thirdFullPositiveWindowPolarization244 A B C labels.1) p
  let gq := thirdFullSectorRealWindowGerm244 ρ hρ middle
    (thirdFullPositiveWindowPolarization244 A B C middle) q
  let gr := thirdFullSectorRealWindowGerm244 ρ hρ labels.2
    (thirdFullPositiveWindowPolarization244 A B C labels.2) r
  have hIsolated := thirdFullPositiveSector_actual_interpolation244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass
  dsimp only at hIsolated
  rw [hIsolated]
  simp only [thirdFullAxisComplexWindowPacket_real_germ_phase244]
  change complexCoefficient p q r
      (fun d => (gq d : ℂ) * thirdFullPositiveWindowPhase244 middle) *
    amplitudeDot
      (fun d => (gp d : ℂ) * thirdFullPositiveWindowPhase244 labels.1)
      (fun d => (gr d : ℂ) * thirdFullPositiveWindowPhase244 labels.2) =
    ((dot p r * (dot p q) ^ 2 * dot r gq * dot gp gr : ℝ) : ℂ) *
      Complex.I
  rw [thirdFullSectorInterpolation_real_phase244]
  rw [thirdFullPositiveSector_phase_product244 n]

/-- The true interpolation coefficient has no real part on a positive
coherent sector. This is a consequence of the actual recovered spectrum,
not a sign assumption on an auxiliary polynomial. -/
theorem thirdFullPositiveSector_interpolation_re_zero244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    (thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z).re = 0 := by
  rw [thirdFullPositiveSector_interpolation_eq_real_mul_I244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass]
  simp [Complex.mul_re]

/-- The imaginary interpolation density, for the actual physical Schwartz
velocity, is exactly the real moving-polarization polynomial. -/
theorem thirdFullPositiveSector_interpolation_imag244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    (thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z).im =
      thirdFullPositiveSectorInterpolationReal244 ρ hρ A B C n z := by
  rw [thirdFullPositiveSector_interpolation_eq_real_mul_I244
    ρ hρ hSmall δ hDisj A B C n z hSector hMass]
  simp [Complex.mul_im]

/-- The COMPLETE original unphased physical seven-derivative kernel on a
nonzero positive sector is exactly the five-index gradient imaginary part
plus SIX times the real interpolation polynomial. This is the direct
handoff to the final sign comparison, with no cancellation assumed away. -/
theorem thirdFullPositiveSector_full_imag_eq_gradient_plus_interpolation244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (δ : ℝ) (hDisj : 2 * δ ≤ 1)
    (A B C : Freq244) (n : Fin 6) (z : PairV244)
    (hSector : z ∈ thirdFullHilbertCoherentSector244 (false, n) δ)
    (hMass : thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C
      (WithLp.ofLp z.1, WithLp.ofLp z.2) ≠ 0) :
    (thirdFullAxisRealThirdUnphasedKernel244 ρ hρ A B C z).im =
      (thirdFullAxisRealGradientTotalUnphased244 ρ hρ A B C z).im +
        6 * thirdFullPositiveSectorInterpolationReal244 ρ hρ A B C n z := by
  change (thirdFullAxisRealGradientTotalUnphased244 ρ hρ A B C z +
    6 * thirdFullAxisRealInterpolationKernel244 ρ hρ A B C z).im = _
  rw [Complex.add_im, Complex.mul_im,
    thirdFullPositiveSector_interpolation_imag244
      ρ hρ hSmall δ hDisj A B C n z hSector hMass]
  norm_num

end
end PrimeTensor.FirstMonomialTriad
