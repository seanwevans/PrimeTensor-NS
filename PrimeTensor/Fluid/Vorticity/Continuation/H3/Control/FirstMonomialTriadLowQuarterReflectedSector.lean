import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterLocalIntegral

/-!
# Reality reflection reinforces the signed sharp low-normal sector

The preceding local integral proof controlled only a neighborhood of the
positive resonant pair. This module establishes a global *pointwise* symmetry
of the genuine six-packet Schwartz kernel under simultaneous negation of
both independent Fourier frequencies.

For real frequencies and conjugated amplitudes the ordered trilinear symbol
changes to minus its complex conjugate. The seven-derivative odd-frequency
structure is responsible for the minus sign. Consequently `Re (I * C₆)` is
even under reflection, and the negative resonant sector has the same strictly
positive central value, 9/64. There is a positive localized integral about
the reflected center as well.

This proves reinforcement of the two opposite sectors. It does NOT prove
that the full, unlocalized six-packet integral is nonzero: the other coherent
permutations and possible off-center sign variations remain to be controlled.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter
open scoped Topology SchwartzMap

noncomputable section

private abbrev ReflectV := Fin 3 → ℝ
private abbrev ReflectPair := ReflectV × ReflectV

/-- Negating both real frequencies preserves their Euclidean contraction. -/
private theorem lowNormalReflect_dot (p r : ReflectV) :
    dot (-p) (-r) = dot p r := by
  simp [dot, Fin.sum_univ_succ, Pi.neg_apply]

/-- One real-frequency/complex-amplitude contraction is odd under
frequency reflection and conjugate under amplitude reflection. -/
private theorem lowNormalReflect_mixedDot
    (r : ReflectV) (b : Fin 3 → ℂ) :
    mixedDot (-r) (fun d => star (b d)) =
      -star (mixedDot r b) := by
  change mixedDot (-r) (fun d => (starRingEnd ℂ) (b d)) =
    -(starRingEnd ℂ) (mixedDot r b)
  simp [mixedDot, Fin.sum_univ_succ, Pi.neg_apply,
    map_add, map_mul, Complex.conj_ofReal]

/-- The scalar ordered coefficient is odd and conjugate under total reflection. -/
private theorem lowNormalReflect_complexCoefficient
    (p q r : ReflectV) (b : Fin 3 → ℂ) :
    complexCoefficient (-p) (-q) (-r) (fun d => star (b d)) =
      -star (complexCoefficient p q r b) := by
  unfold complexCoefficient
  rw [lowNormalReflect_dot p r, lowNormalReflect_dot p q,
    lowNormalReflect_mixedDot r b]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

/-- Bilinear amplitude contraction commutes with coordinatewise conjugation. -/
private theorem lowNormalReflect_amplitudeDot
    (a c : Fin 3 → ℂ) :
    amplitudeDot (fun d => star (a d)) (fun d => star (c d)) =
      star (amplitudeDot a c) := by
  change amplitudeDot (fun d => (starRingEnd ℂ) (a d))
      (fun d => (starRingEnd ℂ) (c d)) =
    (starRingEnd ℂ) (amplitudeDot a c)
  simp [amplitudeDot, Fin.sum_univ_succ, map_add, map_mul]

/-- One of the six ordered contributions is odd-conjugate under reflection. -/
private theorem lowNormalReflect_ordered
    (p q r : ReflectV) (a b c : Fin 3 → ℂ) :
    orderedTriadCoefficient (-p) (-q) (-r)
        (fun d => star (a d)) (fun d => star (b d))
        (fun d => star (c d)) =
      -star (orderedTriadCoefficient p q r a b c) := by
  change
    complexCoefficient (-p) (-q) (-r) (fun d => star (b d)) *
      amplitudeDot (fun d => star (a d)) (fun d => star (c d)) =
    -(starRingEnd ℂ) (complexCoefficient p q r b * amplitudeDot a c)
  rw [lowNormalReflect_complexCoefficient, lowNormalReflect_amplitudeDot]
  simp only [map_mul, starRingEnd_apply]
  exact neg_mul _ _

/-- All six ordered terms retain the same odd-conjugate parity. This is
an exact trilinear identity, independent of any integrability assumption. -/
theorem lowNormalReflect_sixOrder
    (p q r : ReflectV) (a b c : Fin 3 → ℂ) :
    sixOrderTriadCoefficient (-p) (-q) (-r)
        (fun d => star (a d)) (fun d => star (b d))
        (fun d => star (c d)) =
      -star (sixOrderTriadCoefficient p q r a b c) := by
  change
    orderedTriadCoefficient (-p) (-q) (-r) (fun d => star (a d))
        (fun d => star (b d)) (fun d => star (c d)) +
      orderedTriadCoefficient (-p) (-r) (-q) (fun d => star (a d))
        (fun d => star (c d)) (fun d => star (b d)) +
      orderedTriadCoefficient (-q) (-p) (-r) (fun d => star (b d))
        (fun d => star (a d)) (fun d => star (c d)) +
      orderedTriadCoefficient (-q) (-r) (-p) (fun d => star (b d))
        (fun d => star (c d)) (fun d => star (a d)) +
      orderedTriadCoefficient (-r) (-p) (-q) (fun d => star (c d))
        (fun d => star (a d)) (fun d => star (b d)) +
      orderedTriadCoefficient (-r) (-q) (-p) (fun d => star (c d))
        (fun d => star (b d)) (fun d => star (a d)) =
      -(starRingEnd ℂ) (sixOrderTriadCoefficient p q r a b c)
  rw [lowNormalReflect_ordered, lowNormalReflect_ordered,
    lowNormalReflect_ordered, lowNormalReflect_ordered,
    lowNormalReflect_ordered, lowNormalReflect_ordered]
  simp only [sixOrderTriadCoefficient, map_add, starRingEnd_apply]
  abel

private theorem lowNormalQuarterSchwartz_reality' (ξ : ReflectV) :
    lowNormalQuarterSchwartz (-ξ) =
      (fun d => star (lowNormalQuarterSchwartz ξ d)) := by
  exact lowNormalSmoothSixPacketSchwartz_reality
    (1 / 4 : ℝ) (by norm_num) ξ

/-- The odd phase `I` turns `-conj(C)` into the same signed real number. -/
private theorem lowNormalReflect_signed_re (w : ℂ) :
    (Complex.I * (-star w)).re = (Complex.I * w).re := by
  simp [Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.conj_im]

/-- Reflection preserves the momentum constraint q = -(p+r). -/
private theorem lowNormalReflect_middleFrequency (p r : ReflectV) :
    middleFrequency (-p) (-r) = -(middleFrequency p r) := by
  funext d
  simp [middleFrequency, Pi.neg_apply]
  ring

/-- **Exact evenness of the signed kernel on the entire frequency-pair
space.** In particular, the reflected triad is not an opposite-sign sector. -/
theorem lowNormalQuarterSignedKernel_reflect (z : ReflectPair) :
    lowNormalQuarterSignedKernel (-z.1, -z.2) =
      lowNormalQuarterSignedKernel z := by
  rcases z with ⟨p, r⟩
  change
    (Complex.I * sixOrderTriadCoefficient (-p)
      (middleFrequency (-p) (-r)) (-r)
      (lowNormalQuarterSchwartz (-p))
      (lowNormalQuarterSchwartz (middleFrequency (-p) (-r)))
      (lowNormalQuarterSchwartz (-r))).re =
    (Complex.I * sixOrderTriadCoefficient p (middleFrequency p r) r
      (lowNormalQuarterSchwartz p)
      (lowNormalQuarterSchwartz (middleFrequency p r))
      (lowNormalQuarterSchwartz r)).re
  rw [lowNormalReflect_middleFrequency,
    lowNormalQuarterSchwartz_reality',
    lowNormalQuarterSchwartz_reality',
    lowNormalQuarterSchwartz_reality',
    lowNormalReflect_sixOrder]
  exact lowNormalReflect_signed_re _

/-- The negatively oriented resonant pair. -/
def lowNormalQuarterReflectedResonantPair : ReflectPair :=
  (-lowNormalAuditP, -lowNormalAuditR (1 / 4 : ℝ))

/-- Reflection gives the same exact positive value 9/64, not its negative. -/
theorem lowNormalQuarterSignedKernel_at_reflected_center :
    lowNormalQuarterSignedKernel lowNormalQuarterReflectedResonantPair =
      9 / 64 := by
  change lowNormalQuarterSignedKernel
    (-lowNormalAuditP, -lowNormalAuditR (1 / 4 : ℝ)) = 9 / 64
  have hReflect := lowNormalQuarterSignedKernel_reflect
    (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ))
  rw [hReflect]
  exact lowNormalQuarterSignedKernel_at_center

/-- Positivity persists around the reflected resonant pair as well. -/
theorem lowNormalQuarterSignedKernel_reflected_eventually_positive :
    ∀ᶠ z : ReflectPair in 𝓝 lowNormalQuarterReflectedResonantPair,
      0 < lowNormalQuarterSignedKernel z := by
  have hOpen : IsOpen {z : ReflectPair | 0 < lowNormalQuarterSignedKernel z} :=
    isOpen_lt continuous_const lowNormalQuarterSignedKernel_continuous
  apply hOpen.mem_nhds
  change 0 < lowNormalQuarterSignedKernel lowNormalQuarterReflectedResonantPair
  rw [lowNormalQuarterSignedKernel_at_reflected_center]
  norm_num

/-- A compact positive neighborhood around the reflected frequency pair. -/
theorem lowNormalQuarterSignedKernel_reflected_exists_positive_closedBall :
    ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ Metric.closedBall lowNormalQuarterReflectedResonantPair r,
        0 < lowNormalQuarterSignedKernel z := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
    lowNormalQuarterSignedKernel_reflected_eventually_positive
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  exact hsub ((Metric.closedBall_subset_ball (half_lt_self hε)) hz)

/-- Signed integral localized at the reflected, negatively oriented triad. -/
noncomputable def lowNormalQuarterReflectedLocalizedSignedIntegral (r : ℝ) : ℝ :=
  ∫ z in Metric.closedBall lowNormalQuarterReflectedResonantPair r,
    lowNormalQuarterSignedKernel z ∂(volume.prod volume)

/-- **Both orientation classes contain a positive-measure, positive signed
contribution.** Global noncancellation is not asserted. -/
theorem lowNormalQuarterReflectedLocalizedSignedIntegral_exists_pos :
    ∃ r : ℝ, 0 < r ∧ 0 < lowNormalQuarterReflectedLocalizedSignedIntegral r := by
  obtain ⟨r, hr, hpos⟩ :=
    lowNormalQuarterSignedKernel_reflected_exists_positive_closedBall
  let s : Set ReflectPair :=
    Metric.closedBall lowNormalQuarterReflectedResonantPair r
  have hCompact : IsCompact s := isCompact_closedBall _ _
  have hMeas : MeasurableSet s := measurableSet_closedBall
  have hInt : IntegrableOn lowNormalQuarterSignedKernel s
      (volume.prod volume) :=
    lowNormalQuarterSignedKernel_continuous.continuousOn.integrableOn_compact
      hCompact
  have hNonneg :
      0 ≤ᵐ[(volume.prod volume).restrict s] lowNormalQuarterSignedKernel := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact (hpos z hz).le
  have hBallSubset :
      Metric.ball lowNormalQuarterReflectedResonantPair r ⊆
        Function.support lowNormalQuarterSignedKernel ∩ s := by
    intro z hz
    constructor
    · change lowNormalQuarterSignedKernel z ≠ 0
      exact ne_of_gt (hpos z (Metric.ball_subset_closedBall hz))
    · exact Metric.ball_subset_closedBall hz
  have hMeasure :
      0 < (volume.prod volume)
        (Function.support lowNormalQuarterSignedKernel ∩ s) := by
    exact (Metric.measure_ball_pos (volume.prod volume)
      lowNormalQuarterReflectedResonantPair hr).trans_le
        (measure_mono hBallSubset)
  refine ⟨r, hr, ?_⟩
  change 0 < ∫ z in s, lowNormalQuarterSignedKernel z ∂(volume.prod volume)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure

/-- The positive and reflected oriented sectors each have a strictly
positive compact-neighborhood integral, potentially at different radii. -/
theorem lowNormalQuarterBothOrientations_exist_positive_localized_integrals :
    (∃ r : ℝ, 0 < r ∧ 0 < lowNormalQuarterLocalizedSignedIntegral r) ∧
    (∃ r : ℝ, 0 < r ∧ 0 < lowNormalQuarterReflectedLocalizedSignedIntegral r) :=
  ⟨lowNormalQuarterLocalizedSignedIntegral_exists_pos,
    lowNormalQuarterReflectedLocalizedSignedIntegral_exists_pos⟩

end
end PrimeTensor.FirstMonomialTriad
