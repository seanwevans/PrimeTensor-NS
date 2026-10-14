import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterReflectedSector

/-!
# All twelve coherent first-monomial Schwartz triad sectors

The complete six-order coefficient is invariant under permutations of its
three (frequency, polarization) pairs. The corresponding signed kernel on
the momentum plane is invariant under both exchange of the outer variables
and the cyclic change `(p,r) ↦ (-(p+r),p)`.

At quarter scale, this transports the already proved value `9/64` from
one resonant pair to all six positive permutations and, by the established
Hermitian reflection identity, all six reflected permutations. Every one of
these twelve indexed resonant pairs admits a compact positive-volume ball
on which the signed six-order kernel has strictly positive integral.

Important: positivity on twelve *small neighborhoods* does not imply that
the integral over the entire six-packet support is positive. A full global
noncancellation result needs a uniform sign or an explicit bound on the
remaining within-packet contributions. No such result is asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter
open scoped Topology SchwartzMap

noncomputable section

private abbrev SectorV := Fin 3 → ℝ
private abbrev SectorPair := SectorV × SectorV

/-- The complete six-order coefficient is invariant under exchanging the
first and third frequency-polarization pairs. -/
theorem sixOrderTriadCoefficient_swap_outer
    (p q r : SectorV) (a b c : Fin 3 → ℂ) :
    sixOrderTriadCoefficient r q p c b a =
      sixOrderTriadCoefficient p q r a b c := by
  simp only [sixOrderTriadCoefficient]
  abel

/-- The complete six-order coefficient is invariant under the cyclic
rotation `(p,q,r) ↦ (q,r,p)`, with polarizations rotated as well. -/
theorem sixOrderTriadCoefficient_cycle
    (p q r : SectorV) (a b c : Fin 3 → ℂ) :
    sixOrderTriadCoefficient q r p b c a =
      sixOrderTriadCoefficient p q r a b c := by
  simp only [sixOrderTriadCoefficient]
  abel

/-- Exchanging the two independent momentum variables does not change the
signed six-order Schwartz kernel. No divergence hypothesis is required. -/
theorem lowNormalQuarterSignedKernel_swap (p r : SectorV) :
    lowNormalQuarterSignedKernel (r, p) =
      lowNormalQuarterSignedKernel (p, r) := by
  change
    (Complex.I * sixOrderTriadCoefficient r (middleFrequency r p) p
      (lowNormalQuarterSchwartz r)
      (lowNormalQuarterSchwartz (middleFrequency r p))
      (lowNormalQuarterSchwartz p)).re =
    (Complex.I * sixOrderTriadCoefficient p (middleFrequency p r) r
      (lowNormalQuarterSchwartz p)
      (lowNormalQuarterSchwartz (middleFrequency p r))
      (lowNormalQuarterSchwartz r)).re
  rw [middleFrequency_swap p r]
  rw [sixOrderTriadCoefficient_swap_outer]

/-- The true cyclic reindexing `(p,r) ↦ (q,p)` with `q=-(p+r)`
represents `(p,q,r) ↦ (q,r,p)` and preserves the signed kernel. -/
theorem lowNormalQuarterSignedKernel_cycle (p r : SectorV) :
    lowNormalQuarterSignedKernel (middleFrequency p r, p) =
      lowNormalQuarterSignedKernel (p, r) := by
  have hMiddle : middleFrequency (middleFrequency p r) p = r := by
    funext d
    simp only [middleFrequency]
    ring
  change
    (Complex.I * sixOrderTriadCoefficient (middleFrequency p r)
      (middleFrequency (middleFrequency p r) p) p
      (lowNormalQuarterSchwartz (middleFrequency p r))
      (lowNormalQuarterSchwartz (middleFrequency (middleFrequency p r) p))
      (lowNormalQuarterSchwartz p)).re =
    (Complex.I * sixOrderTriadCoefficient p (middleFrequency p r) r
      (lowNormalQuarterSchwartz p)
      (lowNormalQuarterSchwartz (middleFrequency p r))
      (lowNormalQuarterSchwartz r)).re
  rw [hMiddle]
  rw [sixOrderTriadCoefficient_cycle]

/-- At the sharp quarter scale, the middle frequency of `(P,R)` is Q. -/
private theorem lowNormalQuarterMiddle :
    middleFrequency lowNormalAuditP (lowNormalAuditR (1 / 4 : ℝ)) =
      lowNormalAuditQ (1 / 4 : ℝ) := by
  funext d
  have hm := lowNormalAudit_momentum (1 / 4 : ℝ) d
  dsimp [middleFrequency]
  linarith

/-- Ordered representatives of the six positive frequency-pair sectors:
(P,R), (R,P), (Q,R), (R,Q), (Q,P), and (P,Q). -/
def lowNormalQuarterPositivePair (k : Fin 6) : SectorPair :=
  match k.val with
  | 0 => (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ))
  | 1 => (lowNormalAuditR (1 / 4 : ℝ), lowNormalAuditP)
  | 2 => (lowNormalAuditQ (1 / 4 : ℝ), lowNormalAuditR (1 / 4 : ℝ))
  | 3 => (lowNormalAuditR (1 / 4 : ℝ), lowNormalAuditQ (1 / 4 : ℝ))
  | 4 => (lowNormalAuditQ (1 / 4 : ℝ), lowNormalAuditP)
  | _ => (lowNormalAuditP, lowNormalAuditQ (1 / 4 : ℝ))

/-- Each of the six positive permutations has the same exactly positive
signed value `9/64`. The result is independent of the cutoff shape. -/
theorem lowNormalQuarterPositivePair_value (k : Fin 6) :
    lowNormalQuarterSignedKernel (lowNormalQuarterPositivePair k) =
      9 / 64 := by
  let p := lowNormalAuditP
  let r := lowNormalAuditR (1 / 4 : ℝ)
  let q := lowNormalAuditQ (1 / 4 : ℝ)
  have hPR : lowNormalQuarterSignedKernel (p, r) = 9 / 64 :=
    lowNormalQuarterSignedKernel_at_center
  have hRP : lowNormalQuarterSignedKernel (r, p) = 9 / 64 :=
    (lowNormalQuarterSignedKernel_swap p r).trans hPR
  have hQpr : middleFrequency p r = q := lowNormalQuarterMiddle
  have hQswap : middleFrequency r p = q :=
    (middleFrequency_swap p r).trans hQpr
  have hQP : lowNormalQuarterSignedKernel (q, p) = 9 / 64 := by
    calc
      lowNormalQuarterSignedKernel (q, p) =
          lowNormalQuarterSignedKernel (middleFrequency p r, p) :=
        congrArg (fun v : SectorV => lowNormalQuarterSignedKernel (v, p)) hQpr.symm
      _ = lowNormalQuarterSignedKernel (p, r) :=
        lowNormalQuarterSignedKernel_cycle p r
      _ = 9 / 64 := hPR
  have hPQ : lowNormalQuarterSignedKernel (p, q) = 9 / 64 :=
    (lowNormalQuarterSignedKernel_swap q p).trans hQP
  have hQR : lowNormalQuarterSignedKernel (q, r) = 9 / 64 := by
    calc
      lowNormalQuarterSignedKernel (q, r) =
          lowNormalQuarterSignedKernel (middleFrequency r p, r) :=
        congrArg (fun v : SectorV => lowNormalQuarterSignedKernel (v, r)) hQswap.symm
      _ = lowNormalQuarterSignedKernel (r, p) :=
        lowNormalQuarterSignedKernel_cycle r p
      _ = 9 / 64 := hRP
  have hRQ : lowNormalQuarterSignedKernel (r, q) = 9 / 64 :=
    (lowNormalQuarterSignedKernel_swap q r).trans hQR
  fin_cases k
  · simpa [lowNormalQuarterPositivePair, p, r] using hPR
  · simpa [lowNormalQuarterPositivePair, p, r] using hRP
  · simpa [lowNormalQuarterPositivePair, q, r] using hQR
  · simpa [lowNormalQuarterPositivePair, q, r] using hRQ
  · simpa [lowNormalQuarterPositivePair, q, p] using hQP
  · simpa [lowNormalQuarterPositivePair, p, q] using hPQ

/-- A Boolean flag chooses between a coherent positive permutation and
its Hermitian-reflected negative counterpart. -/
def lowNormalQuarterCoherentPair (reflected : Bool) (k : Fin 6) : SectorPair :=
  if reflected then
    (-(lowNormalQuarterPositivePair k).1,
     -(lowNormalQuarterPositivePair k).2)
  else
    lowNormalQuarterPositivePair k

/-- The full twelve-point resonant orbit has one and the same signed value. -/
theorem lowNormalQuarterCoherentPair_value (reflected : Bool) (k : Fin 6) :
    lowNormalQuarterSignedKernel (lowNormalQuarterCoherentPair reflected k) =
      9 / 64 := by
  cases reflected with
  | false =>
      exact lowNormalQuarterPositivePair_value k
  | true =>
      change lowNormalQuarterSignedKernel
        (-(lowNormalQuarterPositivePair k).1,
         -(lowNormalQuarterPositivePair k).2) = 9 / 64
      rw [lowNormalQuarterSignedKernel_reflect]
      exact lowNormalQuarterPositivePair_value k

/-- A positive center of the continuous signed kernel has a compact ball
with a strictly positive *set integral*. This is an analytic result for
this actual fixed Schwartz field, not a global-support statement. -/
theorem lowNormalQuarterSignedKernel_positive_local_integral_at
    (center : SectorPair) (hCenter : 0 < lowNormalQuarterSignedKernel center) :
    ∃ radius : ℝ, 0 < radius ∧
      0 < ∫ z in Metric.closedBall center radius,
        lowNormalQuarterSignedKernel z ∂(volume.prod volume) := by
  have hOpen : IsOpen {z : SectorPair | 0 < lowNormalQuarterSignedKernel z} :=
    isOpen_lt continuous_const lowNormalQuarterSignedKernel_continuous
  have hEvent : ∀ᶠ z in 𝓝 center, 0 < lowNormalQuarterSignedKernel z :=
    hOpen.mem_nhds hCenter
  obtain ⟨ε, hε, hSub⟩ := Metric.mem_nhds_iff.mp hEvent
  let radius : ℝ := ε / 2
  have hr : 0 < radius := half_pos hε
  let s : Set SectorPair := Metric.closedBall center radius
  have hPos : ∀ z ∈ s, 0 < lowNormalQuarterSignedKernel z := by
    intro z hz
    exact hSub ((Metric.closedBall_subset_ball (half_lt_self hε)) hz)
  have hCompact : IsCompact s := isCompact_closedBall _ _
  have hMeas : MeasurableSet s := measurableSet_closedBall
  have hInt : IntegrableOn lowNormalQuarterSignedKernel s
      (volume.prod volume) :=
    lowNormalQuarterSignedKernel_continuous.continuousOn.integrableOn_compact
      hCompact
  have hNonneg :
      0 ≤ᵐ[(volume.prod volume).restrict s] lowNormalQuarterSignedKernel := by
    filter_upwards [ae_restrict_mem hMeas] with z hz
    exact (hPos z hz).le
  have hBallSubset :
      Metric.ball center radius ⊆
        Function.support lowNormalQuarterSignedKernel ∩ s := by
    intro z hz
    constructor
    · change lowNormalQuarterSignedKernel z ≠ 0
      exact ne_of_gt (hPos z (Metric.ball_subset_closedBall hz))
    · exact Metric.ball_subset_closedBall hz
  have hMeasure :
      0 < (volume.prod volume)
        (Function.support lowNormalQuarterSignedKernel ∩ s) := by
    exact (Metric.measure_ball_pos (volume.prod volume) center hr).trans_le
      (measure_mono hBallSubset)
  refine ⟨radius, hr, ?_⟩
  change 0 < ∫ z in s, lowNormalQuarterSignedKernel z ∂(volume.prod volume)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure

/-- All twelve coherent indexed frequency-pair sectors have strictly
positive *localized* signed integrals. The radius may depend on the sector. -/
theorem lowNormalQuarterCoherentPair_positive_local_integral
    (reflected : Bool) (k : Fin 6) :
    ∃ radius : ℝ, 0 < radius ∧
      0 < ∫ z in Metric.closedBall (lowNormalQuarterCoherentPair reflected k) radius,
        lowNormalQuarterSignedKernel z ∂(volume.prod volume) := by
  apply lowNormalQuarterSignedKernel_positive_local_integral_at
  rw [lowNormalQuarterCoherentPair_value]
  norm_num

end
end PrimeTensor.FirstMonomialTriad
