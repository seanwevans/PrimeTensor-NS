import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterCenter

/-!
# An open signed triad neighborhood for the genuine sharp Schwartz field

The already proved six-order coefficient is nonzero at the sharp frequency
triad p+q+r=0, with t=1/4.  A pointwise nonzero value does not establish a
nonzero frequency integral.  Here we prove something intermediate but crucial:
for the *actual fixed Schwartz field* the phase-adjusted signed six-order
kernel depends continuously on the two independent Fourier frequencies.
It is strictly positive at (p,r), and hence strictly positive throughout
an open neighborhood of (p,r).

The factor I is used to extract the imaginary part of the six-order symbol,
not the physical seven-derivative phase (which has the opposite sign).
No claim of a nonzero full-space integral is made in this file.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
open scoped Topology SchwartzMap

noncomputable section

private theorem continuous_dot_of_continuous
    {X : Type*} [TopologicalSpace X]
    (p q : X → Fin 3 → ℝ) (hp : Continuous p) (hq : Continuous q) :
    Continuous (fun x => dot (p x) (q x)) := by
  have hc (d : Fin 3) :
      Continuous (fun x => p x d * q x d) :=
    ((continuous_apply d).comp hp).mul ((continuous_apply d).comp hq)
  change Continuous (fun x => ∑ d : Fin 3, p x d * q x d)
  exact continuous_finsetSum Finset.univ (by
    intro d _
    exact hc d)

private theorem continuous_mixedDot_of_continuous
    {X : Type*} [TopologicalSpace X]
    (p : X → Fin 3 → ℝ) (b : X → Fin 3 → ℂ)
    (hp : Continuous p) (hb : Continuous b) :
    Continuous (fun x => mixedDot (p x) (b x)) := by
  have hc (d : Fin 3) :
      Continuous (fun x => (p x d : ℂ) * b x d) :=
    (Complex.ofRealCLM.continuous.comp ((continuous_apply d).comp hp)).mul
      ((continuous_apply d).comp hb)
  change Continuous (fun x => ∑ d : Fin 3, (p x d : ℂ) * b x d)
  exact continuous_finsetSum Finset.univ (by
    intro d _
    exact hc d)

private theorem continuous_amplitudeDot_of_continuous
    {X : Type*} [TopologicalSpace X]
    (a c : X → Fin 3 → ℂ) (ha : Continuous a) (hc : Continuous c) :
    Continuous (fun x => amplitudeDot (a x) (c x)) := by
  have hd (d : Fin 3) :
      Continuous (fun x => a x d * c x d) :=
    ((continuous_apply d).comp ha).mul ((continuous_apply d).comp hc)
  change Continuous (fun x => ∑ d : Fin 3, a x d * c x d)
  exact continuous_finsetSum Finset.univ (by
    intro d _
    exact hd d)

private theorem continuous_complexCoefficient_of_continuous
    {X : Type*} [TopologicalSpace X]
    (p q r : X → Fin 3 → ℝ) (b : X → Fin 3 → ℂ)
    (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    (hb : Continuous b) :
    Continuous (fun x => complexCoefficient (p x) (q x) (r x) (b x)) := by
  change Continuous (fun x =>
    ((dot (p x) (r x) * (dot (p x) (q x)) ^ 2 : ℝ) : ℂ) *
       mixedDot (r x) (b x))
  exact (Complex.ofRealCLM.continuous.comp
      ((continuous_dot_of_continuous p r hp hr).mul
        ((continuous_dot_of_continuous p q hp hq).pow 2))).mul
    (continuous_mixedDot_of_continuous r b hr hb)

private theorem continuous_orderedTriadCoefficient_of_continuous
    {X : Type*} [TopologicalSpace X]
    (p q r : X → Fin 3 → ℝ) (a b c : X → Fin 3 → ℂ)
    (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => orderedTriadCoefficient (p x) (q x) (r x)
      (a x) (b x) (c x)) := by
  change Continuous (fun x =>
    complexCoefficient (p x) (q x) (r x) (b x) * amplitudeDot (a x) (c x))
  exact (continuous_complexCoefficient_of_continuous p q r b hp hq hr hb).mul
    (continuous_amplitudeDot_of_continuous a c ha hc)

private theorem continuous_sixOrderTriadCoefficient_of_continuous
    {X : Type*} [TopologicalSpace X]
    (p q r : X → Fin 3 → ℝ) (a b c : X → Fin 3 → ℂ)
    (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => sixOrderTriadCoefficient (p x) (q x) (r x)
      (a x) (b x) (c x)) := by
  have h1 := continuous_orderedTriadCoefficient_of_continuous
    p q r a b c hp hq hr ha hb hc
  have h2 := continuous_orderedTriadCoefficient_of_continuous
    p r q a c b hp hr hq ha hc hb
  have h3 := continuous_orderedTriadCoefficient_of_continuous
    q p r b a c hq hp hr hb ha hc
  have h4 := continuous_orderedTriadCoefficient_of_continuous
    q r p b c a hq hr hp hb hc ha
  have h5 := continuous_orderedTriadCoefficient_of_continuous
    r p q c a b hr hp hq hc ha hb
  have h6 := continuous_orderedTriadCoefficient_of_continuous
    r q p c b a hr hq hp hc hb ha
  have hsum := ((((h1.add h2).add h3).add h4).add h5).add h6
  -- A function-space sum and a pointwise sum are definitionally equal,
  -- but the simplifier does not rewrite an unapplied function sum.
  convert hsum using 1 <;> (funext x; rfl)

/-- Signed six-order symbol of the genuine quarter-scale Schwartz field,
restricted to the momentum plane q=-p-r. -/
def lowNormalQuarterSignedKernel
    (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  (Complex.I * sixOrderTriadCoefficient z.1 (middleFrequency z.1 z.2) z.2
    (lowNormalQuarterSchwartz z.1)
    (lowNormalQuarterSchwartz (middleFrequency z.1 z.2))
    (lowNormalQuarterSchwartz z.2)).re

/-- The signed kernel is continuous in both independent Fourier variables. -/
theorem lowNormalQuarterSignedKernel_continuous :
    Continuous lowNormalQuarterSignedKernel := by
  let V := Fin 3 → ℝ
  let Y := Fin 3 → ℂ
  have ht : (1 / 4 : ℝ) ≠ 0 := by norm_num
  have hU : Continuous (lowNormalQuarterSchwartz : V → Y) := by
    have hEq : (lowNormalQuarterSchwartz : V → Y) =
        lowNormalSmoothSixPacketFourier (1 / 4 : ℝ) ht := by
      funext ξ
      exact lowNormalSmoothSixPacketSchwartz_apply (1 / 4 : ℝ) ht ξ
    rw [hEq]
    exact (lowNormalSmoothSixPacketFourier_contDiff (1 / 4 : ℝ) ht).continuous
  have hp : Continuous (fun z : V × V => z.1) := continuous_fst
  have hr : Continuous (fun z : V × V => z.2) := continuous_snd
  have hq : Continuous (fun z : V × V => middleFrequency z.1 z.2) := by
    change Continuous (fun z : V × V => fun d : Fin 3 => -(z.1 d + z.2 d))
    apply continuous_pi
    intro d
    exact (((continuous_apply d).comp hp).add
      ((continuous_apply d).comp hr)).neg
  have ha : Continuous (fun z : V × V => lowNormalQuarterSchwartz z.1) :=
    hU.comp hp
  have hb : Continuous (fun z : V × V =>
      lowNormalQuarterSchwartz (middleFrequency z.1 z.2)) :=
    hU.comp hq
  have hc : Continuous (fun z : V × V => lowNormalQuarterSchwartz z.2) :=
    hU.comp hr
  have hSix := continuous_sixOrderTriadCoefficient_of_continuous
    (fun z : V × V => z.1)
    (fun z : V × V => middleFrequency z.1 z.2)
    (fun z : V × V => z.2)
    (fun z : V × V => lowNormalQuarterSchwartz z.1)
    (fun z : V × V => lowNormalQuarterSchwartz (middleFrequency z.1 z.2))
    (fun z : V × V => lowNormalQuarterSchwartz z.2)
    hp hq hr ha hb hc
  exact Complex.continuous_re.comp (continuous_const.mul hSix)

/-- The exact real signed value at the resonant center pair is 9/64. -/
theorem lowNormalQuarterSignedKernel_at_center :
    lowNormalQuarterSignedKernel
        (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ)) = 9 / 64 := by
  have hm : middleFrequency lowNormalAuditP (lowNormalAuditR (1 / 4 : ℝ)) =
      lowNormalAuditQ (1 / 4 : ℝ) := by
    funext d
    have h := lowNormalAudit_momentum (1 / 4 : ℝ) d
    dsimp [middleFrequency]
    linarith
  unfold lowNormalQuarterSignedKernel
  rw [hm, lowNormalQuarterSchwartz_sixOrder]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

/-- A strict sign on an *open frequency neighborhood*, not just at one
measure-zero resonant point. -/
theorem lowNormalQuarterSignedKernel_eventually_positive :
    ∀ᶠ z : (Fin 3 → ℝ) × (Fin 3 → ℝ) in
        𝓝 (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ)),
      0 < lowNormalQuarterSignedKernel z := by
  have hOpen : IsOpen {z : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      0 < lowNormalQuarterSignedKernel z} :=
    isOpen_lt continuous_const lowNormalQuarterSignedKernel_continuous
  apply hOpen.mem_nhds
  change 0 < lowNormalQuarterSignedKernel
    (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ))
  rw [lowNormalQuarterSignedKernel_at_center]
  norm_num

end
end PrimeTensor.FirstMonomialTriad
