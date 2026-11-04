import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPureSixthPowerFluxLimit
import Mathlib.Tactic

/-!
# Quantitative radial-shell gain for the pure solenoidal sixth-power H³ flux

The genuine solenoidal physical H³ transport has now been represented by the
uncorrected complex sixth-power triad flux. That representation retains three
radial differences rather than having a fixed sign. The present module shows
that these differences give a sharp linear gain in the squared-radius spread.

For three Fourier frequencies, write P=|p|², Q=|q|², R=|r|², S=max(P,Q,R)
and Δ=S-min(P,Q,R). Every complex polarization satisfies the pointwise bound

  |F₆(p,q,r; A,B,C)| ≤ 3 S² Δ (|X|+|Y|+|Z|),

where X, Y, Z are exactly the three existing complex polarization-frequency
contractions. Thus, on a common squared-radius annulus [lo,hi], S≤hi and
Δ≤hi-lo, making the gain 3 hi² (hi-lo). No real-polarization replacement,
nonzero-frequency division, or favorable sign is introduced. The bound is
pointwise: an integrated H³ improvement requires a corresponding spectral
localization or a controlled off-shell tail, not presumed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeSolenoidalRadialShell244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact real polynomial estimate behind the thin-shell gain.
It is uniform down to zero radius and has no negative-power singularity. -/
theorem thirdFull_realCubeGap_le_radiusSquare244
    (x y S : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hXS : x ≤ S) (hYS : y ≤ S) :
    |x ^ 3 - y ^ 3| ≤ (3 * S ^ 2) * |x - y| := by
  have hS : 0 ≤ S := le_trans hx hXS
  have hX2 : x ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hx hXS 2
  have hY2 : y ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hy hYS 2
  have hXY : x * y ≤ S ^ 2 := by
    calc
      x * y ≤ S * y := mul_le_mul_of_nonneg_right hXS hy
      _ ≤ S * S := mul_le_mul_of_nonneg_left hYS hS
      _ = S ^ 2 := by ring
  have hPoly : 0 ≤ x ^ 2 + x * y + y ^ 2 := by positivity
  have hPolyBound : x ^ 2 + x * y + y ^ 2 ≤ 3 * S ^ 2 := by
    nlinarith only [hX2, hY2, hXY]
  calc
    |x ^ 3 - y ^ 3| = |x - y| * (x ^ 2 + x * y + y ^ 2) := by
      rw [show x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) by ring,
        abs_mul, abs_of_nonneg hPoly]
    _ ≤ |x - y| * (3 * S ^ 2) :=
      mul_le_mul_of_nonneg_left hPolyBound (abs_nonneg _)
    _ = (3 * S ^ 2) * |x - y| := by ring

/-- Complex Fourier phases do not alter a real squared-radius cubic gap. -/
theorem thirdFull_complexCubeGap_norm244 (x y : ℝ) :
    ‖((x : ℂ) ^ 3 - (y : ℂ) ^ 3)‖ = |x ^ 3 - y ^ 3| := by
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

/-- Squared Euclidean radius is nonnegative on the actual three-axis carrier. -/
theorem thirdFull_axisSquareRadius_nonneg244 (p : A3 → ℝ) :
    0 ≤ thirdTriadAxisDot244 p p := by
  unfold thirdTriadAxisDot244
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg (p i)

/-- A universal elementary max/min radius identity: any two of three
squared radii differ by at most the full radial spread. -/
theorem thirdFull_threeRadius_pairwiseSpread244 (P Q R : ℝ) :
    |P - Q| ≤ max P (max Q R) - min P (min Q R) ∧
    |P - R| ≤ max P (max Q R) - min P (min Q R) ∧
    |Q - R| ≤ max P (max Q R) - min P (min Q R) := by
  let S : ℝ := max P (max Q R)
  let m : ℝ := min P (min Q R)
  have hPmax : P ≤ S := le_max_left _ _
  have hQmax : Q ≤ S := (le_max_left Q R).trans (le_max_right P (max Q R))
  have hRmax : R ≤ S := (le_max_right Q R).trans (le_max_right P (max Q R))
  have hPmin : m ≤ P := min_le_left _ _
  have hQmin : m ≤ Q := (min_le_right P (min Q R)).trans (min_le_left Q R)
  have hRmin : m ≤ R := (min_le_right P (min Q R)).trans (min_le_right Q R)
  change |P-Q| ≤ S-m ∧ |P-R| ≤ S-m ∧ |Q-R| ≤ S-m
  constructor
  · exact abs_le.mpr ⟨by linarith only [hPmin, hQmax],
      by linarith only [hQmin, hPmax]⟩
  constructor
  · exact abs_le.mpr ⟨by linarith only [hPmin, hRmax],
      by linarith only [hRmin, hPmax]⟩
  · exact abs_le.mpr ⟨by linarith only [hQmin, hRmax],
      by linarith only [hRmin, hQmax]⟩

/-- Largest of the three REAL squared Fourier radii. -/
noncomputable def thirdFullTriadSquareRadiusMax244
    (p q r : A3 → ℝ) : ℝ :=
  max (thirdTriadAxisDot244 p p)
    (max (thirdTriadAxisDot244 q q) (thirdTriadAxisDot244 r r))

/-- Exact nonnegative squared-radius spread (not a frequency norm ratio). -/
noncomputable def thirdFullTriadSquareRadiusSpread244
    (p q r : A3 → ℝ) : ℝ :=
  thirdFullTriadSquareRadiusMax244 p q r -
    min (thirdTriadAxisDot244 p p)
      (min (thirdTriadAxisDot244 q q) (thirdTriadAxisDot244 r r))

/-- The physical six-transfer contraction budget, retaining all complex
phases inside each coefficient and taking the norm only afterward. -/
noncomputable def thirdFullComplexSixthFluxContractionBudget244
    (_p q r : A3 → ℝ) (A B C : A3 → ℂ) : ℝ :=
  ‖thirdFullComplexPolarizationDot244 A C * mixedDot r B‖ +
  ‖thirdFullComplexPolarizationDot244 A B * mixedDot q C‖ +
  ‖thirdFullComplexPolarizationDot244 B C * mixedDot r A‖

/-- The exact complex sixth-power flux has a universal LINEAR radial-spread
gain. This works for arbitrary complex Fourier amplitudes; solenoidality is
used upstream to identify this flux with the physical H³ transport. -/
theorem thirdFullComplexSixthPowerFlux_radialSpread_le244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) :
    ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ ≤
      (3 * (thirdFullTriadSquareRadiusMax244 p q r) ^ 2 *
        thirdFullTriadSquareRadiusSpread244 p q r) *
        thirdFullComplexSixthFluxContractionBudget244 p q r A B C := by
  let P : ℝ := thirdTriadAxisDot244 p p
  let Q : ℝ := thirdTriadAxisDot244 q q
  let R : ℝ := thirdTriadAxisDot244 r r
  let S : ℝ := max P (max Q R)
  let m : ℝ := min P (min Q R)
  let Δ : ℝ := S - m
  have hP0 : 0 ≤ P := thirdFull_axisSquareRadius_nonneg244 p
  have hQ0 : 0 ≤ Q := thirdFull_axisSquareRadius_nonneg244 q
  have hR0 : 0 ≤ R := thirdFull_axisSquareRadius_nonneg244 r
  have hPS : P ≤ S := le_max_left _ _
  have hQS : Q ≤ S := (le_max_left Q R).trans (le_max_right P (max Q R))
  have hRS : R ≤ S := (le_max_right Q R).trans (le_max_right P (max Q R))
  have hS0 : 0 ≤ S := hP0.trans hPS
  have hPair := thirdFull_threeRadius_pairwiseSpread244 P Q R
  have hPR : |R - P| ≤ Δ := by
    simpa only [abs_sub_comm, Δ, S, m] using hPair.2.1
  have hPQ : |Q - P| ≤ Δ := by
    simpa only [abs_sub_comm, Δ, S, m] using hPair.1
  have hQR : |R - Q| ≤ Δ := by
    simpa only [abs_sub_comm, Δ, S, m] using hPair.2.2
  have hΔ0 : 0 ≤ Δ := by
    have hmin : m ≤ P := min_le_left _ _
    dsimp only [Δ]
    linarith only [hmin, hPS]
  let K : ℝ := 3 * S ^ 2 * Δ
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hRPcube : ‖((R : ℂ) ^ 3 - (P : ℂ) ^ 3)‖ ≤ K := by
    rw [thirdFull_complexCubeGap_norm244]
    exact (thirdFull_realCubeGap_le_radiusSquare244
      R P S hR0 hP0 hRS hPS).trans
        (mul_le_mul_of_nonneg_left hPR (by positivity))
  have hQPcube : ‖((Q : ℂ) ^ 3 - (P : ℂ) ^ 3)‖ ≤ K := by
    rw [thirdFull_complexCubeGap_norm244]
    exact (thirdFull_realCubeGap_le_radiusSquare244
      Q P S hQ0 hP0 hQS hPS).trans
        (mul_le_mul_of_nonneg_left hPQ (by positivity))
  have hRQcube : ‖((R : ℂ) ^ 3 - (Q : ℂ) ^ 3)‖ ≤ K := by
    rw [thirdFull_complexCubeGap_norm244]
    exact (thirdFull_realCubeGap_le_radiusSquare244
      R Q S hR0 hQ0 hRS hQS).trans
        (mul_le_mul_of_nonneg_left hQR (by positivity))
  let X : ℂ := thirdFullComplexPolarizationDot244 A C * mixedDot r B
  let Y : ℂ := thirdFullComplexPolarizationDot244 A B * mixedDot q C
  let Z : ℂ := thirdFullComplexPolarizationDot244 B C * mixedDot r A
  have hX : ‖X * ((R : ℂ) ^ 3 - (P : ℂ) ^ 3)‖ ≤ ‖X‖ * K := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hRPcube (norm_nonneg _)
  have hY : ‖Y * ((Q : ℂ) ^ 3 - (P : ℂ) ^ 3)‖ ≤ ‖Y‖ * K := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hQPcube (norm_nonneg _)
  have hZ : ‖Z * ((R : ℂ) ^ 3 - (Q : ℂ) ^ 3)‖ ≤ ‖Z‖ * K := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hRQcube (norm_nonneg _)
  change ‖X * ((R : ℂ) ^ 3 - (P : ℂ) ^ 3) +
      Y * ((Q : ℂ) ^ 3 - (P : ℂ) ^ 3) +
      Z * ((R : ℂ) ^ 3 - (Q : ℂ) ^ 3)‖ ≤
    K * (‖X‖ + ‖Y‖ + ‖Z‖)
  calc
    _ ≤ (‖X * ((R : ℂ) ^ 3 - (P : ℂ) ^ 3)‖ +
          ‖Y * ((Q : ℂ) ^ 3 - (P : ℂ) ^ 3)‖) +
          ‖Z * ((R : ℂ) ^ 3 - (Q : ℂ) ^ 3)‖ := by
            exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (‖X‖ * K + ‖Y‖ * K) + ‖Z‖ * K := by
      exact add_le_add (add_le_add hX hY) hZ
    _ = K * (‖X‖ + ‖Y‖ + ‖Z‖) := by ring

/-- If the three input frequencies lie in a common squared-radius annulus
[lo,hi], the exact gain is proportional to the annular width hi-lo. -/
theorem thirdFullComplexSixthPowerFlux_annularGain244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (lo hi : ℝ) (_hlo : 0 ≤ lo) (_hlohi : lo ≤ hi)
    (hp : lo ≤ thirdTriadAxisDot244 p p ∧
      thirdTriadAxisDot244 p p ≤ hi)
    (hq : lo ≤ thirdTriadAxisDot244 q q ∧
      thirdTriadAxisDot244 q q ≤ hi)
    (hr : lo ≤ thirdTriadAxisDot244 r r ∧
      thirdTriadAxisDot244 r r ≤ hi) :
    ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ ≤
      (3 * hi ^ 2 * (hi - lo)) *
        thirdFullComplexSixthFluxContractionBudget244 p q r A B C := by
  let S := thirdFullTriadSquareRadiusMax244 p q r
  let Δ := thirdFullTriadSquareRadiusSpread244 p q r
  have hS0 : 0 ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact (thirdFull_axisSquareRadius_nonneg244 p).trans (le_max_left _ _)
  have hSle : S ≤ hi := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact max_le hp.2 (max_le hq.2 hr.2)
  have hmLo : lo ≤ min (thirdTriadAxisDot244 p p)
      (min (thirdTriadAxisDot244 q q) (thirdTriadAxisDot244 r r)) :=
    le_min hp.1 (le_min hq.1 hr.1)
  have hΔ0 : 0 ≤ Δ := by
    dsimp only [Δ, thirdFullTriadSquareRadiusSpread244,
      thirdFullTriadSquareRadiusMax244]
    have hmP : min (thirdTriadAxisDot244 p p)
        (min (thirdTriadAxisDot244 q q) (thirdTriadAxisDot244 r r)) ≤
          thirdTriadAxisDot244 p p := min_le_left _ _
    have hpMax : thirdTriadAxisDot244 p p ≤
        max (thirdTriadAxisDot244 p p)
          (max (thirdTriadAxisDot244 q q) (thirdTriadAxisDot244 r r)) :=
      le_max_left _ _
    linarith only [hmP, hpMax]
  have hΔle : Δ ≤ hi - lo := by
    dsimp only [Δ, thirdFullTriadSquareRadiusSpread244]
    linarith only [hSle, hmLo]
  have hSsq : S ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ hS0 hSle 2
  have hK : 3 * S ^ 2 * Δ ≤ 3 * hi ^ 2 * (hi - lo) := by
    calc
      3 * S ^ 2 * Δ ≤ 3 * hi ^ 2 * Δ := by
        apply mul_le_mul_of_nonneg_right _ hΔ0
        nlinarith only [hSsq]
      _ ≤ 3 * hi ^ 2 * (hi - lo) :=
        mul_le_mul_of_nonneg_left hΔle (by positivity)
  have hBudget : 0 ≤ thirdFullComplexSixthFluxContractionBudget244
      p q r A B C := by
    unfold thirdFullComplexSixthFluxContractionBudget244
    positivity
  exact (thirdFullComplexSixthPowerFlux_radialSpread_le244 p q r A B C).trans
    (mul_le_mul_of_nonneg_right hK hBudget)


/-- The exact radial spread is nonnegative for every triad, including at the
origin and without a nonzero-frequency assumption. -/
theorem thirdFullTriadSquareRadiusSpread_nonneg244
    (p q r : A3 → ℝ) :
    0 ≤ thirdFullTriadSquareRadiusSpread244 p q r := by
  unfold thirdFullTriadSquareRadiusSpread244
  have hMin : min (thirdTriadAxisDot244 p p)
      (min (thirdTriadAxisDot244 q q) (thirdTriadAxisDot244 r r)) ≤
        thirdTriadAxisDot244 p p := min_le_left _ _
  have hMax : thirdTriadAxisDot244 p p ≤
      thirdFullTriadSquareRadiusMax244 p q r := by
    unfold thirdFullTriadSquareRadiusMax244
    exact le_max_left _ _
  linarith only [hMin, hMax]

/-- Any genuinely nonzero transverse sixth-power transfer requires distinct
squared radii. This is a necessary intershell condition, NOT a lower bound on
the spread uniform across arbitrary Fourier amplitudes. -/
theorem thirdFullComplexSixthPowerFlux_nonzero_forces_radialSpread244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hFlux : thirdFullComplexSixthPowerFlux244 p q r A B C ≠ 0) :
    0 < thirdFullTriadSquareRadiusSpread244 p q r := by
  by_contra hNo
  have hZero : thirdFullTriadSquareRadiusSpread244 p q r = 0 :=
    le_antisymm (le_of_not_gt hNo)
      (thirdFullTriadSquareRadiusSpread_nonneg244 p q r)
  have hBound := thirdFullComplexSixthPowerFlux_radialSpread_le244
    p q r A B C
  rw [hZero] at hBound
  simp only [mul_zero, zero_mul] at hBound
  have hNormZero : ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ = 0 :=
    le_antisymm hBound (norm_nonneg _)
  exact hFlux (norm_eq_zero.mp hNormZero)

/-- The same quantified spread gain applies at EVERY actual Fourier triad
of one arbitrary complex Schwartz velocity, with its real six-dimensional
carrier and correct momentum pairing `(p,-p-r,r)`. -/
theorem thirdFullSchwartzComplexSixthPowerFlux_radialSpread_le244
    (f : A3 → SchwartzMap H3FourierPoint3 ℂ)
    (z : H3FourierPoint3 × H3FourierPoint3) :
    let p : A3 → ℝ := WithLp.ofLp z.1
    let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
    let r : A3 → ℝ := WithLp.ofLp z.2
    let U := h3SchwartzTriadPolarization f
    ‖thirdFullSchwartzComplexSixthPowerFlux244 f z‖ ≤
      (3 * (thirdFullTriadSquareRadiusMax244 p q r) ^ 2 *
        thirdFullTriadSquareRadiusSpread244 p q r) *
        thirdFullComplexSixthFluxContractionBudget244
          p q r (U p) (U q) (U r) := by
  dsimp only
  exact thirdFullComplexSixthPowerFlux_radialSpread_le244
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2)))
    (WithLp.ofLp z.2)
    (h3SchwartzTriadPolarization f (WithLp.ofLp z.1))
    (h3SchwartzTriadPolarization f (WithLp.ofLp (-(z.1 + z.2))))
    (h3SchwartzTriadPolarization f (WithLp.ofLp z.2))

end
end PrimeTensor.FirstMonomialTriad
