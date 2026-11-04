import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalAnnularFluxDecomposition
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadFourier
import Mathlib.Tactic

/-!
# Absolute six-dimensional contraction budget for a solenoidal H³ flux

The thin-annulus Fourier bound previously required local L¹ integrability of
an unsigned three-channel complex contraction budget. We now prove that
integrability for EVERY complex Schwartz field, independently of solenoidality.

Every complex contraction is expanded into 3² coordinate-indexed Fourier
triples; the single frequency in each mixed contraction can be moved onto
an existing Fourier factor at that SAME frequency. The repository's genuine
weighted Schwartz triple-integrability theorem then closes all 27 terms.
No crude pointwise Fourier L∞ or H³-only budget bound is inserted.

The resulting global finite unsigned budget allows unconditional localized
annular estimates and a sharp complementary off-shell excess gate for any
complex physically divergence-free Schwartz field. It does NOT control the
budgets uniformly over an H³ density sequence. Thus no uniform physical PDE
transport bound or continuation theorem follows from this file alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypeAnnularBudget244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- First cubic Fourier contraction: outer polarization at p and r,
with the r-frequency differentiated on the existing outer r-amplitude. -/
noncomputable def thirdFullSchwartzSixthFluxBudgetFirst244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) : ℂ :=
  (∑ j : A3, (𝓕 (v j)) z.1 * (𝓕 (v j)) z.2) *
    (∑ m : A3, ((WithLp.ofLp z.2 m : ℝ) : ℂ) *
      (𝓕 (v m)) (-(z.1 + z.2)))

/-- Second contraction: q acts on the Fourier factor already at q. -/
noncomputable def thirdFullSchwartzSixthFluxBudgetSecond244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) : ℂ :=
  (∑ j : A3,
      (𝓕 (v j)) z.1 * (𝓕 (v j)) (-(z.1 + z.2))) *
    (∑ m : A3, ((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
      (𝓕 (v m)) z.2)

/-- Third contraction: r acts on the second polarization factor at r. -/
noncomputable def thirdFullSchwartzSixthFluxBudgetThird244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) : ℂ :=
  (∑ j : A3,
      (𝓕 (v j)) (-(z.1 + z.2)) * (𝓕 (v j)) z.2) *
    (∑ m : A3, ((WithLp.ofLp z.2 m : ℝ) : ℂ) *
      (𝓕 (v m)) z.1)

/-- Elementary finite two-index contraction, with complex multiplication
kept in the precise ordering used by the weighted Fourier triple. -/
private theorem thirdFull_budget_doubleSum244
    (a b c d : A3 → ℂ) :
    (∑ j : A3, a j * b j) * (∑ m : A3, c m * d m) =
      ∑ j : A3, ∑ m : A3, (a j * (c m * b j)) * d m := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The unweighted complex triple, with one real Fourier coordinate
multiplier on the OUTER r-factor, is absolutely integrable. -/
private theorem thirdFull_budget_weightedOuter_integrable244
    (f g h : SchwartzMap V3 ℂ) (m : A3) :
    Integrable (fun z : PairV =>
      ((𝓕 f z.1 * (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 h z.2)) *
        𝓕 g (-(z.1 + z.2)))) (volume.prod volume) := by
  have hi := h3Schwartz_triad_integrable
    (𝓕 f) (𝓕 g)
    (h3Schwartz_frequencyWeight (h3FourierAxisDirection m) (𝓕 h))
  apply hi.congr
  filter_upwards with z
  simp only [h3Schwartz_frequencyWeight_apply, inner_h3FourierAxisDirection]

/-- The same estimate with the coordinate multiplier carried at the
MIDDLE q-frequency; no convolution inequality is postulated. -/
private theorem thirdFull_budget_weightedMiddle_integrable244
    (f g h : SchwartzMap V3 ℂ) (m : A3) :
    Integrable (fun z : PairV =>
      ((𝓕 f z.1 *
          (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
            𝓕 g (-(z.1 + z.2)))) * 𝓕 h z.2))
      (volume.prod volume) := by
  have hi := h3Schwartz_triad_integrable
    (𝓕 f)
    (h3Schwartz_frequencyWeight (h3FourierAxisDirection m) (𝓕 g))
    (𝓕 h)
  apply hi.congr
  filter_upwards with z
  simp only [h3Schwartz_frequencyWeight_apply, inner_h3FourierAxisDirection]
  ring

/-- The first complex contraction has an unconditional L¹ norm. -/
theorem thirdFullSchwartzSixthFluxBudgetFirst_integrable244
    (v : A3 → SchwartzMap V3 ℂ) :
    Integrable (thirdFullSchwartzSixthFluxBudgetFirst244 v)
      (volume.prod volume) := by
  have hTerm (j m : A3) :
      Integrable (fun z : PairV =>
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (v j) z.2)) *
          𝓕 (v m) (-(z.1 + z.2)))) (volume.prod volume) :=
    thirdFull_budget_weightedOuter_integrable244 (v j) (v m) (v j) m
  have hSum : Integrable (fun z : PairV =>
      ∑ j : A3, ∑ m : A3,
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (v j) z.2)) *
          𝓕 (v m) (-(z.1 + z.2)))) (volume.prod volume) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro m _
    exact hTerm j m
  apply hSum.congr
  filter_upwards with z
  exact (thirdFull_budget_doubleSum244
    (fun j => 𝓕 (v j) z.1) (fun j => 𝓕 (v j) z.2)
    (fun m => (((WithLp.ofLp z.2 m : ℝ) : ℂ)))
    (fun m => 𝓕 (v m) (-(z.1 + z.2)))).symm

/-- The second complex contraction has an unconditional L¹ norm. -/
theorem thirdFullSchwartzSixthFluxBudgetSecond_integrable244
    (v : A3 → SchwartzMap V3 ℂ) :
    Integrable (thirdFullSchwartzSixthFluxBudgetSecond244 v)
      (volume.prod volume) := by
  have hTerm (j m : A3) :
      Integrable (fun z : PairV =>
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
            𝓕 (v j) (-(z.1 + z.2)))) * 𝓕 (v m) z.2))
        (volume.prod volume) :=
    thirdFull_budget_weightedMiddle_integrable244 (v j) (v j) (v m) m
  have hSum : Integrable (fun z : PairV =>
      ∑ j : A3, ∑ m : A3,
        ((𝓕 (v j) z.1 *
          (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ) *
            𝓕 (v j) (-(z.1 + z.2)))) * 𝓕 (v m) z.2))
      (volume.prod volume) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro m _
    exact hTerm j m
  apply hSum.congr
  filter_upwards with z
  exact (thirdFull_budget_doubleSum244
    (fun j => 𝓕 (v j) z.1)
    (fun j => 𝓕 (v j) (-(z.1 + z.2)))
    (fun m => (((WithLp.ofLp (-(z.1 + z.2)) m : ℝ) : ℂ)))
    (fun m => 𝓕 (v m) z.2)).symm

/-- The third complex contraction has an unconditional L¹ norm. -/
theorem thirdFullSchwartzSixthFluxBudgetThird_integrable244
    (v : A3 → SchwartzMap V3 ℂ) :
    Integrable (thirdFullSchwartzSixthFluxBudgetThird244 v)
      (volume.prod volume) := by
  have hTerm (j m : A3) :
      Integrable (fun z : PairV =>
        ((𝓕 (v j) (-(z.1 + z.2)) *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (v j) z.2)) *
          𝓕 (v m) z.1)) (volume.prod volume) := by
    have hi := thirdFull_budget_weightedOuter_integrable244
      (v m) (v j) (v j) m
    apply hi.congr
    filter_upwards with z
    ring
  have hSum : Integrable (fun z : PairV =>
      ∑ j : A3, ∑ m : A3,
        ((𝓕 (v j) (-(z.1 + z.2)) *
          (((WithLp.ofLp z.2 m : ℝ) : ℂ) * 𝓕 (v j) z.2)) *
          𝓕 (v m) z.1)) (volume.prod volume) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro m _
    exact hTerm j m
  apply hSum.congr
  filter_upwards with z
  exact (thirdFull_budget_doubleSum244
    (fun j => 𝓕 (v j) (-(z.1 + z.2)))
    (fun j => 𝓕 (v j) z.2)
    (fun m => (((WithLp.ofLp z.2 m : ℝ) : ℂ)))
    (fun m => 𝓕 (v m) z.1)).symm

/-- Identifies the actual three-channel unsigned symbol with the norms of
three genuine integrable complex Schwartz triple contractions. -/
theorem thirdFullSchwartzSixthFluxBudget_eq_coordinateNorms244
    (v : A3 → SchwartzMap V3 ℂ) (z : PairV) :
    thirdFullSchwartzSixthFluxBudget244 v z =
      ‖thirdFullSchwartzSixthFluxBudgetFirst244 v z‖ +
      ‖thirdFullSchwartzSixthFluxBudgetSecond244 v z‖ +
      ‖thirdFullSchwartzSixthFluxBudgetThird244 v z‖ := by
  simp only [thirdFullSchwartzSixthFluxBudget244,
    thirdFullComplexSixthFluxContractionBudget244,
    thirdFullComplexPolarizationDot244, mixedDot,
    thirdFullSchwartzSixthFluxBudgetFirst244,
    thirdFullSchwartzSixthFluxBudgetSecond244,
    thirdFullSchwartzSixthFluxBudgetThird244,
    h3SchwartzTriadPolarization, WithLp.toLp_ofLp]

/-- The EXACT previously conditional unsigned contraction budget is
unconditionally integrable for EVERY complex Schwartz velocity. It needs
no solenoidal, spectral support, or physical H³-energy hypothesis. -/
theorem thirdFullSchwartzSixthFluxBudget_integrable244
    (v : A3 → SchwartzMap V3 ℂ) :
    Integrable (thirdFullSchwartzSixthFluxBudget244 v)
      (volume.prod volume) := by
  have hXYZ : Integrable (fun z : PairV =>
      ‖thirdFullSchwartzSixthFluxBudgetFirst244 v z‖ +
        ‖thirdFullSchwartzSixthFluxBudgetSecond244 v z‖ +
        ‖thirdFullSchwartzSixthFluxBudgetThird244 v z‖)
      (volume.prod volume) :=
    ((thirdFullSchwartzSixthFluxBudgetFirst_integrable244 v).norm.add
      (thirdFullSchwartzSixthFluxBudgetSecond_integrable244 v).norm).add
      (thirdFullSchwartzSixthFluxBudgetThird_integrable244 v).norm
  exact hXYZ.congr (Filter.Eventually.of_forall (fun z =>
    (thirdFullSchwartzSixthFluxBudget_eq_coordinateNorms244 v z).symm))

/-- Finite total unsigned triad budget for one complex Schwartz field.
This may grow with the Schwartz density index and is NOT an H³-only bound. -/
noncomputable def thirdFullSchwartzSixthFluxTotalBudget244
    (v : A3 → SchwartzMap V3 ℂ) : ℝ :=
  ∫ z : PairV, thirdFullSchwartzSixthFluxBudget244 v z
    ∂volume.prod volume

/-- The global budget is a finite, nonnegative real number. -/
theorem thirdFullSchwartzSixthFluxTotalBudget_nonneg244
    (v : A3 → SchwartzMap V3 ℂ) :
    0 ≤ thirdFullSchwartzSixthFluxTotalBudget244 v := by
  unfold thirdFullSchwartzSixthFluxTotalBudget244
  exact integral_nonneg (thirdFullSchwartzSixthFluxBudget_nonneg244 v)

/-- Every measurable sector uses at most the whole integrable, nonnegative
Schwartz contraction budget; this is independent of annular geometry. -/
theorem thirdFullSchwartzSixthFluxBudget_sector_le_total244
    (v : A3 → SchwartzMap V3 ℂ)
    (s : Set PairV) (_hs : MeasurableSet s) :
    (∫ z in s, thirdFullSchwartzSixthFluxBudget244 v z
      ∂volume.prod volume) ≤ thirdFullSchwartzSixthFluxTotalBudget244 v := by
  unfold thirdFullSchwartzSixthFluxTotalBudget244
  apply integral_mono_measure Measure.restrict_le_self
  · exact Filter.Eventually.of_forall
      (thirdFullSchwartzSixthFluxBudget_nonneg244 v)
  · exact thirdFullSchwartzSixthFluxBudget_integrable244 v

/-- A genuine UNCONDITIONAL thin-shell integral estimate for every complex
Schwartz field with physical zero divergence. The former local budget
integrability premise has been proved rather than postulated. -/
theorem thirdFullSchwartzSixthPowerFlux_annularIntegral_auto244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (s : Set PairV) (hs : MeasurableSet s)
    (hShell : ∀ z ∈ s, thirdFullTriadWithinSquareAnnulus244 lo hi z) :
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      (3 * hi ^ 2 * (hi - lo)) *
        thirdFullSchwartzSixthFluxTotalBudget244 v := by
  have hNear := thirdFullSchwartzSixthPowerFlux_annularIntegral_le244
    v hDiv lo hi hlo hlohi s hs hShell
    (thirdFullSchwartzSixthFluxBudget_integrable244 v).integrableOn
  have hK : 0 ≤ 3 * hi ^ 2 * (hi - lo) := by
    have hhi : 0 ≤ hi := hlo.trans hlohi
    positivity
  exact hNear.trans (mul_le_mul_of_nonneg_left
    (thirdFullSchwartzSixthFluxBudget_sector_le_total244 v s hs) hK)

/-- A large full solenoidal H³ sixth-power flux must be carried off a thin
annulus unless its finite, explicitly evaluated Schwartz L¹ budget pays
for it. There is NO separate budget-integrability hypothesis. -/
theorem thirdFullSchwartzSixthPowerFlux_offshellFloor_auto244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (s : Set PairV) (hs : MeasurableSet s)
    (hShell : ∀ z ∈ s, thirdFullTriadWithinSquareAnnulus244 lo hi z)
    (M : ℝ)
    (hExcess :
      (3 * hi ^ 2 * (hi - lo)) *
        thirdFullSchwartzSixthFluxTotalBudget244 v + M <
      ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖) :
    M < ‖∫ z in sᶜ,
      thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ := by
  have hSplit := thirdFullSchwartzSixthPowerFlux_setSplit244 v hDiv s hs
  have hNear := thirdFullSchwartzSixthPowerFlux_annularIntegral_auto244
    v hDiv lo hi hlo hlohi s hs hShell
  rw [hSplit] at hExcess
  have hTriangle := norm_add_le
    (∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
      ∂volume.prod volume)
    (∫ z in sᶜ, thirdFullSchwartzComplexSixthPowerFlux244 v z
      ∂volume.prod volume)
  linarith only [hExcess, hTriangle, hNear]


/-- For a FIXED solenoidal Schwartz field, a bounded family of common
squared-radius annuli whose widths tend to zero contributes asymptotically
zero sixth-power flux. No bound uniform over a Schwartz density sequence
is inferred. This is an integrated, rather than pointwise, shell limit. -/
theorem thirdFullSchwartzSixthPowerFlux_shrinkingAnnulus_vanishes244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (lo hi : ℕ → ℝ) (H : ℝ)
    (hlo : ∀ n, 0 ≤ lo n) (hlohi : ∀ n, lo n ≤ hi n)
    (hhi : ∀ n, hi n ≤ H)
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n))
    (hShell : ∀ n z, z ∈ s n →
      thirdFullTriadWithinSquareAnnulus244 (lo n) (hi n) z)
    (hWidth : Tendsto (fun n => hi n - lo n) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ‖∫ z in s n,
      thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖) atTop (𝓝 (0 : ℝ)) := by
  let B : ℝ := thirdFullSchwartzSixthFluxTotalBudget244 v
  have hB : 0 ≤ B := thirdFullSchwartzSixthFluxTotalBudget_nonneg244 v
  have hUpper (n : ℕ) :
      ‖∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      (3 * H ^ 2 * (hi n - lo n)) * B := by
    have hNear := thirdFullSchwartzSixthPowerFlux_annularIntegral_auto244
      v hDiv (lo n) (hi n) (hlo n) (hlohi n)
      (s n) (hs n) (hShell n)
    have hSquare : (hi n) ^ 2 ≤ H ^ 2 :=
      pow_le_pow_left₀ ((hlo n).trans (hlohi n)) (hhi n) 2
    have hCoeff :
        3 * (hi n) ^ 2 * (hi n - lo n) ≤
        3 * H ^ 2 * (hi n - lo n) := by
      have hSq : 3 * (hi n) ^ 2 ≤ 3 * H ^ 2 := by
        nlinarith only [hSquare]
      exact mul_le_mul_of_nonneg_right hSq (sub_nonneg.mpr (hlohi n))
    exact hNear.trans (mul_le_mul_of_nonneg_right hCoeff hB)
  have hMajor : Tendsto
      (fun n => (3 * H ^ 2 * (hi n - lo n)) * B)
      atTop (𝓝 (0 : ℝ)) := by
    have h := (hWidth.const_mul (3 * H ^ 2)).mul_const B
    simpa only [mul_zero, zero_mul] using h
  exact squeeze_zero
    (fun n => norm_nonneg _)
    hUpper hMajor

end
end PrimeTensor.FirstMonomialTriad
