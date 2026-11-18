import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinCompactnessEnvelope
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Pi
import Mathlib.Tactic

/-!
# Fixed finite Fourier core controls differences across arbitrary Galerkin cutoffs

A uniform W_(9/5) mass bound supplies an exponential W_(3/2) tail for
*each* zero-extended finite Galerkin state. The union of two unrelated
cutoffs therefore has a cutoff-independent difference tail. A fixed,
cutoff-independent cube of integer modes contains every frequency of
l1-degree < N. Hence the entire W_(3/2) difference of two states is
controlled by their difference on ONE fixed finite cube plus
200 * exp(-(log(9/5)-log(3/2))*N).

This is a genuine compactness upgrade criterion. It does not postulate
or claim coordinatewise convergence, a diagonal subsequence, or an
infinite Fourier Navier--Stokes solution. Those are subsequent steps.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

private abbrev CoreIndex244 := thirdFullThreeBandZ3Index244
private abbrev CoreBand244 := EuclideanSpace ℂ (Fin 3)

/-- Every finite Fourier-set Wiener sum satisfies the triangle inequality
for subtraction, for arbitrary (not necessarily supported) coefficient maps. -/
theorem thirdFullThreeBand_z3GalerkinWiener_sub_le244
    (r : ℝ) (q : Finset CoreIndex244)
    (u v : CoreIndex244 → CoreBand244) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r q (fun n => u n - v n) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r q u +
        thirdFullThreeBandZ3GalerkinWienerMass244 r q v := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
  calc
    (∑ n ∈ q, thirdFullThreeBandZ3Weight244 r n * ‖u n - v n‖) ≤
        ∑ n ∈ q, (thirdFullThreeBandZ3Weight244 r n * ‖u n‖ +
          thirdFullThreeBandZ3Weight244 r n * ‖v n‖) := by
          apply Finset.sum_le_sum
          intro n hn
          calc
            thirdFullThreeBandZ3Weight244 r n * ‖u n - v n‖ ≤
                thirdFullThreeBandZ3Weight244 r n * (‖u n‖ + ‖v n‖) :=
              mul_le_mul_of_nonneg_left (norm_sub_le (u n) (v n))
                (thirdFullThreeBand_z3Weight_pos244 r n).le
            _ = _ := by ring
    _ = _ := by rw [Finset.sum_add_distrib]

/-- Zero-extension is an isometry for Wiener mass under arbitrary enlargement
of its finite support; in particular it adds no spurious mass to s ∪ t. -/
theorem thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
    (r : ℝ) (s q : Finset CoreIndex244) (hsq : s ⊆ q)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r q
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) =
    thirdFullThreeBandZ3GalerkinWienerMass244 r s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) := by
  classical
  unfold thirdFullThreeBandZ3GalerkinWienerMass244
  apply (Finset.sum_subset hsq ?_).symm
  intro n hnq hns
  rw [thirdFullThreeBand_z3GalerkinFiniteExtend_off244 s x n hns]
  simp

/-- A uniform high-radius ball bounds the difference tail of TWO coefficient
maps by twice the single-path exponential tail, with no cutoff factor. -/
theorem thirdFullThreeBand_z3GalerkinWiener_differenceTail244
    (r R N : ℝ) (hrR : r ≤ R)
    (q : Finset CoreIndex244) (u v : CoreIndex244 → CoreBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244 R q u ≤ 100)
    (hV : thirdFullThreeBandZ3GalerkinWienerMass244 R q v ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r
      (q.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n))
      (fun n => u n - v n) ≤
      Real.exp (-(R - r) * N) * 200 := by
  have hSub := thirdFullThreeBand_z3GalerkinWiener_sub_le244 r
    (q.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n)) u v
  have hTailU := thirdFullThreeBand_z3WienerTail_twoRadius244
    r R N hrR q u
  have hTailV := thirdFullThreeBand_z3WienerTail_twoRadius244
    r R N hrR q v
  calc
    _ ≤ thirdFullThreeBandZ3GalerkinWienerMass244 r
          (q.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n)) u +
        thirdFullThreeBandZ3GalerkinWienerMass244 r
          (q.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n)) v := hSub
    _ ≤ Real.exp (-(R - r) * N) *
          thirdFullThreeBandZ3GalerkinWienerMass244 R q u +
        Real.exp (-(R - r) * N) *
          thirdFullThreeBandZ3GalerkinWienerMass244 R q v :=
      add_le_add hTailU hTailV
    _ = Real.exp (-(R - r) * N) *
          (thirdFullThreeBandZ3GalerkinWienerMass244 R q u +
            thirdFullThreeBandZ3GalerkinWienerMass244 R q v) := by ring
    _ ≤ Real.exp (-(R - r) * N) * 200 :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

/-- The full difference is its low-frequency core plus an exponentially
small high-frequency remainder. This is true for any two coefficient maps
on one finite output set, without assuming they have matching supports. -/
theorem thirdFullThreeBand_z3GalerkinWiener_fixedCore_split244
    (r R N : ℝ) (hrR : r ≤ R)
    (q : Finset CoreIndex244) (u v : CoreIndex244 → CoreBand244)
    (hU : thirdFullThreeBandZ3GalerkinWienerMass244 R q u ≤ 100)
    (hV : thirdFullThreeBandZ3GalerkinWienerMass244 R q v ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244 r q (fun n => u n - v n) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 r
        (q.filter (fun n => thirdFullThreeBandZ3Degree244 n < N))
        (fun n => u n - v n) +
      Real.exp (-(R - r) * N) * 200 := by
  classical
  have hSplit :
      thirdFullThreeBandZ3GalerkinWienerMass244 r q (fun n => u n - v n) =
        thirdFullThreeBandZ3GalerkinWienerMass244 r
          (q.filter (fun n => thirdFullThreeBandZ3Degree244 n < N))
          (fun n => u n - v n) +
        thirdFullThreeBandZ3GalerkinWienerMass244 r
          (q.filter (fun n => N ≤ thirdFullThreeBandZ3Degree244 n))
          (fun n => u n - v n) := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
    simpa only [not_lt] using
      (Finset.sum_filter_add_sum_filter_not q
        (fun n => thirdFullThreeBandZ3Degree244 n < N)
        (fun n => thirdFullThreeBandZ3Weight244 r n * ‖u n - v n‖)).symm
  rw [hSplit]
  exact add_le_add_right
    (thirdFullThreeBand_z3GalerkinWiener_differenceTail244
      r R N hrR q u v hU hV) _

/-- A genuinely FIXED finite cube of integer frequencies, independent of
all Galerkin cutoffs and of the time variable. -/
def thirdFullThreeBandZ3GalerkinFixedCoreCube244 (N : ℕ) :
    Finset CoreIndex244 :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N : ℤ)) (N : ℤ))

/-- Every frequency of l1-degree < N is in the SAME finite cube.
No cutoff-dependent finite set is needed in the diagonal argument. -/
theorem thirdFullThreeBand_z3Galerkin_degree_lt_mem_fixedCube244
    (N : ℕ) (n : CoreIndex244)
    (hn : thirdFullThreeBandZ3Degree244 n < (N : ℝ)) :
    n ∈ thirdFullThreeBandZ3GalerkinFixedCoreCube244 N := by
  classical
  unfold thirdFullThreeBandZ3GalerkinFixedCoreCube244
  rw [Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_Icc]
  have hCoord : |(n j : ℝ)| ≤ thirdFullThreeBandZ3Degree244 n := by
    unfold thirdFullThreeBandZ3Degree244
    exact Finset.single_le_sum (fun k hk => abs_nonneg (n k : ℝ))
      (Finset.mem_univ j)
  have hBound : |(n j : ℝ)| ≤ (N : ℝ) := (hCoord.trans_lt hn).le
  have hLower : -(N : ℝ) ≤ (n j : ℝ) := (abs_le.mp hBound).1
  have hUpper : (n j : ℝ) ≤ (N : ℝ) := (abs_le.mp hBound).2
  constructor
  · exact_mod_cast hLower
  · exact_mod_cast hUpper

/-- Uniform TWO-CUTOFF quantitative compactness: the entire lower-radius
Wiener difference of two zero-extended Galerkin states is controlled by a
FIXED finite cube, plus 200 exp(-gap*N). The supports may be unrelated.
This is the key reduction from strong convergence to finite-coordinate
convergence; it does not assume convergence or its subsequence extraction. -/
theorem thirdFullThreeBand_z3Galerkin_twoCutoff_fixedCore244
    (N : ℕ) (s t : Finset CoreIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (y : thirdFullThreeBandZ3GalerkinFiniteState244 t)
    (hX : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100)
    (hY : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) t
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y) ≤ 100) :
    thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
      (s ∪ t)
      (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n -
        thirdFullThreeBandZ3GalerkinFiniteExtend244 t y n) ≤
    thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
      (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N)
      (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n -
        thirdFullThreeBandZ3GalerkinFiniteExtend244 t y n) +
    Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) * (N : ℝ)) * 200 := by
  classical
  let u := thirdFullThreeBandZ3GalerkinFiniteExtend244 s x
  let v := thirdFullThreeBandZ3GalerkinFiniteExtend244 t y
  have hUnionX : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) (s ∪ t) u ≤ 100 := by
    rw [thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
      (Real.log (9 / 5 : ℝ)) s (s ∪ t) Finset.subset_union_left x]
    exact hX
  have hUnionY : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) (s ∪ t) v ≤ 100 := by
    rw [thirdFullThreeBand_z3GalerkinWiener_zeroExtend_superset244
      (Real.log (9 / 5 : ℝ)) t (s ∪ t) Finset.subset_union_right y]
    exact hY
  have hRadius : Real.log (3 / 2 : ℝ) ≤ Real.log (9 / 5 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hSplit := thirdFullThreeBand_z3GalerkinWiener_fixedCore_split244
    (Real.log (3 / 2 : ℝ)) (Real.log (9 / 5 : ℝ))
    (N : ℝ) hRadius (s ∪ t) u v hUnionX hUnionY
  have hSubset : (s ∪ t).filter
      (fun n => thirdFullThreeBandZ3Degree244 n < (N : ℝ)) ⊆
      thirdFullThreeBandZ3GalerkinFixedCoreCube244 N := by
    intro n hn
    exact thirdFullThreeBand_z3Galerkin_degree_lt_mem_fixedCube244
      N n (Finset.mem_filter.mp hn).2
  have hCore : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ))
      ((s ∪ t).filter (fun n => thirdFullThreeBandZ3Degree244 n < (N : ℝ)))
      (fun n => u n - v n) ≤
      thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
        (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N)
        (fun n => u n - v n) := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
    apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
    intro n hn hnNot
    exact mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le
      (norm_nonneg _)
  exact hSplit.trans (add_le_add_left hCore _)

/-- A direct epsilon criterion: small difference on one fixed finite cube
plus the uniform analytic tail forces globally small Wiener difference
between two entirely unrelated cutoffs. -/
theorem thirdFullThreeBand_z3Galerkin_twoCutoff_small_of_fixedCore244
    (N : ℕ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (s t : Finset CoreIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (y : thirdFullThreeBandZ3GalerkinFiniteState244 t)
    (hX : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) ≤ 100)
    (hY : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (9 / 5 : ℝ)) t
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y) ≤ 100)
    (hCore : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (3 / 2 : ℝ))
      (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N)
      (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n -
        thirdFullThreeBandZ3GalerkinFiniteExtend244 t y n) ≤ epsilon / 2)
    (hTail : Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
      (N : ℝ)) * 200 ≤ epsilon / 2) :
    thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
      (s ∪ t)
      (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s x n -
        thirdFullThreeBandZ3GalerkinFiniteExtend244 t y n) ≤ epsilon := by
  have hBound := thirdFullThreeBand_z3Galerkin_twoCutoff_fixedCore244
    N s t x y hX hY
  linarith

/-- Two ACTUALLY CONSTRUCTED Galerkin flows for arbitrary cutoffs have the
same fixed-core/tail comparison on their full common closed time interval.
The paths, their strong ODEs and their analytic mass bounds are CONSTRUCTED
from the initial states, not assumed as external trajectories. -/
theorem thirdFullThreeBand_z3Galerkin_exists_twoCutoff_fixedCore244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s t : Finset CoreIndex244)
    (x : thirdFullThreeBandZ3GalerkinFiniteState244 s)
    (y : thirdFullThreeBandZ3GalerkinFiniteState244 t)
    (hInitialX : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) s
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 s x) < 100)
    (hInitialY : thirdFullThreeBandZ3GalerkinWienerMass244
      (Real.log (2 : ℝ)) t
      (thirdFullThreeBandZ3GalerkinFiniteExtend244 t y) < 100) :
    ∃ gamma : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 s,
    ∃ beta : ℝ → thirdFullThreeBandZ3GalerkinFiniteState244 t,
      gamma a = x ∧ beta a = y ∧
      (∀ z ∈ Set.Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        HasDerivAt gamma (thirdFullThreeBandZ3GalerkinFiniteField244 mu s (gamma z)) z) ∧
      (∀ z ∈ Set.Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        HasDerivAt beta (thirdFullThreeBandZ3GalerkinFiniteField244 mu t (beta z)) z) ∧
      (∀ z ∈ Set.Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ N : ℕ,
          thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
            (s ∪ t)
            (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma z) n -
              thirdFullThreeBandZ3GalerkinFiniteExtend244 t (beta z) n) ≤
          thirdFullThreeBandZ3GalerkinWienerMass244 (Real.log (3 / 2 : ℝ))
            (thirdFullThreeBandZ3GalerkinFixedCoreCube244 N)
            (fun n => thirdFullThreeBandZ3GalerkinFiniteExtend244 s (gamma z) n -
              thirdFullThreeBandZ3GalerkinFiniteExtend244 t (beta z) n) +
          Real.exp (-(Real.log (9 / 5 : ℝ) - Real.log (3 / 2 : ℝ)) *
            (N : ℝ)) * 200) := by
  obtain ⟨gamma, hGammaStart, hGammaODE, _hMovingGamma, _hLipGamma,
    hHighGamma, _hSpeedGamma, _hTailGamma⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244
      mu a hmu hmuMax s x hInitialX
  obtain ⟨beta, hBetaStart, hBetaODE, _hMovingBeta, _hLipBeta,
    hHighBeta, _hSpeedBeta, _hTailBeta⟩ :=
    thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244
      mu a hmu hmuMax t y hInitialY
  refine ⟨gamma, beta, hGammaStart, hBetaStart, hGammaODE, hBetaODE, ?_⟩
  intro z hz N
  exact thirdFullThreeBand_z3Galerkin_twoCutoff_fixedCore244
    N s t (gamma z) (beta z) (hHighGamma z hz) (hHighBeta z hz)

end
end PrimeTensor.FirstMonomialTriad
