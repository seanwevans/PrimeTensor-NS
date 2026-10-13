import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowResonance

/-!
# Quantitative nonresonance for the six sharp low-normal Fourier centers

The integer-lattice classification already excludes every noncoherent triple.
Here we upgrade nonvanishing to an explicit coordinate margin.  The plane
embedding (A,B) |-> (A+tB,tB,0) has the decisive property that either
B != 0, whence the second physical coordinate has magnitude at least |t|,
or B = 0 and A != 0, whence the first coordinate has magnitude at least 1.

Therefore any three frequency vectors lying in coordinatewise balls of
radius min(1,|t|)/4 about the six centers can sum to zero only if their
center labels form one of the twelve coherent triples.  This is a support
separation theorem, not yet the construction of Schwartz Fourier bumps or a
nonzero integrated first-monomial pairing.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section

/-- Integer sum of three signed center lattice coordinates. -/
def lowNormalThreeCenterLatticeSum (i j k : Fin 6) (d : Fin 2) : ℤ :=
  lowNormalSignedLatticeCenter i d +
    lowNormalSignedLatticeCenter j d +
      lowNormalSignedLatticeCenter k d

/-- A nonzero integer has real absolute value at least one. -/
private theorem int_cast_abs_ge_one (z : ℤ) (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  have hcases : z ≤ -1 ∨ 1 ≤ z := by omega
  rcases hcases with hneg | hpos
  · have hreal : (z : ℝ) ≤ -1 := by exact_mod_cast hneg
    rw [abs_of_nonpos (by linarith : (z : ℝ) ≤ 0)]
    linarith
  · have hreal : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hpos
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z)]
    linarith

/-- First coordinate of an embedded three-center frequency sum. -/
theorem lowNormalSixCenter_sum_zero_coordinate
    (t : ℝ) (i j k : Fin 6) :
    lowNormalSixCenter t i 0 + lowNormalSixCenter t j 0 +
      lowNormalSixCenter t k 0 =
      (lowNormalThreeCenterLatticeSum i j k 0 : ℝ) +
        t * (lowNormalThreeCenterLatticeSum i j k 1 : ℝ) := by
  simp only [lowNormalSixCenter, lowNormalLatticeEmbedding_zero,
    lowNormalThreeCenterLatticeSum]
  push_cast
  ring

/-- Second coordinate of an embedded three-center frequency sum. -/
theorem lowNormalSixCenter_sum_one_coordinate
    (t : ℝ) (i j k : Fin 6) :
    lowNormalSixCenter t i 1 + lowNormalSixCenter t j 1 +
      lowNormalSixCenter t k 1 =
      t * (lowNormalThreeCenterLatticeSum i j k 1 : ℝ) := by
  simp only [lowNormalSixCenter, lowNormalLatticeEmbedding_one,
    lowNormalThreeCenterLatticeSum]
  push_cast
  ring

/-- A noncoherent triple has a physical coordinate with a definite gap.
No asymptotic or compactness argument is necessary. -/
theorem lowNormalSixCenter_noncoherent_coordinate_gap
    (t : ℝ) (i j k : Fin 6)
    (hNoncoherent : ¬ lowNormalCoherentCenters i j k) :
    ∃ d : Fin 3, min (1 : ℝ) |t| ≤
      |lowNormalSixCenter t i d + lowNormalSixCenter t j d +
        lowNormalSixCenter t k d| := by
  have hAB : lowNormalThreeCenterLatticeSum i j k 0 ≠ 0 ∨
      lowNormalThreeCenterLatticeSum i j k 1 ≠ 0 := by
    obtain ⟨d, hd⟩ :=
      lowNormalSignedLatticeCenter_noncoherent i j k hNoncoherent
    fin_cases d
    · exact Or.inl hd
    · exact Or.inr hd
  by_cases hB : lowNormalThreeCenterLatticeSum i j k 1 = 0
  · have hA : lowNormalThreeCenterLatticeSum i j k 0 ≠ 0 := by
      rcases hAB with hA | hBne
      · exact hA
      · exact (hBne hB).elim
    refine ⟨0, ?_⟩
    rw [lowNormalSixCenter_sum_zero_coordinate]
    simp only [hB, Int.cast_zero, mul_zero, add_zero]
    exact (min_le_left (1 : ℝ) |t|).trans (int_cast_abs_ge_one _ hA)
  · refine ⟨1, ?_⟩
    rw [lowNormalSixCenter_sum_one_coordinate, abs_mul]
    calc
      min (1 : ℝ) |t| ≤ |t| := min_le_right _ _
      _ = |t| * 1 := by ring
      _ ≤ |t| * |(lowNormalThreeCenterLatticeSum i j k 1 : ℝ)| :=
        mul_le_mul_of_nonneg_left (int_cast_abs_ge_one _ hB) (abs_nonneg t)

/-- One fourth of the worst possible nonzero coordinate gap. -/
def lowNormalSixCenterSeparationRadius (t : ℝ) : ℝ :=
  min (1 : ℝ) |t| / 4

theorem lowNormalSixCenterSeparationRadius_pos
    (t : ℝ) (ht : t ≠ 0) :
    0 < lowNormalSixCenterSeparationRadius t := by
  unfold lowNormalSixCenterSeparationRadius
  have habs : 0 < |t| := abs_pos.mpr ht
  exact div_pos (lt_min (by norm_num) habs) (by norm_num)

/-- Coordinatewise Fourier localization around a labeled center. -/
def lowNormalSixCenterCoordinateBall
    (t : ℝ) (i : Fin 6) (x : Fin 3 → ℝ) : Prop :=
  ∀ d : Fin 3,
    |x d - lowNormalSixCenter t i d| < lowNormalSixCenterSeparationRadius t

/-- Any zero-momentum triple in the six small frequency neighborhoods must
belong to one of the twelve intended oriented triads. -/
theorem lowNormalSixCenterCoordinateBall_zero_sum_coherent
    (t : ℝ) (ht : t ≠ 0) (i j k : Fin 6)
    (x y z : Fin 3 → ℝ)
    (hx : lowNormalSixCenterCoordinateBall t i x)
    (hy : lowNormalSixCenterCoordinateBall t j y)
    (hz : lowNormalSixCenterCoordinateBall t k z)
    (hSum : ∀ d : Fin 3, x d + y d + z d = 0) :
    lowNormalCoherentCenters i j k := by
  by_contra hNoncoherent
  obtain ⟨d, hGap⟩ :=
    lowNormalSixCenter_noncoherent_coordinate_gap t i j k hNoncoherent
  have hx' : |lowNormalSixCenter t i d - x d| <
      lowNormalSixCenterSeparationRadius t := by
    simpa only [abs_sub_comm] using hx d
  have hy' : |lowNormalSixCenter t j d - y d| <
      lowNormalSixCenterSeparationRadius t := by
    simpa only [abs_sub_comm] using hy d
  have hz' : |lowNormalSixCenter t k d - z d| <
      lowNormalSixCenterSeparationRadius t := by
    simpa only [abs_sub_comm] using hz d
  have hIdentity :
      lowNormalSixCenter t i d + lowNormalSixCenter t j d +
        lowNormalSixCenter t k d =
      (lowNormalSixCenter t i d - x d) +
        (lowNormalSixCenter t j d - y d) +
          (lowNormalSixCenter t k d - z d) := by
    linarith [hSum d]
  have hTri :
      |lowNormalSixCenter t i d + lowNormalSixCenter t j d +
        lowNormalSixCenter t k d| ≤
      |lowNormalSixCenter t i d - x d| +
        |lowNormalSixCenter t j d - y d| +
          |lowNormalSixCenter t k d - z d| := by
    rw [hIdentity]
    calc
      _ ≤ |(lowNormalSixCenter t i d - x d) +
              (lowNormalSixCenter t j d - y d)| +
              |lowNormalSixCenter t k d - z d| := abs_add_le _ _
      _ ≤ |lowNormalSixCenter t i d - x d| +
              |lowNormalSixCenter t j d - y d| +
                |lowNormalSixCenter t k d - z d| := by
          exact add_le_add
            (abs_add_le (lowNormalSixCenter t i d - x d)
              (lowNormalSixCenter t j d - y d))
            (le_refl _)
  have hMinPos : 0 < min (1 : ℝ) |t| :=
    lt_min (by norm_num) (abs_pos.mpr ht)
  have hQuarter :
      3 * lowNormalSixCenterSeparationRadius t < min (1 : ℝ) |t| := by
    unfold lowNormalSixCenterSeparationRadius
    linarith
  linarith

end
end PrimeTensor.FirstMonomialTriad
