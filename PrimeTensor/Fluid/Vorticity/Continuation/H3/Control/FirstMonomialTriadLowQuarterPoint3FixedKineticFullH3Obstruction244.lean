import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FixedKineticConcentrationBarrier244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3ActualDilationEnergySums
import Mathlib.Tactic

/-!
# Fixed kinetic mass does not absorb the signed H³ interpolation monomial,
# even after paying a multiple of the FULL normalized H³ energy

For the genuine Point3 real Schwartz concentration

  f_t(x) = t³ f(t² x),  t > 0,

the project has already proved E0(f_t)=E0(f), D4(f_t)=t^16 D4(f),
M(f_t)=t^17 M(f) and E1(f_t)=t^4 E1(f). This module closes the other two
physical quadratic blocks:

  E2(f_t)=t^8 E2(f),  E3(f_t)=t^12 E3(f).

Hence the *entire* normalized H³ energy, including all three components
and all derivative orders 0 through 3, grows only through t^12, while
quadratic top dissipation grows through t^16 and the positive signed first
monomial through t^17.

Consequently no constant-coefficient estimate

  M(f) <= C D4(f) + K (1 + E0(f)+E1(f)+E2(f)+E3(f))

holds on the divergence-free Schwartz class, EVEN AT A FIXED EXACT E0.
This is not a counterexample to regularity: the first monomial is not
identical to the complete physical Navier--Stokes transport.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFixedKineticFullH3_244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Amplitude homogeneity of the full 27-slot real second-jet energy. -/
theorem fixedKinetic_secondEnergy_real_smul244
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Energy2 f := by
  unfold lowNormalRealSchwartzH3Energy2
  simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul]
  simp only [← Finset.mul_sum]

/-- Amplitude homogeneity of all 81 real third-jet squares. -/
theorem fixedKinetic_thirdEnergy_real_smul244
    (a : ℝ) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy3 (fun j => a • f j) =
      a ^ 2 * lowNormalRealSchwartzH3Energy3 f := by
  unfold lowNormalRealSchwartzH3Energy3
  simp only [LineDeriv.lineDerivOp_smul, smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul]
  simp only [← Finset.mul_sum]

/-- A true physical concentration identity, for all 27 second-order slots. -/
theorem fixedKineticSchwartzConcentration_energy2_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy2
      (fixedKineticSchwartzConcentration244 t ht f) =
      t ^ 8 * lowNormalRealSchwartzH3Energy2 f := by
  unfold fixedKineticSchwartzConcentration244
  rw [fixedKinetic_secondEnergy_real_smul244,
    lowNormalRealSchwartzH3Energy2_dilation]
  have hn : t ≠ 0 := ne_of_gt ht
  field_simp [hn]

/-- The full 81-slot third-order physical square mass grows as t^12. -/
theorem fixedKineticSchwartzConcentration_energy3_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy3
      (fixedKineticSchwartzConcentration244 t ht f) =
      t ^ 12 * lowNormalRealSchwartzH3Energy3 f := by
  unfold fixedKineticSchwartzConcentration244
  rw [fixedKinetic_thirdEnergy_real_smul244,
    lowNormalRealSchwartzH3Energy3_dilation]
  have hn : t ≠ 0 := ne_of_gt ht
  field_simp [hn]

/-- Exact growth of the FULL physical normalized H³ energy, not just its
kinetic or top derivative block. The normalization 1 remains unchanged. -/
theorem fixedKineticSchwartzConcentration_fullEnergy_eq244
    (t : ℝ) (ht : 0 < t) (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy
      (fixedKineticSchwartzConcentration244 t ht f) =
        1 + lowNormalRealSchwartzH3Energy0 f +
          t ^ 4 * lowNormalRealSchwartzH3Energy1 f +
          t ^ 8 * lowNormalRealSchwartzH3Energy2 f +
          t ^ 12 * lowNormalRealSchwartzH3Energy3 f := by
  unfold lowNormalRealSchwartzH3Energy
  rw [fixedKineticSchwartzConcentration_energy0_eq244,
    fixedKineticSchwartzConcentration_energy1_eq244,
    fixedKineticSchwartzConcentration_energy2_eq244,
    fixedKineticSchwartzConcentration_energy3_eq244]

/-- The scalar exponent barrier is independent of Schwartz elaboration.
At t>=1 every lower-order energy grows no faster than t^16, whereas
M grows as t^17. Absolute values allow arbitrary real coefficients. -/
private theorem fixedKinetic_fullH3_scalar_absorption244
    (M D E0 E1 E2 E3 C K t : ℝ)
    (ht : 1 ≤ t)
    (hBudget : |C * D| +
      |K| * (1 + |E0| + |E1| + |E2| + |E3|) < t * M) :
    C * (t ^ 16 * D) +
      K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) <
        t ^ 17 * M := by
  have h16 : 1 ≤ t ^ 16 := one_le_pow₀ ht
  have hpos : 0 < t ^ 16 := lt_of_lt_of_le zero_lt_one h16
  have h4 : t ^ 4 ≤ t ^ 16 :=
    pow_le_pow_right₀ ht (by norm_num : (4 : ℕ) ≤ 16)
  have h8 : t ^ 8 ≤ t ^ 16 :=
    pow_le_pow_right₀ ht (by norm_num : (8 : ℕ) ≤ 16)
  have h12 : t ^ 12 ≤ t ^ 16 :=
    pow_le_pow_right₀ ht (by norm_num : (12 : ℕ) ≤ 16)
  have h0 : (t : ℝ) ^ 0 ≤ t ^ 16 := by simpa only [pow_zero] using h16
  have hTerm (p : ℕ) (E : ℝ) (hp : t ^ p ≤ t ^ 16) :
      K * (t ^ p * E) ≤ t ^ 16 * (|K| * |E|) := by
    calc
      K * (t ^ p * E) = t ^ p * (K * E) := by ring
      _ ≤ t ^ p * |K * E| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg (le_trans zero_le_one ht) _)
      _ = t ^ p * (|K| * |E|) := by rw [abs_mul]
      _ ≤ t ^ 16 * (|K| * |E|) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hC : C * (t ^ 16 * D) ≤ t ^ 16 * |C * D| := by
    calc
      C * (t ^ 16 * D) = t ^ 16 * (C * D) := by ring
      _ ≤ t ^ 16 * |C * D| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (le_trans zero_le_one h16)
  have hK : K ≤ t ^ 16 * |K| := by
    calc
      K ≤ |K| := le_abs_self _
      _ = 1 * |K| := by ring
      _ ≤ t ^ 16 * |K| := mul_le_mul_of_nonneg_right h16 (abs_nonneg _)
  have hE0 : K * E0 ≤ t ^ 16 * (|K| * |E0|) := by
    simpa only [pow_zero, one_mul] using hTerm 0 E0 h0
  have hE1 := hTerm 4 E1 h4
  have hE2 := hTerm 8 E2 h8
  have hE3 := hTerm 12 E3 h12
  have hMajor :
      C * (t ^ 16 * D) +
          K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) ≤
        t ^ 16 * (|C * D| +
          |K| * (1 + |E0| + |E1| + |E2| + |E3|)) := by
    calc
      _ = C * (t ^ 16 * D) + K + K * E0 + K * (t ^ 4 * E1) +
          K * (t ^ 8 * E2) + K * (t ^ 12 * E3) := by ring
      _ ≤ t ^ 16 * |C * D| + t ^ 16 * |K| +
          t ^ 16 * (|K| * |E0|) + t ^ 16 * (|K| * |E1|) +
          t ^ 16 * (|K| * |E2|) + t ^ 16 * (|K| * |E3|) := by
        linarith only [hC, hK, hE0, hE1, hE2, hE3]
      _ = _ := by ring
  calc
    _ ≤ t ^ 16 * (|C * D| +
          |K| * (1 + |E0| + |E1| + |E2| + |E3|)) := hMajor
    _ < t ^ 16 * (t * M) := mul_lt_mul_of_pos_left hBudget hpos
    _ = t ^ 17 * M := by ring

/-- The stronger fixed-kinetic obstruction: even an arbitrary multiple of
THE ENTIRE normalized H³ energy cannot absorb the positive monomial.
This is an exact physical Schwartz theorem with no extra smoothness or
nonlinear approximation assumption. -/
theorem fixedKineticSchwartzConcentration_exceeds_fullH3_absorption244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (C K : ℝ) :
    ∃ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g ∧
      lowNormalRealSchwartzH3Energy0 g = lowNormalRealSchwartzH3Energy0 f ∧
      0 < lowNormalRealSchwartzPoint3Monomial g ∧
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy g <
          lowNormalRealSchwartzPoint3Monomial g := by
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let D : ℝ := lowNormalRealSchwartzH3TopDissipation f
  let E0 : ℝ := lowNormalRealSchwartzH3Energy0 f
  let E1 : ℝ := lowNormalRealSchwartzH3Energy1 f
  let E2 : ℝ := lowNormalRealSchwartzH3Energy2 f
  let E3 : ℝ := lowNormalRealSchwartzH3Energy3 f
  have hMpos : 0 < M := hM
  let A : ℝ := |C * D| + |K| * (1 + |E0| + |E1| + |E2| + |E3|)
  let t : ℝ := (A + 1) / M + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have htOne : 1 ≤ t := by
    dsimp [t]
    have hnonneg : 0 ≤ (A + 1) / M :=
      div_nonneg (add_nonneg hA (by norm_num)) hMpos.le
    linarith
  have hBudget : A < t * M := by
    dsimp [t]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hMpos), one_mul]
    linarith only [hMpos]
  have hScalar :
      C * (t ^ 16 * D) +
        K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) <
          t ^ 17 * M := by
    apply fixedKinetic_fullH3_scalar_absorption244 M D E0 E1 E2 E3 C K t htOne
    exact hBudget
  let g : A3 → SchwartzMap V3 ℝ := fixedKineticSchwartzConcentration244 t ht f
  have hSol : lowNormalRealSchwartz_Point3Solenoidal g :=
    fixedKineticSchwartzConcentration_solenoidal244 t ht f hDiv
  have hMass : lowNormalRealSchwartzH3Energy0 g = E0 :=
    fixedKineticSchwartzConcentration_energy0_eq244 t ht f
  have hTop : lowNormalRealSchwartzH3TopDissipation g = t ^ 16 * D :=
    fixedKineticSchwartzConcentration_dissipation_eq244 t ht f
  have hMon : lowNormalRealSchwartzPoint3Monomial g = t ^ 17 * M :=
    fixedKineticSchwartzConcentration_monomial_eq244 t ht f
  have hFull : lowNormalRealSchwartzH3Energy g =
      1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3 :=
    fixedKineticSchwartzConcentration_fullEnergy_eq244 t ht f
  have hAbsorb :
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy g <
          lowNormalRealSchwartzPoint3Monomial g := by
    calc
      _ = C * (t ^ 16 * D) +
            K * (1 + E0 + t ^ 4 * E1 + t ^ 8 * E2 + t ^ 12 * E3) := by
        rw [hTop, hFull]
      _ < t ^ 17 * M := hScalar
      _ = lowNormalRealSchwartzPoint3Monomial g := hMon.symm
  have hPositive : 0 < lowNormalRealSchwartzPoint3Monomial g := by
    rw [hMon]
    exact mul_pos (pow_pos ht 17) hMpos
  exact ⟨g, hSol, hMass, hPositive, hAbsorb⟩

/-- Unconditional quarter-packet witness for every real pair C,K. Both
Schwartz velocities are physically divergence-free and share EXACT E0. -/
theorem lowNormalQuarter_exists_fixedKinetic_fullH3_absorption_counterexample244
    (C K : ℝ) :
    ∃ f g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal f ∧
      lowNormalRealSchwartz_Point3Solenoidal g ∧
      0 < lowNormalRealSchwartzPoint3Monomial f ∧
      lowNormalRealSchwartzH3Energy0 g = lowNormalRealSchwartzH3Energy0 f ∧
      0 < lowNormalRealSchwartzPoint3Monomial g ∧
      C * lowNormalRealSchwartzH3TopDissipation g +
        K * lowNormalRealSchwartzH3Energy g <
          lowNormalRealSchwartzPoint3Monomial g := by
  obtain ⟨ρ, hρ, _, hM⟩ :=
    lowNormalQuarterPoint3_exists_both_firstMonomial_signs
  let f : A3 → SchwartzMap V3 ℝ := lowNormalQuarterOppositeSchwartzVelocity ρ hρ
  have hDiv : lowNormalRealSchwartz_Point3Solenoidal f :=
    lowNormalQuarterOppositeSchwartz_Point3Solenoidal244 ρ hρ
  obtain ⟨g, hgDiv, hgE0, hgPositive, hgBound⟩ :=
    fixedKineticSchwartzConcentration_exceeds_fullH3_absorption244
      f hDiv hM C K
  exact ⟨f, g, hDiv, hgDiv, hM, hgE0, hgPositive, hgBound⟩


/-- The exact transport decomposition on physical H³ paths is T₃=G₃+3M.
Consequently, IF a full-transport upper absorption bound were to hold at
one of these concentrated Schwartz snapshots, its independent gradient block
would have to be strongly negative, canceling MORE THAN TWO of the THREE
copies of the positive interpolation monomial. This is a conditional
NECESSARY cancellation statement; it does not establish the physical
Schwartz snapshot is attained by a Navier--Stokes path. -/
theorem lowNormalQuarter_fixedKinetic_forces_gradient_compensation244
    (C K : ℝ) :
    ∃ f g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal f ∧
      lowNormalRealSchwartz_Point3Solenoidal g ∧
      lowNormalRealSchwartzH3Energy0 g = lowNormalRealSchwartzH3Energy0 f ∧
      0 < lowNormalRealSchwartzPoint3Monomial g ∧
      (∀ G : ℝ,
        G + 3 * lowNormalRealSchwartzPoint3Monomial g ≤
          C * lowNormalRealSchwartzH3TopDissipation g +
            K * lowNormalRealSchwartzH3Energy g →
        G < -2 * lowNormalRealSchwartzPoint3Monomial g) := by
  obtain ⟨f, g, hf, hg, _, hE0, hMg, hExcess⟩ :=
    lowNormalQuarter_exists_fixedKinetic_fullH3_absorption_counterexample244 C K
  refine ⟨f, g, hf, hg, hE0, hMg, ?_⟩
  intro G hTransport
  linarith only [hTransport, hExcess]

end
end PrimeTensor.FirstMonomialTriad
