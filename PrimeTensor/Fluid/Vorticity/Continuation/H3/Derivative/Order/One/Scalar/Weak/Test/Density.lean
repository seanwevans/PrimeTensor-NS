import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Weak.First.Jet.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Schwartz.Dense
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Compact
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Scalar weak tests are dense in physical L²

The weak first-jet derivative theorem from
`H3PathOrderOneSelectedWeakFirstJetDerivative` is stated against the project's
compact smooth scalar tests.  To turn those scalar identities into Hilbert
identities, we need only the standard density statement

    range h3WeakTestFunctionPhysicalL2  dense in  H3ScalarL2.

The repository already proves that physical real Schwartz functions are dense
in `H3ScalarL2`.  This file adds the elementary compact-cutoff step directly on
`Point3`:

* multiply a physical Schwartz function by an expanding smooth bump;
* package the compact product as an actual `H3WeakTestFunction`;
* prove the cutoff converges in physical `L²` by dominated convergence;
* conclude every Schwartz `L²` class lies in the closure of the weak-test
  image.

Combining this with existing Schwartz density closes scalar weak-test density
outright.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneScalarWeakTestDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneScalarWeakTestDensity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Expanding smooth cutoff on the physical carrier. -/
noncomputable def h3OrderOneScalarWeakCutoffBump
    (n : ℕ) :
    ContDiffBump (0 : Point3) where
  rIn := (n : ℝ) + 1
  rOut := 2 * ((n : ℝ) + 1)
  rIn_pos := by
    positivity
  rIn_lt_rOut := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith

@[simp]
theorem h3OrderOneScalarWeakCutoffBump_rIn
    (n : ℕ) :
    (h3OrderOneScalarWeakCutoffBump n).rIn
      =
    (n : ℝ) + 1 := by
  rfl

theorem h3OrderOneScalarWeakCutoffBump_nonneg
    (n : ℕ)
    (x : Point3) :
    0 ≤ h3OrderOneScalarWeakCutoffBump n x :=
  (h3OrderOneScalarWeakCutoffBump n).nonneg

theorem h3OrderOneScalarWeakCutoffBump_le_one
    (n : ℕ)
    (x : Point3) :
    h3OrderOneScalarWeakCutoffBump n x ≤ 1 :=
  (h3OrderOneScalarWeakCutoffBump n).le_one

theorem h3OrderOneScalarWeakCutoffBump_hasCompactSupport
    (n : ℕ) :
    HasCompactSupport
      (h3OrderOneScalarWeakCutoffBump n :
        Point3 → ℝ) :=
  (h3OrderOneScalarWeakCutoffBump n).hasCompactSupport

theorem h3OrderOneScalarWeakCutoffBump_contDiff
    (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (h3OrderOneScalarWeakCutoffBump n :
        Point3 → ℝ) := by
  simpa using
    ((h3OrderOneScalarWeakCutoffBump n).contDiff
      (n := (⊤ : ℕ∞)))

theorem h3OrderOneScalarWeakCutoffBump_eq_one_of_norm_le
    (n : ℕ)
    {x : Point3}
    (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    h3OrderOneScalarWeakCutoffBump n x = 1 := by
  apply (h3OrderOneScalarWeakCutoffBump n).one_of_mem_closedBall

  simpa only [
    Metric.mem_closedBall,
    dist_zero_right,
    h3OrderOneScalarWeakCutoffBump_rIn
  ] using hx

/-- Compact physical Schwartz cutoff. -/
noncomputable def h3OrderOneScalarWeakCutoffSchwartz
    (n : ℕ)
    (φ : H3PhysicalScalarSchwartz) :
    H3PhysicalScalarSchwartz := by
  have hCompact :
      HasCompactSupport
        (fun x : Point3 =>
          h3OrderOneScalarWeakCutoffBump n x * φ x) :=
    (h3OrderOneScalarWeakCutoffBump_hasCompactSupport n).mul_right

  have hSmooth :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Point3 =>
          h3OrderOneScalarWeakCutoffBump n x * φ x) :=
    (h3OrderOneScalarWeakCutoffBump_contDiff n).mul
      (φ.smooth (⊤ : ℕ∞))

  exact
    hCompact.toSchwartzMap hSmooth

@[simp]
theorem h3OrderOneScalarWeakCutoffSchwartz_apply
    (n : ℕ)
    (φ : H3PhysicalScalarSchwartz)
    (x : Point3) :
    h3OrderOneScalarWeakCutoffSchwartz n φ x
      =
    h3OrderOneScalarWeakCutoffBump n x * φ x := by
  rfl

theorem h3OrderOneScalarWeakCutoffSchwartz_hasCompactSupport
    (n : ℕ)
    (φ : H3PhysicalScalarSchwartz) :
    HasCompactSupport
      (h3OrderOneScalarWeakCutoffSchwartz n φ :
        Point3 → ℝ) := by
  unfold h3OrderOneScalarWeakCutoffSchwartz

  exact
    (h3OrderOneScalarWeakCutoffBump_hasCompactSupport n).mul_right

/-- The physical cutoff is literally an admissible scalar weak test. -/
noncomputable def h3OrderOneScalarWeakCutoffWeakTest
    (n : ℕ)
    (φ : H3PhysicalScalarSchwartz) :
    H3WeakTestFunction :=
  h3CompactPhysicalSchwartzToWeakTest
    (h3OrderOneScalarWeakCutoffSchwartz n φ)
    (h3OrderOneScalarWeakCutoffSchwartz_hasCompactSupport n φ)

/-! ## Pointwise stabilization and domination -/

theorem h3OrderOneScalarWeakCutoffBump_eventually_eq_one
    (x : Point3) :
    ∀ᶠ n : ℕ in atTop,
      h3OrderOneScalarWeakCutoffBump n x = 1 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge ‖x‖

  filter_upwards [eventually_ge_atTop N] with n hn

  apply h3OrderOneScalarWeakCutoffBump_eq_one_of_norm_le

  calc
    ‖x‖ ≤ (N : ℝ) := hN
    _ ≤ (n : ℝ) := by
      exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by
      linarith

theorem h3OrderOneScalarWeakCutoffSchwartz_eventually_eq
    (φ : H3PhysicalScalarSchwartz)
    (x : Point3) :
    ∀ᶠ n : ℕ in atTop,
      h3OrderOneScalarWeakCutoffSchwartz n φ x = φ x := by
  filter_upwards [
    h3OrderOneScalarWeakCutoffBump_eventually_eq_one x
  ] with n hn

  rw [
    h3OrderOneScalarWeakCutoffSchwartz_apply,
    hn,
    one_mul
  ]

theorem norm_h3OrderOneScalarWeakCutoffSchwartz_sub_le
    (n : ℕ)
    (φ : H3PhysicalScalarSchwartz)
    (x : Point3) :
    ‖h3OrderOneScalarWeakCutoffSchwartz n φ x - φ x‖
      ≤
    ‖φ x‖ := by
  have hχ0 :
      0 ≤ h3OrderOneScalarWeakCutoffBump n x :=
    h3OrderOneScalarWeakCutoffBump_nonneg n x

  have hχ1 :
      h3OrderOneScalarWeakCutoffBump n x ≤ 1 :=
    h3OrderOneScalarWeakCutoffBump_le_one n x

  rw [h3OrderOneScalarWeakCutoffSchwartz_apply]

  have hRewrite :
      h3OrderOneScalarWeakCutoffBump n x * φ x - φ x
        =
      (h3OrderOneScalarWeakCutoffBump n x - 1) * φ x := by
    ring

  rw [hRewrite, norm_mul]

  have hAbs :
      |h3OrderOneScalarWeakCutoffBump n x - 1|
        =
      1 - h3OrderOneScalarWeakCutoffBump n x := by
    rw [abs_of_nonpos]
    · ring
    · linarith

  rw [Real.norm_eq_abs, hAbs]

  calc
    (1 - h3OrderOneScalarWeakCutoffBump n x) * |φ x|
        ≤
      1 * |φ x| := by
        gcongr
        linarith
    _ = |φ x| := by
      ring

theorem enorm_h3OrderOneScalarWeakCutoffSchwartz_sub_le
    (n : ℕ)
    (φ : H3PhysicalScalarSchwartz)
    (x : Point3) :
    ‖h3OrderOneScalarWeakCutoffSchwartz n φ x - φ x‖ₑ
      ≤
    ‖φ x‖ₑ := by
  rw [enorm_le_iff_norm_le]

  exact
    norm_h3OrderOneScalarWeakCutoffSchwartz_sub_le n φ x

/-! ## Physical L² convergence -/

theorem h3OrderOneScalarWeakCutoffSchwartz_tendsto_eLpNorm_two
    (φ : H3PhysicalScalarSchwartz) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x : Point3 =>
            h3OrderOneScalarWeakCutoffSchwartz n φ x - φ x)
          2
          (volume : Measure Point3))
      atTop
      (𝓝 0) := by
  have hpZero :
      (2 : ℝ≥0∞) ≠ 0 := by
    norm_num

  have hpTop :
      (2 : ℝ≥0∞) ≠ ∞ := by
    norm_num

  have hpPos :
      0 < (2 : ℝ≥0∞).toReal :=
    ENNReal.toReal_pos hpZero hpTop

  suffices hIntegral :
      Tendsto
        (fun n : ℕ =>
          ∫⁻ x : Point3,
            ‖h3OrderOneScalarWeakCutoffSchwartz n φ x - φ x‖ₑ
                ^ (2 : ℝ≥0∞).toReal
            ∂volume)
        atTop
        (𝓝 0) by
    simp only [
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        hpZero
        hpTop
    ]

    have hPow :
        Tendsto
          (fun z : ℝ≥0∞ =>
            z ^ (1 / (2 : ℝ≥0∞).toReal))
          (𝓝 0)
          (𝓝
            ((0 : ℝ≥0∞) ^
              (1 / (2 : ℝ≥0∞).toReal))) :=
      ENNReal.continuous_rpow_const.tendsto 0

    have hComposed :=
      hPow.comp hIntegral

    have hExponentPos :
        0 < 1 / (2 : ℝ≥0∞).toReal := by
      simpa [one_div] using
        (_root_.inv_pos.mpr hpPos)

    have hZeroPow :
        (0 : ℝ≥0∞) ^
            (1 / (2 : ℝ≥0∞).toReal)
          =
        0 :=
      ENNReal.zero_rpow_of_pos hExponentPos

    rw [hZeroPow] at hComposed

    simpa only [Function.comp_def] using hComposed

  have hFMeas :
      ∀ n : ℕ,
        Measurable
          (fun x : Point3 =>
            ‖h3OrderOneScalarWeakCutoffSchwartz n φ x - φ x‖ₑ
              ^ (2 : ℝ≥0∞).toReal) := by
    intro n

    exact
      (((h3OrderOneScalarWeakCutoffSchwartz n φ).continuous.measurable.sub
          φ.continuous.measurable).enorm.pow_const
        (2 : ℝ≥0∞).toReal)

  have hBound :
      ∀ n : ℕ,
        (fun x : Point3 =>
          ‖h3OrderOneScalarWeakCutoffSchwartz n φ x - φ x‖ₑ
            ^ (2 : ℝ≥0∞).toReal)
          ≤ᵐ[volume]
        (fun x : Point3 =>
          ‖φ x‖ₑ ^ (2 : ℝ≥0∞).toReal) := by
    intro n

    exact
      Filter.Eventually.of_forall
        (fun x =>
          ENNReal.rpow_le_rpow
            (enorm_h3OrderOneScalarWeakCutoffSchwartz_sub_le n φ x)
            ENNReal.toReal_nonneg)

  have hφMemLp :
      MemLp
        (φ : Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    φ.memLp 2 volume

  have hFinite :
      (∫⁻ x : Point3,
        ‖φ x‖ₑ ^ (2 : ℝ≥0∞).toReal
        ∂volume)
        ≠
      ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      hpZero
      hpTop
      hφMemLp.2).ne

  have hLimit :
      ∀ᵐ x : Point3 ∂volume,
        Tendsto
          (fun n : ℕ =>
            ‖h3OrderOneScalarWeakCutoffSchwartz n φ x - φ x‖ₑ
              ^ (2 : ℝ≥0∞).toReal)
          atTop
          (𝓝 0) := by
    filter_upwards with x

    refine (tendsto_congr' ?_).2 tendsto_const_nhds

    filter_upwards [
      h3OrderOneScalarWeakCutoffSchwartz_eventually_eq φ x
    ] with n hn

    rw [hn, sub_self]

    simp

  simpa using
    (tendsto_lintegral_of_dominated_convergence
      (fun x : Point3 =>
        ‖φ x‖ₑ ^ (2 : ℝ≥0∞).toReal)
      hFMeas
      hBound
      hFinite
      hLimit)

theorem h3OrderOneScalarWeakCutoffSchwartzPhysicalL2_tendsto
    (φ : H3PhysicalScalarSchwartz) :
    Tendsto
      (fun n : ℕ =>
        h3ScalarSchwartzPhysicalL2
          (h3OrderOneScalarWeakCutoffSchwartz n φ))
      atTop
      (𝓝 (h3ScalarSchwartzPhysicalL2 φ)) := by
  have hRaw :=
    h3OrderOneScalarWeakCutoffSchwartz_tendsto_eLpNorm_two φ

  have hCutMem :
      ∀ n : ℕ,
        MemLp
          (h3OrderOneScalarWeakCutoffSchwartz n φ :
            Point3 → ℝ)
          2
          (volume : Measure Point3) :=
    fun n =>
      (h3OrderOneScalarWeakCutoffSchwartz n φ).memLp 2 volume

  have hφMem :
      MemLp
        (φ : Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    φ.memLp 2 volume

  unfold h3ScalarSchwartzPhysicalL2
  simp only [SchwartzMap.toLpCLM_apply]
  unfold SchwartzMap.toLp

  exact
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n : ℕ =>
        (h3OrderOneScalarWeakCutoffSchwartz n φ :
          Point3 → ℝ))
      hCutMem
      (φ : Point3 → ℝ)
      hφMem).2
      hRaw

/-- The weak-test physical L² package of a cutoff is exactly the Schwartz
physical L² package of that same cutoff. -/
theorem h3WeakTestFunctionPhysicalL2_orderOneCutoff_eq
    (n : ℕ)
    (φ : H3PhysicalScalarSchwartz) :
    h3WeakTestFunctionPhysicalL2
        (h3OrderOneScalarWeakCutoffWeakTest n φ)
      =
    h3ScalarSchwartzPhysicalL2
      (h3OrderOneScalarWeakCutoffSchwartz n φ) := by
  apply MeasureTheory.Lp.ext

  have hWeak :=
    h3WeakTestFunctionPhysicalL2_ae
      (h3OrderOneScalarWeakCutoffWeakTest n φ)

  have hSchwartz :
      (((h3ScalarSchwartzPhysicalL2
            (h3OrderOneScalarWeakCutoffSchwartz n φ) :
          H3ScalarL2) :
        Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (h3OrderOneScalarWeakCutoffSchwartz n φ :
        Point3 → ℝ)) := by
    unfold h3ScalarSchwartzPhysicalL2
    simp only [SchwartzMap.toLpCLM_apply]

    exact
      (h3OrderOneScalarWeakCutoffSchwartz n φ).coeFn_toLp
        2
        (volume : Measure Point3)

  filter_upwards [hWeak, hSchwartz] with x hxWeak hxSchwartz

  rw [hxWeak, hxSchwartz]

  rfl

/-- Every physical Schwartz L² state is a limit of genuine compact smooth weak
tests. -/
theorem h3OrderOneScalarWeakCutoffWeakTestPhysicalL2_tendsto
    (φ : H3PhysicalScalarSchwartz) :
    Tendsto
      (fun n : ℕ =>
        h3WeakTestFunctionPhysicalL2
          (h3OrderOneScalarWeakCutoffWeakTest n φ))
      atTop
      (𝓝 (h3ScalarSchwartzPhysicalL2 φ)) := by
  have h :=
    h3OrderOneScalarWeakCutoffSchwartzPhysicalL2_tendsto φ

  have hEq :
      (fun n : ℕ =>
        h3WeakTestFunctionPhysicalL2
          (h3OrderOneScalarWeakCutoffWeakTest n φ))
        =
      (fun n : ℕ =>
        h3ScalarSchwartzPhysicalL2
          (h3OrderOneScalarWeakCutoffSchwartz n φ)) := by
    funext n

    exact
      h3WeakTestFunctionPhysicalL2_orderOneCutoff_eq n φ

  rw [hEq]

  exact h

theorem h3ScalarSchwartzPhysicalL2_mem_closure_range_h3WeakTestFunctionPhysicalL2
    (φ : H3PhysicalScalarSchwartz) :
    h3ScalarSchwartzPhysicalL2 φ
      ∈
    closure
      (Set.range h3WeakTestFunctionPhysicalL2) := by
  exact
    mem_closure_of_tendsto
      (h3OrderOneScalarWeakCutoffWeakTestPhysicalL2_tendsto φ)
      (Eventually.of_forall
        (fun n =>
          ⟨
            h3OrderOneScalarWeakCutoffWeakTest n φ,
            rfl
          ⟩))

/-- Compact smooth scalar weak tests are dense in the complete physical
`L²(Point3)` Hilbert space. -/
theorem denseRange_h3WeakTestFunctionPhysicalL2_orderOne :
    DenseRange h3WeakTestFunctionPhysicalL2 := by
  rw [denseRange_iff_closure_range]

  apply Set.eq_univ_iff_forall.2
  intro F

  have hSchwartzDense :
      closure
          (Set.range h3ScalarSchwartzPhysicalL2)
        =
      (Set.univ : Set H3ScalarL2) :=
    denseRange_h3ScalarSchwartzPhysicalL2.closure_range

  have hRangeSubset :
      Set.range h3ScalarSchwartzPhysicalL2
        ⊆
      closure
        (Set.range h3WeakTestFunctionPhysicalL2) := by
    intro G hG
    rcases hG with ⟨φ, rfl⟩

    exact
      h3ScalarSchwartzPhysicalL2_mem_closure_range_h3WeakTestFunctionPhysicalL2
        φ

  have hClosureSubset :
      closure
          (Set.range h3ScalarSchwartzPhysicalL2)
        ⊆
      closure
          (Set.range h3WeakTestFunctionPhysicalL2) :=
    closure_minimal
      hRangeSubset
      isClosed_closure

  rw [hSchwartzDense] at hClosureSubset

  exact
    hClosureSubset
      (Set.mem_univ F)

end

end Euclidean
end Bridge
end PrimeTensor
