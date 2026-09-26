import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualBoundedStrongH3Geometry

/-!
# Strong H³ endpoint control excludes the terminal derivative blowup sequence

The previous reductions showed that strong spectral H³ endpoint control supplies
all of the terminal temporal/spatial moduli needed by the bounded-branch
geometry.

There is a stronger consequence.

The six terminal curl/gradient pairs come in three swapped pairs:

    x_yz ↔ x_zy
    y_zx ↔ y_xz
    z_xy ↔ z_yx.

For each pair `p`, the selected constituent gradient of `p` is exactly the
complementary derivative of the swapped pair.

Hypothetical nonextension already gives one fixed pair `p`, one selected
spacetime sequence `(τ n, x n)`, and one orientation in which that selected
constituent gradient tends to `+∞`.

If every pair has strong H³ endpoint control on every strict selected terminal
sequence, apply it instead to `swap p` along the same `τ`.  Strong H³
convergence makes the corresponding spectral scalar states eventually bounded.
The uniform first-derivative evaluation estimate then makes the complementary
derivative of `swap p` uniformly bounded at every spatial point, hence in
particular at `x n`.

But this complementary derivative is the selected constituent gradient of
`p`, contradicting its oriented divergence to `+∞`.

Thus the all-pairs/all-selected-sequences strong H³ endpoint criterion directly
forces smooth continuation.  Under this hypothesis the nonextension branches
of the terminal classification are empty.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalStrongEndpointContradiction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Swap the two constituent derivatives of one curl component -/

/--
Swap the two constituent derivatives belonging to the same vorticity
component.
-/
def h3TerminalSwapCurlGradientPair :
    H3TerminalCurlGradientPair →
      H3TerminalCurlGradientPair
  | .x_yz => .x_zy
  | .x_zy => .x_yz
  | .y_zx => .y_xz
  | .y_xz => .y_zx
  | .z_xy => .z_yx
  | .z_yx => .z_xy

@[simp]
theorem h3TerminalSwapCurlGradientPair_swap
    (p : H3TerminalCurlGradientPair) :
    h3TerminalSwapCurlGradientPair
        (h3TerminalSwapCurlGradientPair p)
      =
    p := by
  cases p <;> rfl

/--
The selected constituent gradient of a pair is exactly the complementary
gradient of its swapped pair.
-/
@[simp]
theorem h3TerminalComplementGradientFieldForPair_swap_eq_gradient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    h3TerminalComplementGradientFieldForPair
        u
        (h3TerminalSwapCurlGradientPair p)
        t x
      =
    h3TerminalGradientFieldForPair
        u p t x := by
  cases p <;> rfl

/-! ## Strong H³ endpoint control gives an eventual global derivative bound -/

/--
On any strict selected time sequence converging to `T`, strong H³ endpoint
control makes the complementary first derivative eventually bounded uniformly
in the selected spatial points.

The bound is global in space because first-derivative evaluation on weighted
spectral H³ is a bounded linear functional with a coefficient independent of
the evaluation point.
-/
theorem strongH3Endpoint_eventually_abs_complementGradient_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    {x : ℕ → Point3}
    {p : H3TerminalCurlGradientPair}
    (hStrong :
      H3TerminalComplementGradientSelectedStrongH3Endpoint
        hH3 hTauStrict p) :
    ∃ B : ℝ,
      ∀ᶠ n : ℕ in atTop,
        abs
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ n)
              (x n)
          )
          ≤ B := by

  obtain
    ⟨
      Ginf,
      _hTerminalRep,
      hStateModulus
    ⟩ :=
    hStrong

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementDerivativeAxisForPair p)

  let K : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  have hK :
      0 ≤ K := by

    dsimp only [K]

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  have hAxis :
      h3AxisOfFin3 i
        =
      h3TerminalComplementDerivativeAxisForPair p := by

    dsimp only [i]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
        (h3TerminalComplementDerivativeAxisForPair p)

  obtain
    ⟨
      η,
      hη,
      hStateClose
    ⟩ :=
    hStateModulus
      1
      zero_lt_one

  have hTauMetric := hTau

  rw [Metric.tendsto_atTop] at hTauMetric

  obtain
    ⟨
      N,
      hNear
    ⟩ :=
    hTauMetric
      η
      hη

  refine
    ⟨
      K * (1 + ‖Ginf‖),
      ?_
    ⟩

  filter_upwards
    [eventually_ge_atTop N]
    with n hn

  let Gn : H3SpectralScalarState :=
    h3TerminalSelectedComplementSpectralState
      hH3 hTauStrict p n

  have hClose :
      ‖Gn - Ginf‖ < 1 := by

    dsimp only [Gn]

    exact
      hStateClose
        n
        (hNear n hn)

  have hGn :
      ‖Gn‖ ≤ 1 + ‖Ginf‖ := by

    calc
      ‖Gn‖
          =
        ‖(Gn - Ginf) + Ginf‖ := by
          rw [sub_add_cancel]
      _ ≤
        ‖Gn - Ginf‖ + ‖Ginf‖ :=
          norm_add_le _ _
      _ ≤
        1 + ‖Ginf‖ := by
          linarith

  have hRep :
      h3SpectralScalarRealC1RepresentativeOnPoint3 Gn
        =
      loggedVelocityComponent
        u
        (τ n)
        (h3TerminalComplementComponentAxisForPair p) := by

    dsimp only [Gn]

    exact
      h3TerminalSelectedComplementSpectralState_representative_eq_loggedVelocityComponent
        hH3 hTauStrict p n

  have hRaw :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
      Gn
      i
      (x n)

  rw [hAxis] at hRaw

  have hDerivative :
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair p)
          (
            h3SpectralScalarRealC1RepresentativeOnPoint3
              Gn
          )
          (x n)
        =
      h3TerminalComplementGradientFieldForPair
        u p
        (τ n)
        (x n) := by

    rw [hRep]

    rfl

  have hFieldNorm :
      norm
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ n)
            (x n)
        )
        ≤
      K * ‖Gn‖ := by

    rw [← hDerivative]

    dsimp only [K]

    exact
      hRaw

  have hFinal :
      norm
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ n)
            (x n)
        )
        ≤
      K * (1 + ‖Ginf‖) :=
    hFieldNorm.trans
      (
        mul_le_mul_of_nonneg_left
          hGn
          hK
      )

  simpa only [
    Real.norm_eq_abs
  ] using
    hFinal

/-! ## Oriented values are controlled by absolute value -/

/--
Either orientation of a real scalar is bounded above by its absolute value.
-/
theorem h3TerminalOrientedValue_le_abs
    (s : H3TerminalOrientation)
    (z : ℝ) :
    h3TerminalOrientedValue s z
      ≤
    abs z := by

  cases s

  · exact
      le_abs_self z

  · exact
      neg_le_abs z

/-! ## Strong H³ endpoint control rules out nonextension -/

/--
If every fixed terminal pair has strong H³ endpoint control on every strict
selected terminal sequence, then an admissible H³ path in the high-order
energy class has a smooth continuation extension.

The contradiction uses the already-proved fixed-pair constituent-gradient
blowup sequence under hypothetical nonextension and applies strong H³ control
to the swapped pair on that same sequence.
-/
theorem smoothContinuationExtension_of_allPairs_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hAllStrong :
      ∀ p : H3TerminalCurlGradientPair,
        H3TerminalComplementGradientStrongH3EndpointOnAllSelectedTerminalSequences
          hH3 p) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  by_contra hNoExtension

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hBlowup
    ⟩ :=
    fixed_curl_constituentGradient_doubleOriented_samePoint_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTau,
      _hCurlTendsto,
      hGradientTendsto
    ⟩ :=
    hBlowup

  have hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T := by

    intro n

    have hTail :
        τ n ∈ Set.Ioo a T :=
      (hτ n).1

    exact
      ⟨
        lt_trans
          hClass.terminal_start.1
          hTail.1,
        hTail.2
      ⟩

  let q : H3TerminalCurlGradientPair :=
    h3TerminalSwapCurlGradientPair p

  have hStrong :
      H3TerminalComplementGradientSelectedStrongH3Endpoint
        hH3 hTauStrict q :=
    hAllStrong
      q
      τ
      hTauStrict
      hTau

  obtain
    ⟨
      B,
      hBound
    ⟩ :=
    strongH3Endpoint_eventually_abs_complementGradient_le
      hH3
      hTauStrict
      hTau
      (x := x)
      hStrong

  have hGradientBound :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalOrientedValue
            sGradient
            (
              h3TerminalGradientFieldForPair
                u p
                (τ n)
                (x n)
            )
          ≤
        B := by

    filter_upwards
      [hBound]
      with n hn

    have hEq :
        h3TerminalComplementGradientFieldForPair
            u q
            (τ n)
            (x n)
          =
        h3TerminalGradientFieldForPair
            u p
            (τ n)
            (x n) := by

      dsimp only [q]

      exact
        h3TerminalComplementGradientFieldForPair_swap_eq_gradient
          u p
          (τ n)
          (x n)

    have hAbs :
        abs
          (
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (x n)
          )
          ≤ B := by

      rw [← hEq]

      exact
        hn

    exact
      (
        h3TerminalOrientedValue_le_abs
          sGradient
          (
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (x n)
          )
      ).trans
        hAbs

  have hGradientLarge :
      ∀ᶠ n : ℕ in atTop,
        B <
          h3TerminalOrientedValue
            sGradient
            (
              h3TerminalGradientFieldForPair
                u p
                (τ n)
                (x n)
            ) :=
    hGradientTendsto.eventually
      (eventually_gt_atTop B)

  obtain
    ⟨
      n,
      hnBound,
      hnLarge
    ⟩ :=
    (hGradientBound.and hGradientLarge).exists

  exact
    (not_lt_of_ge hnBound)
      hnLarge

end

end Euclidean
end Bridge
end PrimeTensor
