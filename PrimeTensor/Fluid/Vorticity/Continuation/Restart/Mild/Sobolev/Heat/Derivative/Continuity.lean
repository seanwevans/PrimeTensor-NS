import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Bilinear

/-!
# Positive-time strong continuity of the H³ heat-derivative multiplier

The retarded Duhamel kernel contains

    ∂ⱼ e^{ν t Δ}

at positive elapsed time.  Its norm has the expected `t⁻¹/²` singularity at
`t = 0`, but on the open half-line `t > 0` the operator is strongly continuous.

Rather than repeat the dominated-convergence proof already used for the heat
semigroup, we factor around a fixed positive time.  The Fourier symbols satisfy

    m_{a+b} = m_b m_a,

hence

    ∂ⱼ e^{ν(a+b)Δ} G
      = e^{νbΔ} (∂ⱼ e^{νaΔ} G)

for `a > 0` and `b ≥ 0`.

Near any `t₀ > 0`, choose `a = t₀ / 2`.  Then `t - a` stays nonnegative in a
neighborhood of `t₀`, while the inner derivative-heat datum at time `a` is
fixed.  Strong continuity therefore follows directly from the already-proved
nonnegative-time heat-semigroup continuity.

The zero-extended wrapper introduced below is the exact scalar building block
needed for the retarded path-integrability theorem.  It is not claimed to be
continuous at zero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3HeatDerivativeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Heat-symbol semigroup algebra -/

/-- The scalar Fourier heat symbol multiplies under time addition. -/
theorem h3HeatFourierSymbol_add
    (ν a b : ℝ)
    (ξ : H3FourierPoint3) :
    h3HeatFourierSymbol ν (a + b) ξ
      =
    h3HeatFourierSymbol ν b ξ *
      h3HeatFourierSymbol ν a ξ := by
  unfold h3HeatFourierSymbol
  have harg :
      -((2 * Real.pi) ^ 2 * ν * (a + b) * ‖ξ‖ ^ 2)
        =
      -((2 * Real.pi) ^ 2 * ν * b * ‖ξ‖ ^ 2) +
        -((2 * Real.pi) ^ 2 * ν * a * ‖ξ‖ ^ 2) := by
    ring
  rw [harg, Real.exp_add]
  simp

/-- The directional derivative-heat symbol factors through any positive first time. -/
theorem h3HeatDerivativeSymbol_add
    (ν a b : ℝ)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3HeatDerivativeSymbol ν (a + b) j ξ
      =
    h3HeatFourierSymbol ν b ξ *
      h3HeatDerivativeSymbol ν a j ξ := by
  unfold h3HeatDerivativeSymbol
  rw [h3HeatFourierSymbol_add]
  ring

/-! ## Operator semigroup factorization -/

/--
At positive first time `a` and nonnegative additional time `b`, one
heat-derivative application at `a+b` equals ordinary heat evolution for `b`
applied to the fixed heat-derivative state at `a`.
-/
theorem h3SpectralScalarHeatDerivativeApply_add_time
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatDerivativeApply
        ν (a + b) hν
        (add_pos_of_pos_of_nonneg ha hb)
        j G
      =
    h3SpectralScalarHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralScalarHeatDerivativeApply
          ν a hν ha j G) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarHeatDerivativeApply_ae
      hν (add_pos_of_pos_of_nonneg ha hb) j G,
    h3HeatFrequencyApplyNN_coeFn
      ν (le_of_lt hν) (NNReal.mk b hb)
      (h3SpectralScalarHeatDerivativeApply
        ν a hν ha j G),
    h3SpectralScalarHeatDerivativeApply_ae
      hν ha j G
  ] with ξ hleft hheat hinner
  change
    (h3SpectralScalarHeatDerivativeApply
        ν (a + b) hν
        (add_pos_of_pos_of_nonneg ha hb)
        j G :
      H3FourierPoint3 → ℂ) ξ
      =
    (h3HeatFrequencyApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralScalarHeatDerivativeApply
          ν a hν ha j G) :
      H3FourierPoint3 → ℂ) ξ
  rw [hleft, hheat, hinner,
    h3HeatDerivativeSymbol_add]
  simp only [NNReal.coe_mk]
  ring

/-! ## Zero extension and positive-time continuity -/

/--
Zero-extended scalar heat-derivative operator.

The actual retarded Duhamel integrand uses precisely this convention at
nonpositive lag.  The extension is continuous at every positive time, while no
continuity assertion is made at the singular endpoint `t = 0`.
-/
noncomputable def h3SpectralScalarHeatDerivativeApplyZero
    (ν t : ℝ)
    (hν : 0 < ν)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    H3SpectralScalarState :=
  if ht : 0 < t then
    h3SpectralScalarHeatDerivativeApply
      ν t hν ht j G
  else
    0

@[simp]
theorem h3SpectralScalarHeatDerivativeApplyZero_of_pos
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatDerivativeApplyZero
        ν t hν j G
      =
    h3SpectralScalarHeatDerivativeApply
        ν t hν ht j G := by
  simp [h3SpectralScalarHeatDerivativeApplyZero, ht]

@[simp]
theorem h3SpectralScalarHeatDerivativeApplyZero_of_nonpos
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : ¬ 0 < t)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatDerivativeApplyZero
        ν t hν j G
      =
    0 := by
  simp [h3SpectralScalarHeatDerivativeApplyZero, ht]

/--
The zero-extended heat-derivative operator is strongly continuous at every
strictly positive time.
-/
theorem continuousAt_h3SpectralScalarHeatDerivativeApplyZero
    {ν t₀ : ℝ}
    (hν : 0 < ν)
    (ht₀ : 0 < t₀)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    ContinuousAt
      (fun t : ℝ =>
        h3SpectralScalarHeatDerivativeApplyZero
          ν t hν j G)
      t₀ := by
  let a : ℝ := t₀ / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith

  have hat₀ : a < t₀ := by
    dsimp [a]
    linarith

  let F : H3SpectralScalarState :=
    h3SpectralScalarHeatDerivativeApply
      ν a hν ha j G

  have htime :
      Continuous
        (fun t : ℝ =>
          Real.toNNReal (t - a)) := by
    exact
      continuous_real_toNNReal.comp
        (continuous_id.sub continuous_const)

  have hrhs :
      Continuous
        (fun t : ℝ =>
          h3SpectralScalarHeatApplyNN
            ν (le_of_lt hν)
            (Real.toNNReal (t - a))
            F) := by
    exact
      (continuous_h3SpectralScalarHeatApplyNN
        ν (le_of_lt hν) F).comp htime

  have hnear :
      Set.Ioi a ∈ 𝓝 t₀ :=
    Ioi_mem_nhds hat₀

  have hEq :
      (fun t : ℝ =>
        h3SpectralScalarHeatDerivativeApplyZero
          ν t hν j G)
        =ᶠ[𝓝 t₀]
      (fun t : ℝ =>
        h3SpectralScalarHeatApplyNN
          ν (le_of_lt hν)
          (Real.toNNReal (t - a))
          F) := by
    filter_upwards [hnear] with t hat
    have ht : 0 < t :=
      lt_trans ha hat

    have hb : 0 ≤ t - a :=
      sub_nonneg.mpr hat.le

    have hfac :=
      h3SpectralScalarHeatDerivativeApply_add_time
        (ν := ν)
        (a := a)
        (b := t - a)
        hν ha hb j G

    have hsum :
        a + (t - a) = t := by
      ring

    have hnn :
        Real.toNNReal (t - a) =
          NNReal.mk (t - a) hb :=
      Real.toNNReal_of_nonneg hb

    calc
      h3SpectralScalarHeatDerivativeApplyZero
          ν t hν j G
          =
        h3SpectralScalarHeatDerivativeApply
          ν t hν ht j G := by
            exact
              h3SpectralScalarHeatDerivativeApplyZero_of_pos
                hν ht j G
      _ =
        h3SpectralScalarHeatApplyNN
          ν (le_of_lt hν)
          (NNReal.mk (t - a) hb)
          F := by
            simpa only [hsum, F] using hfac
      _ =
        h3SpectralScalarHeatApplyNN
          ν (le_of_lt hν)
          (Real.toNNReal (t - a))
          F := by
            rw [hnn]

  exact
    hrhs.continuousAt.congr_of_eventuallyEq hEq

/-- Positive-time strong continuity on the whole open half-line. -/
theorem continuousOn_h3SpectralScalarHeatDerivativeApplyZero
    {ν : ℝ}
    (hν : 0 < ν)
    (j : Fin 3)
    (G : H3SpectralScalarState) :
    ContinuousOn
      (fun t : ℝ =>
        h3SpectralScalarHeatDerivativeApplyZero
          ν t hν j G)
      (Set.Ioi (0 : ℝ)) := by
  intro t ht
  exact
    (continuousAt_h3SpectralScalarHeatDerivativeApplyZero
      hν ht j G).continuousWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
