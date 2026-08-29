import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Seventh.Endpoint.UniformFifthTailMass

/-!
# Fréchet endpoint induction: generic Fourier moment algebra

The fifth, sixth, and seventh endpoint layers all use the same exponent
geometry.  This file removes the named-exponent duplication and records that
geometry once for an arbitrary nonnegative real Fourier moment.

For a radial moment exponent `q`, define

    w_q(ξ) = ‖ξ‖^q.

The quadratic convolution split is uniform in `q ≥ 0`:

    w_q(ξ)
      ≤
    2^q (w_q(η) + w_q(ξ - η)).

For an integer bootstrap level `n ≥ 1`, the two-stage endpoint step is

    M_n
      -> forcing M_{n-1}
      -> state M_{n+3/4}
      -> forcing M_{n-1/4}
      -> state M_{n+1}.

The two source gains are encoded by the exact identities

    n + 3/4 = (n - 1)   + 7/4,
    n + 1   = (n - 1/4) + 5/4.

Thus the same already-compiled `7/4` and `5/4` heat majorants can be reused at
every induction level.  Future induction files should depend on these generic
weights rather than introducing `SixthFrequencySplit`,
`TwentySevenQuarterFrequencySplit`, and so on.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentAlgebra
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Generic radial Fourier moment weight. -/
noncomputable def h3FourierMomentWeight
    (q : ℝ)
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ q

/-- Generic harmless coefficient in the convolution frequency split. -/
noncomputable def h3FourierMomentSplitCoefficient
    (q : ℝ) : ℝ :=
  (2 : ℝ) ^ q

/-- Generic raw Fourier moment mass of a scalar spectral state. -/
noncomputable def h3SpectralScalarRawFourierMomentMass
    (q : ℝ)
    (F : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierMomentWeight q ξ *
      ‖h3SpectralScalarRawFourier F ξ‖

/-- Generic raw Fourier moment integrability predicate. -/
def H3RawFourierMomentIntegrable
    (q : ℝ)
    (F : H3SpectralScalarState) : Prop :=
  Integrable
    (fun ξ : H3FourierPoint3 =>
      h3FourierMomentWeight q ξ *
        ‖h3SpectralScalarRawFourier F ξ‖)
    (volume : Measure H3FourierPoint3)

/-- Every generic radial moment weight is nonnegative. -/
theorem h3FourierMomentWeight_nonneg
    (q : ℝ)
    (ξ : H3FourierPoint3) :
    0 ≤ h3FourierMomentWeight q ξ := by
  unfold h3FourierMomentWeight
  exact Real.rpow_nonneg (norm_nonneg ξ) _

/-- Every generic convolution split coefficient is nonnegative. -/
theorem h3FourierMomentSplitCoefficient_nonneg
    (q : ℝ) :
    0 ≤ h3FourierMomentSplitCoefficient q := by
  unfold h3FourierMomentSplitCoefficient
  exact Real.rpow_nonneg (by norm_num) _

/-- Nonnegative generic real exponents give continuous radial weights. -/
theorem continuous_h3FourierMomentWeight
    {q : ℝ}
    (hq : 0 ≤ q) :
    Continuous (h3FourierMomentWeight q) := by
  unfold h3FourierMomentWeight
  exact
    continuous_norm.rpow_const
      (fun _ => Or.inr hq)

/-- Generic moment mass is nonnegative. -/
theorem h3SpectralScalarRawFourierMomentMass_nonneg
    (q : ℝ)
    (F : H3SpectralScalarState) :
    0 ≤ h3SpectralScalarRawFourierMomentMass q F := by
  unfold h3SpectralScalarRawFourierMomentMass
  exact
    integral_nonneg fun ξ =>
      mul_nonneg
        (h3FourierMomentWeight_nonneg q ξ)
        (norm_nonneg _)

/-- On nonnegative exponents, radial weights multiply by adding exponents. -/
theorem h3FourierMomentWeight_add
    {q r : ℝ}
    (hq : 0 ≤ q)
    (hr : 0 ≤ r)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (q + r) ξ
      =
    h3FourierMomentWeight q ξ *
      h3FourierMomentWeight r ξ := by
  unfold h3FourierMomentWeight
  exact
    Real.rpow_add_of_nonneg
      (norm_nonneg ξ) hq hr

/-- The generic real-power weight agrees with the ordinary natural power at
integer exponents. -/
theorem h3FourierMomentWeight_natCast
    (n : ℕ)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (n : ℝ) ξ
      =
    ‖ξ‖ ^ n := by
  unfold h3FourierMomentWeight
  exact Real.rpow_natCast ‖ξ‖ n

/-- One ordinary derivative power is exactly one increment of the generic
moment exponent. -/
theorem h3FourierMomentWeight_add_one
    {q : ℝ}
    (hq : 0 ≤ q)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (q + 1) ξ
      =
    h3FourierMomentWeight q ξ * ‖ξ‖ := by
  calc
    h3FourierMomentWeight (q + 1) ξ
        =
      h3FourierMomentWeight q ξ *
        h3FourierMomentWeight 1 ξ :=
      h3FourierMomentWeight_add
        hq (by norm_num) ξ
    _ =
      h3FourierMomentWeight q ξ * ‖ξ‖ := by
      unfold h3FourierMomentWeight
      rw [Real.rpow_one]

/-- The generic convolution frequency split for every nonnegative real moment
exponent.  This single lemma replaces all named integer and fractional split
lemmas in subsequent bootstrap levels. -/
theorem h3FourierMomentWeight_le_split
    {q : ℝ}
    (hq : 0 ≤ q)
    (ξ η : H3FourierPoint3) :
    h3FourierMomentWeight q ξ
      ≤
    h3FourierMomentSplitCoefficient q *
      (h3FourierMomentWeight q η +
        h3FourierMomentWeight q (ξ - η)) := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg _

  have hη0 : 0 ≤ ‖η‖ :=
    norm_nonneg _

  have hshift0 : 0 ≤ ‖ξ - η‖ :=
    norm_nonneg _

  have htri :
      ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    calc
      ‖ξ‖ = ‖η + (ξ - η)‖ := by
        congr 1
        abel
      _ ≤ ‖η‖ + ‖ξ - η‖ :=
        norm_add_le _ _

  have hcoeff0 :
      0 ≤ (2 : ℝ) ^ q :=
    Real.rpow_nonneg (by norm_num) _

  have hηw0 :
      0 ≤ ‖η‖ ^ q :=
    Real.rpow_nonneg hη0 _

  have hshiftw0 :
      0 ≤ ‖ξ - η‖ ^ q :=
    Real.rpow_nonneg hshift0 _

  unfold
    h3FourierMomentWeight
    h3FourierMomentSplitCoefficient

  by_cases hηshift : ‖η‖ ≤ ‖ξ - η‖
  · have htwo :
        ‖ξ‖ ≤ 2 * ‖ξ - η‖ := by
      linarith

    have hrpow :
        ‖ξ‖ ^ q
          ≤
        (2 * ‖ξ - η‖) ^ q :=
      Real.rpow_le_rpow
        hξ0 htwo hq

    have hmul :
        (2 * ‖ξ - η‖) ^ q
          =
        (2 : ℝ) ^ q *
          ‖ξ - η‖ ^ q := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hshift0
      ]

    calc
      ‖ξ‖ ^ q
          ≤
        (2 * ‖ξ - η‖) ^ q :=
        hrpow
      _ =
        (2 : ℝ) ^ q *
          ‖ξ - η‖ ^ q :=
        hmul
      _ ≤
        (2 : ℝ) ^ q *
          (‖η‖ ^ q + ‖ξ - η‖ ^ q) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith)
            hcoeff0

  · have hshiftη :
        ‖ξ - η‖ ≤ ‖η‖ := by
      exact le_of_lt (lt_of_not_ge hηshift)

    have htwo :
        ‖ξ‖ ≤ 2 * ‖η‖ := by
      linarith

    have hrpow :
        ‖ξ‖ ^ q
          ≤
        (2 * ‖η‖) ^ q :=
      Real.rpow_le_rpow
        hξ0 htwo hq

    have hmul :
        (2 * ‖η‖) ^ q
          =
        (2 : ℝ) ^ q *
          ‖η‖ ^ q := by
      rw [
        Real.mul_rpow
          (by norm_num : 0 ≤ (2 : ℝ))
          hη0
      ]

    calc
      ‖ξ‖ ^ q
          ≤
        (2 * ‖η‖) ^ q :=
        hrpow
      _ =
        (2 : ℝ) ^ q *
          ‖η‖ ^ q :=
        hmul
      _ ≤
        (2 : ℝ) ^ q *
          (‖η‖ ^ q + ‖ξ - η‖ ^ q) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith)
            hcoeff0

/-!
The remaining definitions record the exponent geometry of one complete
integer bootstrap step.
-/

/-- Integer state exponent at bootstrap level `n`. -/
noncomputable def h3MomentBootstrapStateExponent
    (n : ℕ) : ℝ :=
  n

/-- Forcing exponent obtained after spending one derivative from `M_n`. -/
noncomputable def h3MomentBootstrapFirstForcingExponent
    (n : ℕ) : ℝ :=
  (n : ℝ) - 1

/-- Subcritical intermediate state exponent. -/
noncomputable def h3MomentBootstrapIntermediateStateExponent
    (n : ℕ) : ℝ :=
  (n : ℝ) + (3 : ℝ) / 4

/-- Forcing exponent after feeding the intermediate state through the
quadratic nonlinearity and spending one derivative. -/
noncomputable def h3MomentBootstrapSecondForcingExponent
    (n : ℕ) : ℝ :=
  (n : ℝ) - (1 : ℝ) / 4

/-- Next integer state exponent. -/
noncomputable def h3MomentBootstrapNextStateExponent
    (n : ℕ) : ℝ :=
  (n : ℝ) + 1

/-- The first nonlinear step spends exactly one power. -/
theorem h3MomentBootstrap_state_eq_firstForcing_add_one
    (n : ℕ) :
    h3MomentBootstrapStateExponent n
      =
    h3MomentBootstrapFirstForcingExponent n + 1 := by
  unfold
    h3MomentBootstrapStateExponent
    h3MomentBootstrapFirstForcingExponent
  ring

/-- The intermediate nonlinear step also spends exactly one power. -/
theorem h3MomentBootstrap_intermediateState_eq_secondForcing_add_one
    (n : ℕ) :
    h3MomentBootstrapIntermediateStateExponent n
      =
    h3MomentBootstrapSecondForcingExponent n + 1 := by
  unfold
    h3MomentBootstrapIntermediateStateExponent
    h3MomentBootstrapSecondForcingExponent
  ring

/-- The first source step gains exactly `7/4` heat powers. -/
theorem h3MomentBootstrap_intermediateState_eq_firstForcing_add_sevenQuarter
    (n : ℕ) :
    h3MomentBootstrapIntermediateStateExponent n
      =
    h3MomentBootstrapFirstForcingExponent n + (7 : ℝ) / 4 := by
  unfold
    h3MomentBootstrapIntermediateStateExponent
    h3MomentBootstrapFirstForcingExponent
  ring

/-- The final source step gains exactly `5/4` heat powers. -/
theorem h3MomentBootstrap_nextState_eq_secondForcing_add_fiveQuarter
    (n : ℕ) :
    h3MomentBootstrapNextStateExponent n
      =
    h3MomentBootstrapSecondForcingExponent n + (5 : ℝ) / 4 := by
  unfold
    h3MomentBootstrapNextStateExponent
    h3MomentBootstrapSecondForcingExponent
  ring

/-- For `n ≥ 1`, the first forcing exponent is nonnegative. -/
theorem h3MomentBootstrapFirstForcingExponent_nonneg
    {n : ℕ}
    (hn : 1 ≤ n) :
    0 ≤ h3MomentBootstrapFirstForcingExponent n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  unfold h3MomentBootstrapFirstForcingExponent
  linarith

/-- For `n ≥ 1`, the intermediate state exponent is nonnegative. -/
theorem h3MomentBootstrapIntermediateStateExponent_nonneg
    (n : ℕ) :
    0 ≤ h3MomentBootstrapIntermediateStateExponent n := by
  unfold h3MomentBootstrapIntermediateStateExponent
  positivity

/-- For `n ≥ 1`, the second forcing exponent is nonnegative. -/
theorem h3MomentBootstrapSecondForcingExponent_nonneg
    {n : ℕ}
    (hn : 1 ≤ n) :
    0 ≤ h3MomentBootstrapSecondForcingExponent n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  unfold h3MomentBootstrapSecondForcingExponent
  linarith

/-- The first subcritical source factorization in generic radial-weight form.
This is the uniform replacement for `15/4 = 2 + 7/4`,
`19/4 = 3 + 7/4`, `23/4 = 4 + 7/4`, and all later copies. -/
theorem h3FourierMomentBootstrap_intermediateWeight_eq_firstForcing_mul_sevenQuarter
    {n : ℕ}
    (hn : 1 ≤ n)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight
        (h3MomentBootstrapIntermediateStateExponent n) ξ
      =
    h3FourierMomentWeight
        (h3MomentBootstrapFirstForcingExponent n) ξ *
      h3FourierSevenQuarterWeight ξ := by
  have hFirst0 :
      0 ≤ h3MomentBootstrapFirstForcingExponent n :=
    h3MomentBootstrapFirstForcingExponent_nonneg hn

  unfold h3FourierSevenQuarterWeight

  calc
    h3FourierMomentWeight
        (h3MomentBootstrapIntermediateStateExponent n) ξ
        =
      h3FourierMomentWeight
        (h3MomentBootstrapFirstForcingExponent n + (7 : ℝ) / 4) ξ := by
      rw [
        h3MomentBootstrap_intermediateState_eq_firstForcing_add_sevenQuarter
      ]
    _ =
      h3FourierMomentWeight
          (h3MomentBootstrapFirstForcingExponent n) ξ *
        h3FourierMomentWeight ((7 : ℝ) / 4) ξ :=
      h3FourierMomentWeight_add
        hFirst0 (by norm_num) ξ
    _ =
      h3FourierMomentWeight
          (h3MomentBootstrapFirstForcingExponent n) ξ *
        ‖ξ‖ ^ ((7 : ℝ) / 4) := by
      rfl

/-- The final subcritical source factorization in generic radial-weight form.
This uniformly replaces `4 = 11/4 + 5/4`,
`5 = 15/4 + 5/4`, `6 = 19/4 + 5/4`, and all later copies. -/
theorem h3FourierMomentBootstrap_nextWeight_eq_secondForcing_mul_fiveQuarter
    {n : ℕ}
    (hn : 1 ≤ n)
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight
        (h3MomentBootstrapNextStateExponent n) ξ
      =
    h3FourierMomentWeight
        (h3MomentBootstrapSecondForcingExponent n) ξ *
      h3FourierFiveQuarterWeight ξ := by
  have hSecond0 :
      0 ≤ h3MomentBootstrapSecondForcingExponent n :=
    h3MomentBootstrapSecondForcingExponent_nonneg hn

  unfold h3FourierFiveQuarterWeight

  calc
    h3FourierMomentWeight
        (h3MomentBootstrapNextStateExponent n) ξ
        =
      h3FourierMomentWeight
        (h3MomentBootstrapSecondForcingExponent n + (5 : ℝ) / 4) ξ := by
      rw [
        h3MomentBootstrap_nextState_eq_secondForcing_add_fiveQuarter
      ]
    _ =
      h3FourierMomentWeight
          (h3MomentBootstrapSecondForcingExponent n) ξ *
        h3FourierMomentWeight ((5 : ℝ) / 4) ξ :=
      h3FourierMomentWeight_add
        hSecond0 (by norm_num) ξ
    _ =
      h3FourierMomentWeight
          (h3MomentBootstrapSecondForcingExponent n) ξ *
        ‖ξ‖ ^ ((5 : ℝ) / 4) := by
      rfl

/-- The old canonical full-fifth mass is exactly the generic moment mass at
real exponent `5`.  This is the first bridge from the concrete layers into the
induction API. -/
theorem h3SpectralScalarRawFourierMomentMass_five_eq
    (F : H3SpectralScalarState) :
    h3SpectralScalarRawFourierMomentMass 5 F
      =
    h3SpectralScalarRawFourierFifthMass F := by
  unfold
    h3SpectralScalarRawFourierMomentMass
    h3SpectralScalarRawFourierFifthMass

  apply integral_congr_ae
  filter_upwards with ξ

  unfold h3FourierMomentWeight

  have hpow :
      ‖ξ‖ ^ (5 : ℝ)
        =
      ‖ξ‖ ^ (5 : ℕ) := by
    exact Real.rpow_natCast ‖ξ‖ 5

  rw [hpow]

end
end Euclidean
end Bridge
end PrimeTensor
