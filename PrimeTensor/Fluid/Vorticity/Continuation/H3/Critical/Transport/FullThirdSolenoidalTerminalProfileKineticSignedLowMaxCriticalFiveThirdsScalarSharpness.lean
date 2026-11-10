import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalFiveThirdsDissipationContinuationGate
import Mathlib.Tactic

/-!
# Sharpness of the cubic terminal-rate mechanism at exponent 5/3

This file proves the precise limitation of the preceding physical endpoint
continuation criterion.  The scalar model `D(d) = d^(-8/3)` saturates

  1 = d^8 * D(d)^3

for every `d > 0`.  Its five-thirds weighted terminal cost is `1/d`,
which is not integrable, but for EVERY `beta > 5/3` its beta-weighted
cost is integrable over each finite terminal interval.

This is a scalar obstruction to strengthening the cubic-rate ARGUMENT, not
an actual nonextendible Navier--Stokes solution.  Any supercritical
weighted continuation result needs an additional property of the PDE.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The exactly saturating scalar cubic terminal-rate profile. -/
noncomputable def thirdFullKinetic_cubicRateSaturatingProfile244
    (d : ℝ) : ℝ :=
  d ^ (-(8 : ℝ) / 3)

/-- The scalar profile is nonnegative at positive terminal distance. -/
theorem thirdFullKinetic_cubicRateSaturatingProfile_nonneg244
    (d : ℝ) (hd : 0 < d) :
    0 ≤ thirdFullKinetic_cubicRateSaturatingProfile244 d := by
  unfold thirdFullKinetic_cubicRateSaturatingProfile244
  exact Real.rpow_nonneg hd.le _

/-- Exact saturation of the cubic terminal estimate, with coefficient 1. -/
theorem thirdFullKinetic_cubicRateSaturatingProfile_exactCubic244
    (d : ℝ) (hd : 0 < d) :
    (1 : ℝ) = d ^ 8 * (thirdFullKinetic_cubicRateSaturatingProfile244 d) ^ 3 := by
  have hCube :
      (thirdFullKinetic_cubicRateSaturatingProfile244 d) ^ (3 : ℕ) =
        d ^ (-(8 : ℝ)) := by
    unfold thirdFullKinetic_cubicRateSaturatingProfile244
    calc
      (d ^ (-(8 : ℝ) / 3)) ^ (3 : ℕ) =
          (d ^ (-(8 : ℝ) / 3)) ^ (3 : ℝ) :=
        (Real.rpow_natCast (d ^ (-(8 : ℝ) / 3)) 3).symm
      _ = d ^ ((-(8 : ℝ) / 3) * 3) :=
        (Real.rpow_mul hd.le (-(8 : ℝ) / 3) (3 : ℝ)).symm
      _ = d ^ (-(8 : ℝ)) := by congr 1; ring
  calc
    (1 : ℝ) = d ^ ((8 : ℝ) + (-(8 : ℝ))) := by
      rw [show (8 : ℝ) + (-(8 : ℝ)) = 0 by ring, Real.rpow_zero]
    _ = d ^ (8 : ℝ) * d ^ (-(8 : ℝ)) :=
      Real.rpow_add hd (8 : ℝ) (-(8 : ℝ))
    _ = d ^ 8 * (thirdFullKinetic_cubicRateSaturatingProfile244 d) ^ 3 := by
      rw [hCube]
      exact congrArg (fun x : ℝ => x * d ^ (-(8 : ℝ)))
        (Real.rpow_natCast d 8)

/-- Multiplying the saturating profile by a beta weight leaves an exact
power with exponent beta - 8/3. -/
theorem thirdFullKinetic_cubicRateSaturatingProfile_weight244
    (d beta : ℝ) (hd : 0 < d) :
    d ^ beta * thirdFullKinetic_cubicRateSaturatingProfile244 d =
      d ^ (beta - (8 : ℝ) / 3) := by
  unfold thirdFullKinetic_cubicRateSaturatingProfile244
  calc
    d ^ beta * d ^ (-(8 : ℝ) / 3) =
        d ^ (beta + (-(8 : ℝ) / 3)) :=
      (Real.rpow_add hd beta (-(8 : ℝ) / 3)).symm
    _ = d ^ (beta - (8 : ℝ) / 3) := by congr 1; ring

/-- At beta=5/3, the exact saturating profile has the nonintegrable
harmonic terminal cost. -/
theorem thirdFullKinetic_cubicRateSaturatingProfile_criticalNonintegrable244
    (T a : ℝ) (ha : a < T) :
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) ^ ((5 : ℝ) / 3) *
        thirdFullKinetic_cubicRateSaturatingProfile244 (T - t))
      (Set.Ioo a T) := by
  intro hCritical
  have hReciprocal : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / (T - t)) (Set.Ioo a T) := by
    apply Integrable.congr hCritical
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hd : 0 < T - t := sub_pos.mpr ht.2
    calc
      (T - t) ^ ((5 : ℝ) / 3) *
          thirdFullKinetic_cubicRateSaturatingProfile244 (T - t) =
        (T - t) ^ (((5 : ℝ) / 3) - (8 : ℝ) / 3) :=
          thirdFullKinetic_cubicRateSaturatingProfile_weight244
            (T - t) ((5 : ℝ) / 3) hd
      _ = (T - t) ^ (-(1 : ℝ)) := by congr 1; ring
      _ = 1 / (T - t) := by rw [Real.rpow_neg_one]; ring
  exact not_integrableOn_one_div_terminalDistance ha hReciprocal

/-- Every supercritical exponent has an integrable weighted scalar
profile despite exact saturation of the cubic terminal rate. -/
theorem thirdFullKinetic_cubicRateSaturatingProfile_supercriticalIntegrable244
    (T a beta : ℝ) (ha : a < T)
    (hbeta : (5 : ℝ) / 3 < beta) :
    IntervalIntegrable
      (fun t : ℝ => (T - t) ^ beta *
        thirdFullKinetic_cubicRateSaturatingProfile244 (T - t))
      volume a T := by
  let gamma : ℝ := beta - (8 : ℝ) / 3
  have hgamma : -1 < gamma := by
    dsimp only [gamma]
    linarith only [hbeta]
  have hBase : IntervalIntegrable
      (fun d : ℝ => d ^ gamma) volume 0 (T - a) := by
    exact intervalIntegral.intervalIntegrable_rpow' hgamma
  have hShift : IntervalIntegrable
      (fun t : ℝ => (T - t) ^ gamma) volume a T := by
    have hComp := hBase.comp_sub_left T
    simpa only [sub_zero, sub_sub_cancel] using hComp.symm
  have hPowerOn : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) ^ gamma) (Set.Ioo a T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mp hShift
  have hWeightedOn : MeasureTheory.IntegrableOn
      (fun t : ℝ => (T - t) ^ beta *
        thirdFullKinetic_cubicRateSaturatingProfile244 (T - t))
      (Set.Ioo a T) := by
    apply Integrable.congr hPowerOn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hd : 0 < T - t := sub_pos.mpr ht.2
    change (T - t) ^ (beta - (8 : ℝ) / 3) =
      (T - t) ^ beta *
        thirdFullKinetic_cubicRateSaturatingProfile244 (T - t)
    exact (thirdFullKinetic_cubicRateSaturatingProfile_weight244
      (T - t) beta hd).symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr hWeightedOn

/-- The rate inequality alone cannot prohibit integrability at any
terminal weight beta strictly greater than 5/3: a single explicit scalar
counterprofile works for every such beta. -/
theorem thirdFullKinetic_cubicRate_supercriticalWeight_hasCounterprofile244
    (T a beta : ℝ) (ha : a < T)
    (hbeta : (5 : ℝ) / 3 < beta) :
    ∃ D : ℝ → ℝ,
      (∀ d : ℝ, 0 < d →
        0 ≤ D d ∧ (1 : ℝ) ≤ d ^ 8 * (D d) ^ 3) ∧
      IntervalIntegrable
        (fun t : ℝ => (T - t) ^ beta * D (T - t))
        volume a T := by
  refine ⟨thirdFullKinetic_cubicRateSaturatingProfile244, ?_, ?_⟩
  · intro d hd
    exact ⟨thirdFullKinetic_cubicRateSaturatingProfile_nonneg244 d hd,
      le_of_eq (thirdFullKinetic_cubicRateSaturatingProfile_exactCubic244 d hd)⟩
  · exact thirdFullKinetic_cubicRateSaturatingProfile_supercriticalIntegrable244
      T a beta ha hbeta

end
end PrimeTensor.FirstMonomialTriad
