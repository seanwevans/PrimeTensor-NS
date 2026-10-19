import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdActualStaticAbsorptionObstruction244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact
import Mathlib.Tactic

/-!
# The adverse full-third Schwartz sign in the unforced Navier–Stokes balance

The full-third spatial Schwartz counterexample now has an actual nonzero
coefficient, and the preceding checkpoint ruled out static upper absorption
of the POSITIVE coefficient. The physical unforced Navier–Stokes energy
identity, however, has the opposite sign:

  E'(t) + 2 D(t) = -T_H3(t).

This module reverses the complete cubic without changing the quadratic
kinetic anchor, dissipation, or normalized H3 energy. It constructs a SINGLE
fixed-kinetic solenoidal Schwartz seed whose concentrated, sign-reversed
profiles defeat every static absorption estimate on the physically adverse
side `-T3`.

The final theorem plugs an arbitrary actual energy-class Navier–Stokes path
into its previously proved EXACT balance. Its hypotheses expose two necessary
remaining bridges: the lower-order transport contribution of the actual path,
and the relation between path dissipation and the Schwartz fourth-order mass.
It does not assume an arbitrary Schwartz profile is already attained as a
positive-time solution, and does not deduce blowup or even the existence of a
particular solution from these static profiles.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeUnforcedSign244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Reverse the COMPLETE cubic `G3 + 3M`, not merely the first monomial. -/
theorem fullSchwartzThirdCommutator_negate244
    (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzThirdCommutator244 (fun j => (-1 : ℝ) • f j) =
      - fullSchwartzThirdCommutator244 f := by
  rw [fullSchwartzThirdCommutator_real_smul244]
  norm_num

/-- Reversing velocity leaves the actual fourth-derivative square mass intact. -/
theorem fullSchwartzTopDissipation_negate244
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3TopDissipation (fun j => (-1 : ℝ) • f j) =
      lowNormalRealSchwartzH3TopDissipation f := by
  rw [lowNormalRealSchwartzH3TopDissipation_real_smul]
  norm_num

/-- Reversing velocity leaves the full normalized H3 energy, including its
constant term, exactly unchanged. -/
theorem fullSchwartzH3Energy_negate244
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy (fun j => (-1 : ℝ) • f j) =
      lowNormalRealSchwartzH3Energy f := by
  simp only [lowNormalRealSchwartzH3Energy_eq_one_add_quadratic,
    lowNormalRealSchwartzH3EnergyQuadratic_real_smul]
  norm_num

/-- The physical kinetic anchor also survives sign reversal. -/
theorem fullSchwartzKineticEnergy_negate244
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy0 (fun j => (-1 : ℝ) • f j) =
      lowNormalRealSchwartzH3Energy0 f := by
  rw [lowNormalRealSchwartzH3Energy0_real_smul]
  norm_num

/-- The already proved unconditional positive-coefficient obstruction can
be reversed, with EXACTLY the same anchor, into the adverse sign of the
unforced Navier–Stokes energy identity. The seed is fixed BEFORE C and K. -/
theorem thirdFullSchwartz_oneSeed_adverseUnforcedTransport244 :
    ∃ seed : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal seed ∧
      fullSchwartzThirdCommutator244 seed < 0 ∧
      ∀ C K : ℝ, ∃ g : A3 → SchwartzMap V3 ℝ,
        lowNormalRealSchwartz_Point3Solenoidal g ∧
        lowNormalRealSchwartzH3Energy0 g =
          lowNormalRealSchwartzH3Energy0 seed ∧
        fullSchwartzThirdCommutator244 g < 0 ∧
        C * lowNormalRealSchwartzH3TopDissipation g +
            K * lowNormalRealSchwartzH3Energy g <
          - fullSchwartzThirdCommutator244 g := by
  obtain ⟨positiveSeed, hDiv, hPositive, hAll⟩ :=
    thirdFullActualSchwartz_oneSeed_defeats_all_staticCoefficients244
  let seed : A3 → SchwartzMap V3 ℝ :=
    fun j => (-1 : ℝ) • positiveSeed j
  have hSeedDiv : lowNormalRealSchwartz_Point3Solenoidal seed :=
    lowNormalRealSchwartz_Point3Solenoidal_real_smul (-1) positiveSeed hDiv
  have hSeedNeg : fullSchwartzThirdCommutator244 seed < 0 := by
    change fullSchwartzThirdCommutator244
      (fun j => (-1 : ℝ) • positiveSeed j) < 0
    rw [fullSchwartzThirdCommutator_negate244]
    exact neg_lt_zero.mpr hPositive
  refine ⟨seed, hSeedDiv, hSeedNeg, ?_⟩
  intro C K
  obtain ⟨positiveProfile, hProfileDiv, hProfileMass, hProfilePos, hEscape⟩ :=
    hAll C K
  let g : A3 → SchwartzMap V3 ℝ :=
    fun j => (-1 : ℝ) • positiveProfile j
  have hgDiv : lowNormalRealSchwartz_Point3Solenoidal g :=
    lowNormalRealSchwartz_Point3Solenoidal_real_smul
      (-1) positiveProfile hProfileDiv
  have hgMass : lowNormalRealSchwartzH3Energy0 g =
      lowNormalRealSchwartzH3Energy0 seed := by
    calc
      _ = lowNormalRealSchwartzH3Energy0 positiveProfile :=
        fullSchwartzKineticEnergy_negate244 positiveProfile
      _ = lowNormalRealSchwartzH3Energy0 positiveSeed := hProfileMass
      _ = lowNormalRealSchwartzH3Energy0 seed :=
        (fullSchwartzKineticEnergy_negate244 positiveSeed).symm
  have hgNeg : fullSchwartzThirdCommutator244 g < 0 := by
    change fullSchwartzThirdCommutator244
      (fun j => (-1 : ℝ) • positiveProfile j) < 0
    rw [fullSchwartzThirdCommutator_negate244]
    exact neg_lt_zero.mpr hProfilePos
  have hgEscape :
      C * lowNormalRealSchwartzH3TopDissipation g +
          K * lowNormalRealSchwartzH3Energy g <
        - fullSchwartzThirdCommutator244 g := by
    change C * lowNormalRealSchwartzH3TopDissipation
        (fun j => (-1 : ℝ) • positiveProfile j) +
      K * lowNormalRealSchwartzH3Energy
        (fun j => (-1 : ℝ) • positiveProfile j) <
      -fullSchwartzThirdCommutator244
        (fun j => (-1 : ℝ) • positiveProfile j)
    rw [fullSchwartzTopDissipation_negate244,
      fullSchwartzH3Energy_negate244,
      fullSchwartzThirdCommutator_negate244]
    simpa only [neg_neg] using hEscape
  exact ⟨g, hgDiv, hgMass, hgNeg, hgEscape⟩

/-- One kinetic mass supports adverse signed profiles for ALL coercive
coefficients, including the physical coefficient two of viscosity. -/
theorem thirdFullSchwartz_fixedKinetic_unforcedAdverse244 :
    ∃ E₀ : ℝ, ∀ C K : ℝ,
      ∃ g : A3 → SchwartzMap V3 ℝ,
        lowNormalRealSchwartz_Point3Solenoidal g ∧
        lowNormalRealSchwartzH3Energy0 g = E₀ ∧
        fullSchwartzThirdCommutator244 g < 0 ∧
        C * lowNormalRealSchwartzH3TopDissipation g +
          K * lowNormalRealSchwartzH3Energy g <
            -fullSchwartzThirdCommutator244 g := by
  obtain ⟨seed, _, _, hAll⟩ :=
    thirdFullSchwartz_oneSeed_adverseUnforcedTransport244
  exact ⟨lowNormalRealSchwartzH3Energy0 seed, hAll⟩

/-- In particular, the literal viscous coefficient TWO in the exact
unforced balance is defeated at the SAME physical kinetic-energy anchor. -/
theorem thirdFullSchwartz_fixedKinetic_viscousTwoAdverse244 :
    ∃ E₀ : ℝ, ∀ K : ℝ,
      ∃ g : A3 → SchwartzMap V3 ℝ,
        lowNormalRealSchwartz_Point3Solenoidal g ∧
        lowNormalRealSchwartzH3Energy0 g = E₀ ∧
        fullSchwartzThirdCommutator244 g < 0 ∧
        2 * lowNormalRealSchwartzH3TopDissipation g +
          K * lowNormalRealSchwartzH3Energy g <
            -fullSchwartzThirdCommutator244 g := by
  obtain ⟨E₀, hAll⟩ :=
    thirdFullSchwartz_fixedKinetic_unforcedAdverse244
  exact ⟨E₀, fun K => hAll 2 K⟩

/-- Static absorption in the UNFORCED energy-balance sign, over every
solenoidal Schwartz velocity. This is deliberately not a PDE-time predicate. -/
def FullThirdUnforcedStaticCoercivity244 (C K : ℝ) : Prop :=
  ∀ f : A3 → SchwartzMap V3 ℝ,
    lowNormalRealSchwartz_Point3Solenoidal f →
      -fullSchwartzThirdCommutator244 f ≤
        C * lowNormalRealSchwartzH3TopDissipation f +
          K * lowNormalRealSchwartzH3Energy f

/-- Every proposed uniform STATIC coercive bound with the physically adverse
sign is false, not just one particular positive pair C,K. -/
theorem thirdFullSchwartz_no_unforced_staticCoercivity244 (C K : ℝ) :
    ¬ FullThirdUnforcedStaticCoercivity244 C K := by
  intro hUniversal
  obtain ⟨seed, _, _, hAll⟩ :=
    thirdFullSchwartz_oneSeed_adverseUnforcedTransport244
  obtain ⟨g, hDiv, _, _, hAdverse⟩ := hAll C K
  exact (not_le_of_gt hAdverse) (hUniversal g hDiv)

/-- For an ACTUAL admissible unforced NS path, the exact energy balance
translates an adverse top-order Schwartz coefficient into a positive energy
slope PROVIDED the whole path transport and its lower-order/dissipation
remainder obey the explicit compatibility inequalities. No NS realization
of an arbitrary Schwartz field is asserted. -/
theorem h3Path_energySlope_pos_of_fullThird_adverseSlice244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t C K R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hTransport : velocityH3TransportDerivativeAt u t =
      fullSchwartzThirdCommutator244 f + R)
    (hRemainder : R + 2 * velocityH3DissipationAt u t ≤
      C * lowNormalRealSchwartzH3TopDissipation f +
        K * lowNormalRealSchwartzH3Energy f)
    (hAdverse : C * lowNormalRealSchwartzH3TopDissipation f +
        K * lowNormalRealSchwartzH3Energy f <
      -fullSchwartzThirdCommutator244 f) :
    0 < deriv (velocityH3EnergyAt u) t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  rw [hTransport] at hBalance
  linarith

end
end PrimeTensor.FirstMonomialTriad
