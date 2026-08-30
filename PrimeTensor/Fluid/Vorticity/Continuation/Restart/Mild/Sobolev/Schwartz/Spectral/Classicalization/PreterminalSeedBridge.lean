import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalSpectralSlice

/-!
# Classicalization: bridge to the preterminal H³ seed interface

The classicalization restart assumes `VelocityH3IntegrableAt u t` at one
strictly preterminal anchor time.  The older BKM / H³-energy stack packages the
same datum as `PreterminalH3Seed u T`: existence of an interior time together
with one finite scalar bound for every logged velocity derivative through
order three.

The canonical finite-sum H³ energy already turns integrability at a fixed time
into such a finite bound.  Conversely, `VelocityH3BoundAt` contains the
integrability of every square appearing in `VelocityH3IntegrableAt`.

Thus no new analytic theorem is required to identify the two seed interfaces.
The still-open issue is propagation of this seed in time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

noncomputable section

/-- A finite componentwise H³ bound contains all square-integrability facts
required by `VelocityH3IntegrableAt`. -/
theorem velocityH3IntegrableAt_of_velocityH3BoundAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t M : ℝ}
    (hBound : VelocityH3BoundAt u t M) :
    VelocityH3IntegrableAt u t := by
  intro j

  have h := hBound j

  dsimp only at h ⊢

  rcases h with
    ⟨h0, h1, h2, h3⟩

  refine
    ⟨
      h0.1,
      ?_,
      ?_,
      ?_
    ⟩

  · intro i
    exact (h1 i).1

  · intro i k
    exact (h2 i k).1

  · intro i k l
    exact (h3 i k l).1

/-- The BKM seed predicate is equivalent to existence of one strictly
preterminal H³-integrable slice. -/
theorem preterminalH3Seed_iff_exists_velocityH3IntegrableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} :
    PreterminalH3Seed u T
      ↔
    ∃ t : ℝ,
      t ∈ Set.Ioo (0 : ℝ) T
        ∧
      VelocityH3IntegrableAt u t := by
  constructor

  · rintro
      ⟨
        t,
        M,
        ht,
        _hM,
        hBound
      ⟩

    exact
      ⟨
        t,
        ht,
        velocityH3IntegrableAt_of_velocityH3BoundAt
          hBound
      ⟩

  · rintro
      ⟨
        t,
        ht,
        hInt
      ⟩

    refine
      ⟨
        t,
        velocityH3EnergyAt u t,
        ht,
        ?_,
        velocityH3BoundAt_canonical
          u t hInt
      ⟩

    exact
      le_trans
        (by norm_num)
        (one_le_velocityH3EnergyAt u t)

/-- Direct bridge used by classicalization: an explicit H³-integrable restart
anchor canonically supplies the older `PreterminalH3Seed` interface. -/
theorem preterminalH3Seed_of_velocityH3IntegrableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t) :
    PreterminalH3Seed u T := by
  exact
    preterminalH3Seed_iff_exists_velocityH3IntegrableAt.mpr
      ⟨t, ht, hInt⟩

end
end Euclidean
end Bridge
end PrimeTensor
