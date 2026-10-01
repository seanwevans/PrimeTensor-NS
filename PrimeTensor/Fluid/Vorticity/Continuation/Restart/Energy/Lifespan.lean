import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Lifespan
import PrimeTensor.Fluid.Vorticity.H3.Energy.Functional

/-!
# Canonical-energy form of the uniform H³ restart lifespan

`UniformH3RealRestartLifespan` is stated using the componentwise predicate
`VelocityH3BoundAt u t M`: every velocity component and every ordered spatial
partial through order three has squared `L²` energy bounded by the same number
`M`.

Classical local well-posedness is more naturally stated in terms of one scalar
H³ norm.  The project already has exactly such a normalized scalar quantity,
`velocityH3EnergyAt`.

This file proves the finite-coordinate bookkeeping needed to pass back and
forth between the two formulations.  No local Navier--Stokes existence theorem
is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeRestartEnergyLifespan
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The total scalar H³ budget obtained when every componentwise squared-energy
summand is bounded by the same number `M`.

Writing it as finite sums rather than hard-coding the three-dimensional
multiplicity keeps the statement tied directly to the project's positive-axis
representation.
-/
noncomputable def velocityH3CoordinateBudget
    (M : ℝ) : ℝ :=
  1
    + (∑ _j : PrimeTensor.Axis Depth.three, M)
    + (∑ _j : PrimeTensor.Axis Depth.three,
        ∑ _i : PrimeTensor.Axis Depth.three, M)
    + (∑ _j : PrimeTensor.Axis Depth.three,
        ∑ _i : PrimeTensor.Axis Depth.three,
          ∑ _k : PrimeTensor.Axis Depth.three, M)
    + (∑ _j : PrimeTensor.Axis Depth.three,
        ∑ _i : PrimeTensor.Axis Depth.three,
          ∑ _k : PrimeTensor.Axis Depth.three,
            ∑ _l : PrimeTensor.Axis Depth.three, M)

/-- A nonnegative componentwise budget gives a normalized scalar budget. -/
theorem one_le_velocityH3CoordinateBudget
    {M : ℝ}
    (hM : 0 ≤ M) :
    1 ≤ velocityH3CoordinateBudget M := by

  have h0 :
      0 ≤ ∑ _j : PrimeTensor.Axis Depth.three, M := by
    exact
      Finset.sum_nonneg
        (fun _ _ => hM)

  have h1 :
      0 ≤
        ∑ _j : PrimeTensor.Axis Depth.three,
          ∑ _i : PrimeTensor.Axis Depth.three, M := by
    exact
      Finset.sum_nonneg
        (fun _ _ =>
          Finset.sum_nonneg
            (fun _ _ => hM))

  have h2 :
      0 ≤
        ∑ _j : PrimeTensor.Axis Depth.three,
          ∑ _i : PrimeTensor.Axis Depth.three,
            ∑ _k : PrimeTensor.Axis Depth.three, M := by
    exact
      Finset.sum_nonneg
        (fun _ _ =>
          Finset.sum_nonneg
            (fun _ _ =>
              Finset.sum_nonneg
                (fun _ _ => hM)))

  have h3 :
      0 ≤
        ∑ _j : PrimeTensor.Axis Depth.three,
          ∑ _i : PrimeTensor.Axis Depth.three,
            ∑ _k : PrimeTensor.Axis Depth.three,
              ∑ _l : PrimeTensor.Axis Depth.three, M := by
    exact
      Finset.sum_nonneg
        (fun _ _ =>
          Finset.sum_nonneg
            (fun _ _ =>
              Finset.sum_nonneg
                (fun _ _ =>
                  Finset.sum_nonneg
                    (fun _ _ => hM))))

  unfold velocityH3CoordinateBudget

  linarith

/-- A componentwise H³ bound contains the corresponding integrability data. -/
theorem velocityH3IntegrableAt_of_bound
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t M : ℝ}
    (
      hBound :
        VelocityH3BoundAt
          u t M
    ) :
    VelocityH3IntegrableAt
      u t := by

  unfold VelocityH3BoundAt at hBound
  unfold VelocityH3IntegrableAt

  intro j

  have hj := hBound j

  dsimp only at hj ⊢

  refine
    ⟨
      hj.1.1,
      ?_,
      ?_,
      ?_
    ⟩

  · intro i
    exact
      (hj.2.1 i).1

  · intro i k
    exact
      (hj.2.2.1 i k).1

  · intro i k l
    exact
      (hj.2.2.2 i k l).1

/--
If each componentwise H³ summand is bounded by `M`, the canonical normalized
H³ energy is bounded by `velocityH3CoordinateBudget M`.
-/
theorem velocityH3EnergyAt_le_coordinateBudget_of_bound
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t M : ℝ}
    (
      hBound :
        VelocityH3BoundAt
          u t M
    ) :
    velocityH3EnergyAt u t
      ≤
    velocityH3CoordinateBudget M := by

  unfold VelocityH3BoundAt at hBound

  have h0 :
      velocityH3Energy0At u t
        ≤
      ∑ _j : PrimeTensor.Axis Depth.three, M := by

    unfold velocityH3Energy0At

    apply Finset.sum_le_sum

    intro j hjMem

    have hj := hBound j

    dsimp only at hj

    simpa [spatialSquareEnergy] using
      hj.1.2

  have h1 :
      velocityH3Energy1At u t
        ≤
      ∑ _j : PrimeTensor.Axis Depth.three,
        ∑ _i : PrimeTensor.Axis Depth.three, M := by

    unfold velocityH3Energy1At

    apply Finset.sum_le_sum

    intro j hjMem

    apply Finset.sum_le_sum

    intro i hiMem

    have hj := hBound j

    dsimp only at hj

    simpa [spatialSquareEnergy] using
      (hj.2.1 i).2

  have h2 :
      velocityH3Energy2At u t
        ≤
      ∑ _j : PrimeTensor.Axis Depth.three,
        ∑ _i : PrimeTensor.Axis Depth.three,
          ∑ _k : PrimeTensor.Axis Depth.three, M := by

    unfold velocityH3Energy2At

    apply Finset.sum_le_sum

    intro j hjMem

    apply Finset.sum_le_sum

    intro i hiMem

    apply Finset.sum_le_sum

    intro k hkMem

    have hj := hBound j

    dsimp only at hj

    simpa [spatialSquareEnergy] using
      (hj.2.2.1 i k).2

  have h3 :
      velocityH3Energy3At u t
        ≤
      ∑ _j : PrimeTensor.Axis Depth.three,
        ∑ _i : PrimeTensor.Axis Depth.three,
          ∑ _k : PrimeTensor.Axis Depth.three,
            ∑ _l : PrimeTensor.Axis Depth.three, M := by

    unfold velocityH3Energy3At

    apply Finset.sum_le_sum

    intro j hjMem

    apply Finset.sum_le_sum

    intro i hiMem

    apply Finset.sum_le_sum

    intro k hkMem

    apply Finset.sum_le_sum

    intro l hlMem

    have hj := hBound j

    dsimp only at hj

    simpa [spatialSquareEnergy] using
      (hj.2.2.2 i k l).2

  unfold velocityH3EnergyAt
  unfold velocityH3CoordinateBudget

  linarith

/-- Increasing the common scalar bound preserves `VelocityH3BoundAt`. -/
theorem velocityH3BoundAt_mono
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t M N : ℝ}
    (
      hBound :
        VelocityH3BoundAt
          u t M
    )
    (hMN : M ≤ N) :
    VelocityH3BoundAt
      u t N := by

  unfold VelocityH3BoundAt at hBound ⊢

  intro j

  have hj := hBound j

  dsimp only at hj ⊢

  refine
    ⟨
      ⟨
        hj.1.1,
        le_trans hj.1.2 hMN
      ⟩,
      ?_,
      ?_,
      ?_
    ⟩

  · intro i
    exact
      ⟨
        (hj.2.1 i).1,
        le_trans (hj.2.1 i).2 hMN
      ⟩

  · intro i k
    exact
      ⟨
        (hj.2.2.1 i k).1,
        le_trans (hj.2.2.1 i k).2 hMN
      ⟩

  · intro i k l
    exact
      ⟨
        (hj.2.2.2 i k l).1,
        le_trans (hj.2.2.2 i k l).2 hMN
      ⟩

/--
Uniform restart lifespan stated using the single canonical normalized H³
energy.

This is the scalar form closest to the usual local-well-posedness statement:
for every normalized energy ceiling `E`, there is a positive lifespan depending
only on `E`.
-/
def UniformCanonicalH3RealRestartLifespan : Prop :=
  ∃ lifespan : ℝ → ℝ,
    (
      ∀ E : ℝ,
        1 ≤ E →
          0 < lifespan E
    )
      ∧
    ∀
      (
        u :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three
      )
      (T t E : ℝ),
        LoggedPreterminalNavierStokesAdmissible
            u T
          →
        t ∈ Set.Ioo (0 : ℝ) T
          →
        1 ≤ E
          →
        VelocityH3IntegrableAt
            u t
          →
        velocityH3EnergyAt u t ≤ E
          →
        ∃
          (
            v :
              PrimeTensor.SpaceTimeVectorField
                ℝ ℝ ℝ Depth.three
          )
          (
            p :
              PrimeTensor.SpaceTimeScalarField
                ℝ ℝ ℝ Depth.three
          )
          (S : ℝ),
            t + lifespan E < S
              ∧
            RealRestartAgreesBeforeT
              u v T
              ∧
            PreterminalNavierStokes3
              v p S
              ∧
            RealVelocitySpatialC3
              v
              ∧
            RealVelocityThirdJetContinuousOn
              v S

/--
The scalar canonical-energy restart theorem implies the componentwise restart
frontier.  The lifespan is reparameterized by the finite coordinate budget.
-/
theorem uniformH3RealRestartLifespan_of_canonicalEnergy
    (
      hCanonical :
        UniformCanonicalH3RealRestartLifespan
    ) :
    UniformH3RealRestartLifespan := by

  rcases hCanonical with
    ⟨
      lifespan,
      hPositive,
      hRestart
    ⟩

  refine
    ⟨
      fun M =>
        lifespan
          (velocityH3CoordinateBudget M),
      ?_,
      ?_
    ⟩

  · intro M hM

    exact
      hPositive
        (velocityH3CoordinateBudget M)
        (one_le_velocityH3CoordinateBudget hM)

  · intro
      u T t M
      hAdmissible
      ht
      hM
      hBound

    have hNormalized :
        1 ≤ velocityH3CoordinateBudget M :=
      one_le_velocityH3CoordinateBudget
        hM

    have hIntegrable :
        VelocityH3IntegrableAt
          u t :=
      velocityH3IntegrableAt_of_bound
        hBound

    have hEnergy :
        velocityH3EnergyAt u t
          ≤
        velocityH3CoordinateBudget M :=
      velocityH3EnergyAt_le_coordinateBudget_of_bound
        hBound

    exact
      hRestart
        u T t
        (velocityH3CoordinateBudget M)
        hAdmissible
        ht
        hNormalized
        hIntegrable
        hEnergy

/--
Conversely, the componentwise restart frontier implies the scalar canonical
energy formulation.  The canonical finite-sum theorem bounds every individual
summand by the total energy, and monotonicity raises that common bound to the
supplied energy ceiling `E`.
-/
theorem uniformCanonicalH3RealRestartLifespan_of_uniformH3
    (
      hUniform :
        UniformH3RealRestartLifespan
    ) :
    UniformCanonicalH3RealRestartLifespan := by

  rcases hUniform with
    ⟨
      lifespan,
      hPositive,
      hRestart
    ⟩

  refine
    ⟨
      lifespan,
      ?_,
      ?_
    ⟩

  · intro E hE

    exact
      hPositive
        E
        (le_trans (by norm_num) hE)

  · intro
      u T t E
      hAdmissible
      ht
      hE
      hIntegrable
      hEnergy

    have hCanonicalBound :
        VelocityH3BoundAt
          u t
          (velocityH3EnergyAt u t) :=
      velocityH3BoundAt_canonical
        u t
        hIntegrable

    have hBound :
        VelocityH3BoundAt
          u t E :=
      velocityH3BoundAt_mono
        hCanonicalBound
        hEnergy

    exact
      hRestart
        u T t E
        hAdmissible
        ht
        (le_trans (by norm_num) hE)
        hBound

/-- The componentwise and canonical scalar restart formulations are equivalent. -/
theorem uniformCanonicalH3RealRestartLifespan_iff_uniformH3 :
    UniformCanonicalH3RealRestartLifespan
      ↔
    UniformH3RealRestartLifespan := by

  constructor

  · exact
      uniformH3RealRestartLifespan_of_canonicalEnergy

  · exact
      uniformCanonicalH3RealRestartLifespan_of_uniformH3

/-- The canonical-energy restart theorem discharges the H³ continuation frontier. -/
theorem h3ControlProducesExtension_of_canonicalEnergyLifespan
    (
      hCanonical :
        UniformCanonicalH3RealRestartLifespan
    ) :
    H3ControlProducesExtension := by

  exact
    h3ControlProducesExtension_of_uniformLifespan
      (
        uniformH3RealRestartLifespan_of_canonicalEnergy
          hCanonical
      )

end Euclidean
end Bridge
end PrimeTensor
