import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPDEPairingL2Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathClosedArbitraryFourthVelocityJets
import PrimeTensor.Fluid.Vorticity.H3.Axis.Sum
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Close the H³ diffusion sign frontier

The physical velocity jets needed by the viscous term are now closed through
order five.  This is enough to justify the whole-space diffusion integration
by parts directly, without an additional cutoff or decay hypothesis.

At each derivative order `|α| ≤ 3` and each coordinate `r`, write

    F = D^α u_j,
    G_r = D^α D_r u_j,
    K_r = D^α D_r² u_j.

Mixed-partial commutation identifies `D_r F = G_r` and `D_r G_r = K_r`.
All three fields belong to physical `L²`; hence the products required by
Mathlib's whole-space Fréchet integration-by-parts theorem are integrable.
Summing over the three spatial axes yields the exact diffusion pairing
identity and therefore nonpositivity of the full H³ diffusion contribution.

Consequently the scalar-sign BKM frontier reduces to pressure cancellation
alone.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathDiffusionSignClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathDiffusionSignClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic whole-space scalar diffusion IBP -/

private theorem integrable_mul_of_memLp_two_two_h3DiffusionSign
    {f g : ScalarField3}
    (hf : MemLp f 2 (volume : Measure Point3))
    (hg : MemLp g 2 (volume : Measure Point3)) :
    Integrable
      (fun x : Point3 => f x * g x)
      (volume : Measure Point3) := by
  have hMeas :
      AEStronglyMeasurable
        (fun x : Point3 => f x * g x)
        (volume : Measure Point3) :=
    hf.1.mul hg.1

  rw [← MeasureTheory.integrable_norm_iff hMeas]

  have hAbs :
      Integrable
        (fun x : Point3 => ‖f x‖ * ‖g x‖)
        (volume : Measure Point3) :=
    MemLp.integrable_mul hf.norm hg.norm

  simpa only [Real.norm_eq_abs, abs_mul] using hAbs

/--
A coordinate factorization of a Laplacian-type field gives the exact scalar
whole-space diffusion integration-by-parts identity.

`H r` is the first derivative of `f` in direction `r`, while `K r` is the
corresponding derivative of `H r`.  The final field `g` is their three-axis
sum.  Physical `L²` membership of `f`, `H r`, and `K r` supplies all product
integrability required by the Fréchet integration-by-parts theorem.
-/
private theorem diffusionPairingIntegrationByParts_of_coordinateFactorization
    {f g : ScalarField3}
    (H K : PrimeTensor.Axis Depth.three → ScalarField3)
    (hf1 : SpatialC1 f)
    (hH1 : ∀ r : PrimeTensor.Axis Depth.three, SpatialC1 (H r))
    (hfL2 : MemLp f 2 (volume : Measure Point3))
    (hHL2 : ∀ r : PrimeTensor.Axis Depth.three,
      MemLp (H r) 2 (volume : Measure Point3))
    (hKL2 : ∀ r : PrimeTensor.Axis Depth.three,
      MemLp (K r) 2 (volume : Measure Point3))
    (hDf : ∀ r : PrimeTensor.Axis Depth.three,
      spatial3.d r f = H r)
    (hDH : ∀ r : PrimeTensor.Axis Depth.three,
      spatial3.d r (H r) = K r)
    (hg :
      g =
        fun x : Point3 =>
          K xAxis x + (K yAxis x + K zAxis x)) :
    DiffusionPairingIntegrationByParts f g := by

  have hIBP
      (r : PrimeTensor.Axis Depth.three) :
      (∫ x : Point3, f x * K r x)
        =
      -(∫ x : Point3, H r x * H r x) := by

    have hDfAt :
        ∀ x : Point3,
          fderiv ℝ f x (axisDirection r) = H r x := by
      intro x
      rw [← congrFun (hDf r) x]
      exact
        (hf1.partialDeriv_eq_fderiv_axisDirection x r).symm

    have hDHAt :
        ∀ x : Point3,
          fderiv ℝ (H r) x (axisDirection r) = K r x := by
      intro x
      rw [← congrFun (hDH r) x]
      exact
        ((hH1 r).partialDeriv_eq_fderiv_axisDirection x r).symm

    have hDFG :
        Integrable
          (fun x : Point3 =>
            fderiv ℝ f x (axisDirection r) * H r x)
          (volume : Measure Point3) := by
      simpa only [hDfAt] using
        (integrable_mul_of_memLp_two_two_h3DiffusionSign
          (hHL2 r) (hHL2 r))

    have hFDG :
        Integrable
          (fun x : Point3 =>
            f x * fderiv ℝ (H r) x (axisDirection r))
          (volume : Measure Point3) := by
      simpa only [hDHAt] using
        (integrable_mul_of_memLp_two_two_h3DiffusionSign
          hfL2 (hKL2 r))

    have hFG :
        Integrable
          (fun x : Point3 => f x * H r x)
          (volume : Measure Point3) :=
      integrable_mul_of_memLp_two_two_h3DiffusionSign
        hfL2 (hHL2 r)

    have hRaw :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := volume)
        (f := f)
        (g := H r)
        (v := axisDirection r)
        hDFG
        hFDG
        hFG
        (fun x hx => hf1.differentiable_one.differentiableAt)
        (fun x hx => (hH1 r).differentiable_one.differentiableAt)

    simpa only [hDfAt, hDHAt] using hRaw

  have hKx :
      Integrable
        (fun x : Point3 => f x * K xAxis x)
        (volume : Measure Point3) :=
    integrable_mul_of_memLp_two_two_h3DiffusionSign
      hfL2 (hKL2 xAxis)

  have hKy :
      Integrable
        (fun x : Point3 => f x * K yAxis x)
        (volume : Measure Point3) :=
    integrable_mul_of_memLp_two_two_h3DiffusionSign
      hfL2 (hKL2 yAxis)

  have hKz :
      Integrable
        (fun x : Point3 => f x * K zAxis x)
        (volume : Measure Point3) :=
    integrable_mul_of_memLp_two_two_h3DiffusionSign
      hfL2 (hKL2 zAxis)

  unfold DiffusionPairingIntegrationByParts
  unfold spatialEnergyPairing
  unfold spatialSquareEnergy

  rw [hg]

  have hMul :
      (fun x : Point3 =>
        f x * (K xAxis x + (K yAxis x + K zAxis x)))
        =
      (fun x : Point3 =>
        f x * K xAxis x +
          (f x * K yAxis x + f x * K zAxis x)) := by
    funext x
    ring

  rw [hMul]

  have hIntYZ :
      (∫ x : Point3,
          f x * K yAxis x + f x * K zAxis x
        ∂(volume : Measure Point3))
        =
      (∫ x : Point3, f x * K yAxis x ∂(volume : Measure Point3))
        +
      (∫ x : Point3, f x * K zAxis x ∂(volume : Measure Point3)) := by
    simpa only [Pi.add_apply] using
      (MeasureTheory.integral_add hKy hKz)

  have hIntXYZ :
      (∫ x : Point3,
          f x * K xAxis x +
            (f x * K yAxis x + f x * K zAxis x)
        ∂(volume : Measure Point3))
        =
      (∫ x : Point3, f x * K xAxis x ∂(volume : Measure Point3))
        +
      (∫ x : Point3,
          f x * K yAxis x + f x * K zAxis x
        ∂(volume : Measure Point3)) := by
    simpa only [Pi.add_apply] using
      (MeasureTheory.integral_add hKx (hKy.add hKz))

  rw [hIntXYZ, hIntYZ]
  rw [axis_sum_three]
  rw [hDf xAxis, hDf yAxis, hDf zAxis]
  simp only [pow_two]
  rw [hIBP xAxis, hIBP yAxis, hIBP zAxis]
  ring

/-! ## High-diffusion component expansions -/

private theorem spatialC1_of_spatialC3_h3DiffusionSign
    {f : ScalarField3}
    (hf : SpatialC3 f) :
    SpatialC1 f := by
  exact hf.of_le (by norm_num)

private theorem firstPartial_spatialC1_of_spatialC3_h3DiffusionSign
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC1 (spatial3.d i f) := by
  have hf2 : SpatialC2 f :=
    hf.of_le (by norm_num)
  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hf2 i

private theorem secondPartial_spatialC1_of_spatialC3_h3DiffusionSign
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (i k : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (spatial3.d i (spatial3.d k f)) := by
  have hk2 : SpatialC2 (spatial3.d k f) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hf k
  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hk2 i

private theorem momentumDiffusion2Component_eq_fourthJetSum_h3DiffusionSign
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i k j : PrimeTensor.Axis Depth.three) :
    momentumDiffusion2Component
        (logSpaceTimeVectorField u)
        t i k j
      =
    fun x : Point3 =>
      spatial3.d i
          (spatial3.d k
            (spatial3.d xAxis
              (spatial3.d xAxis
                (loggedVelocityComponent u t j)))) x
        +
      (
        spatial3.d i
            (spatial3.d k
              (spatial3.d yAxis
                (spatial3.d yAxis
                  (loggedVelocityComponent u t j)))) x
          +
        spatial3.d i
            (spatial3.d k
              (spatial3.d zAxis
                (spatial3.d zAxis
                  (loggedVelocityComponent u t j)))) x
      ) := by

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hPure3
      (q : PrimeTensor.Axis Depth.three) :
      SpatialC3
        (spatial3.d q (spatial3.d q f)) := by
    dsimp only [f, loggedVelocityComponent]
    exact
      hClass.velocity_spatial_five
        t htTail j q q

  have hLap :
      momentumDiffusion0Component
          (logSpaceTimeVectorField u)
          t j
        =
      fun x : Point3 =>
        spatial3.d xAxis (spatial3.d xAxis f) x
          +
        (
          spatial3.d yAxis (spatial3.d yAxis f) x
            +
          spatial3.d zAxis (spatial3.d zAxis f) x
        ) := by
    funext x
    unfold momentumDiffusion0Component
    dsimp only [f, loggedVelocityComponent]
    exact
      laplacian3_eq
        (fun y : Point3 =>
          (logSpaceTimeVectorField u t y).component j)
        x

  have hFirst :
      spatial3.d k
          (momentumDiffusion0Component
            (logSpaceTimeVectorField u)
            t j)
        =
      fun x : Point3 =>
        spatial3.d k
            (spatial3.d xAxis (spatial3.d xAxis f)) x
          +
        (
          spatial3.d k
              (spatial3.d yAxis (spatial3.d yAxis f)) x
            +
          spatial3.d k
              (spatial3.d zAxis (spatial3.d zAxis f)) x
        ) := by

    have hx :
        SpatialC1
          (spatial3.d xAxis (spatial3.d xAxis f)) :=
      spatialC1_of_spatialC3_h3DiffusionSign
        (hPure3 xAxis)

    have hy :
        SpatialC1
          (spatial3.d yAxis (spatial3.d yAxis f)) :=
      spatialC1_of_spatialC3_h3DiffusionSign
        (hPure3 yAxis)

    have hz :
        SpatialC1
          (spatial3.d zAxis (spatial3.d zAxis f)) :=
      spatialC1_of_spatialC3_h3DiffusionSign
        (hPure3 zAxis)

    have hyz :
        SpatialC1
          (fun x : Point3 =>
            spatial3.d yAxis (spatial3.d yAxis f) x
              +
            spatial3.d zAxis (spatial3.d zAxis f) x) :=
      hy.add hz

    rw [hLap]
    funext x

    simp only [spatial3] at hx hy hz hyz ⊢

    rw [
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
        hx hyz x k,
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
        hy hz x k
    ]

  have hx1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d xAxis (spatial3.d xAxis f))) :=
    firstPartial_spatialC1_of_spatialC3_h3DiffusionSign
      (hPure3 xAxis) k

  have hy1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d yAxis (spatial3.d yAxis f))) :=
    firstPartial_spatialC1_of_spatialC3_h3DiffusionSign
      (hPure3 yAxis) k

  have hz1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d zAxis (spatial3.d zAxis f))) :=
    firstPartial_spatialC1_of_spatialC3_h3DiffusionSign
      (hPure3 zAxis) k

  unfold momentumDiffusion2Component momentumDiffusion1Component
  have hyz1 :
      SpatialC1
        (fun x : Point3 =>
          spatial3.d k
              (spatial3.d yAxis (spatial3.d yAxis f)) x
            +
          spatial3.d k
              (spatial3.d zAxis (spatial3.d zAxis f)) x) :=
    hy1.add hz1

  rw [hFirst]
  funext x

  dsimp only [f] at hx1 hy1 hz1 hyz1 ⊢
  simp only [spatial3] at hx1 hy1 hz1 hyz1 ⊢

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hx1 hyz1 x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hy1 hz1 x i
  ]

private theorem momentumDiffusion3Component_eq_fifthJetSum_h3DiffusionSign
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i k l j : PrimeTensor.Axis Depth.three) :
    momentumDiffusion3Component
        (logSpaceTimeVectorField u)
        t i k l j
      =
    fun x : Point3 =>
      spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (spatial3.d xAxis
                (spatial3.d xAxis
                  (loggedVelocityComponent u t j))))) x
        +
      (
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (spatial3.d yAxis
                  (spatial3.d yAxis
                    (loggedVelocityComponent u t j))))) x
          +
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (spatial3.d zAxis
                  (spatial3.d zAxis
                    (loggedVelocityComponent u t j))))) x
      ) := by

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hPure3
      (q : PrimeTensor.Axis Depth.three) :
      SpatialC3
        (spatial3.d q (spatial3.d q f)) := by
    dsimp only [f, loggedVelocityComponent]
    exact
      hClass.velocity_spatial_five
        t htTail j q q

  have hDiff2 :=
    momentumDiffusion2Component_eq_fourthJetSum_h3DiffusionSign
      hClass ht k l j

  have hx1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d l
            (spatial3.d xAxis (spatial3.d xAxis f)))) :=
    secondPartial_spatialC1_of_spatialC3_h3DiffusionSign
      (hPure3 xAxis) k l

  have hy1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d l
            (spatial3.d yAxis (spatial3.d yAxis f)))) :=
    secondPartial_spatialC1_of_spatialC3_h3DiffusionSign
      (hPure3 yAxis) k l

  have hz1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d l
            (spatial3.d zAxis (spatial3.d zAxis f)))) :=
    secondPartial_spatialC1_of_spatialC3_h3DiffusionSign
      (hPure3 zAxis) k l

  unfold momentumDiffusion3Component
  change
    spatial3.d i
        (momentumDiffusion2Component
          (logSpaceTimeVectorField u)
          t k l j)
      =
    _

  have hyz1 :
      SpatialC1
        (fun x : Point3 =>
          spatial3.d k
              (spatial3.d l
                (spatial3.d yAxis (spatial3.d yAxis f))) x
            +
          spatial3.d k
              (spatial3.d l
                (spatial3.d zAxis (spatial3.d zAxis f))) x) :=
    hy1.add hz1

  rw [hDiff2]
  funext x

  dsimp only [f] at hx1 hy1 hz1 hyz1 ⊢
  simp only [spatial3] at hx1 hy1 hz1 hyz1 ⊢

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hx1 hyz1 x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hy1 hz1 x i
  ]

/-! ## Path-level diffusion integration by parts -/

/--
Every strict H³ energy-class time satisfies the full diffusion integration by
parts package.  The top two derivative orders use the already-closed physical
fourth/fifth velocity jets.
-/
theorem h3PathEnergyClassProducesDiffusionIntegrationByParts_closed :
    ∀
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T : ℝ),
        LoggedPreterminalH3PathAdmissible u T →
        ∀ a : ℝ,
          ∀ hClass : PreterminalH3EnergyClass u a T,
            ∀ t : ℝ,
              ∀ ht : t ∈ Set.Ioo a T,
                H3DiffusionIntegrationByPartsAt u t := by

  intro u T hH3 a hClass t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  have hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  obtain ⟨p, hNS⟩ := hH3.navier_stokes

  have hBase3
      (j : PrimeTensor.Axis Depth.three) :
      SpatialC3 (loggedVelocityComponent u t j) := by
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component j)
    exact
      hNS.regularity.velocity_spatial_three
        t htAbs j

  have hBase2
      (j : PrimeTensor.Axis Depth.three) :
      SpatialC2 (loggedVelocityComponent u t j) :=
    (hBase3 j).toSpatialC2

  have hMem0
      (j : PrimeTensor.Axis Depth.three) :
      MemLp
        (loggedVelocityComponent u t j)
        2
        (volume : Measure Point3) := by
    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        hjMeas.1 hjInt.1)

  have hMem1
      (i j : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i (loggedVelocityComponent u t j))
        2
        (volume : Measure Point3) := by
    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.1 i) (hjInt.2.1 i))

  have hMem2
      (i k j : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u t j)))
        2
        (volume : Measure Point3) := by
    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.1 i k) (hjInt.2.2.1 i k))

  have hMem3
      (i k l j : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityComponent u t j))))
        2
        (volume : Measure Point3) := by
    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.2 i k l) (hjInt.2.2.2 i k l))

  have hJet :
      H3FourthFifthVelocityJetMemLp2At u t :=
    h3PathEnergyClassProducesFourthFifthVelocityJetMemLp2_closed
      u T hH3 a hClass t ht

  have hArb4 :
      H3ArbitraryFourthVelocityJetMemLp2At u t :=
    h3PathEnergyClassProducesArbitraryFourthVelocityJetMemLp2_closed
      u T hH3 a hClass t ht

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j

    let f : ScalarField3 :=
      loggedVelocityComponent u t j

    let H : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r => spatial3.d r f

    let K : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r => spatial3.d r (spatial3.d r f)

    have hf1 : SpatialC1 f :=
      (hBase3 j).of_le (by norm_num)

    have hH1 : ∀ r, SpatialC1 (H r) := by
      intro r
      dsimp only [H, f]
      exact
        ((hBase3 j).partialDeriv_contDiff_two r).of_le
          (by norm_num)

    have hDf : ∀ r, spatial3.d r f = H r := by
      intro r
      rfl

    have hDH : ∀ r, spatial3.d r (H r) = K r := by
      intro r
      rfl

    have hg :
        momentumDiffusion0Component
            (logSpaceTimeVectorField u) t j
          =
        fun x : Point3 =>
          K xAxis x + (K yAxis x + K zAxis x) := by
      funext x
      unfold momentumDiffusion0Component
      dsimp only [K, f, loggedVelocityComponent]
      exact
        laplacian3_eq
          (fun y : Point3 =>
            (logSpaceTimeVectorField u t y).component j)
          x

    exact
      diffusionPairingIntegrationByParts_of_coordinateFactorization
        H K
        hf1 hH1
        (by simpa only [f] using hMem0 j)
        (by
          intro r
          simpa only [H, f] using hMem1 r j)
        (by
          intro r
          simpa only [K, f] using hMem2 r r j)
        hDf hDH hg

  · intro i j

    let base : ScalarField3 :=
      loggedVelocityComponent u t j

    let f : ScalarField3 :=
      spatial3.d i base

    let H : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r => spatial3.d i (spatial3.d r base)

    let K : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r => spatial3.d i (spatial3.d r (spatial3.d r base))

    have hf1 : SpatialC1 f := by
      dsimp only [f, base]
      exact
        ((hBase3 j).partialDeriv_contDiff_two i).of_le
          (by norm_num)

    have hH1 : ∀ r, SpatialC1 (H r) := by
      intro r
      dsimp only [H, base]
      exact
        (hClass.velocity_spatial_five
          t htTail j i r).of_le
          (by norm_num)

    have hDf : ∀ r, spatial3.d r f = H r := by
      intro r
      dsimp only [f, H, base]
      funext x
      exact
        (hBase2 j).spatial_d_comm x r i

    have hDH : ∀ r, spatial3.d r (H r) = K r := by
      intro r
      dsimp only [H, K, base]
      funext x
      have hr2 :
          SpatialC2
            (spatial3.d r
              (loggedVelocityComponent u t j)) :=
        (hBase3 j).partialDeriv_contDiff_two r
      exact
        hr2.spatial_d_comm x r i

    have hg :
        momentumDiffusion1Component
            (logSpaceTimeVectorField u) t i j
          =
        fun x : Point3 =>
          K xAxis x + (K yAxis x + K zAxis x) := by
      funext x
      unfold momentumDiffusion1Component momentumDiffusion0Component
      dsimp only [K, base, loggedVelocityComponent]
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
          (hBase3 j) x i

    exact
      diffusionPairingIntegrationByParts_of_coordinateFactorization
        H K
        hf1 hH1
        (by simpa only [f, base] using hMem1 i j)
        (by
          intro r
          simpa only [H, base] using hMem2 i r j)
        (by
          intro r
          simpa only [K, base] using hMem3 i r r j)
        hDf hDH hg

  · intro i k j

    let base : ScalarField3 :=
      loggedVelocityComponent u t j

    let f : ScalarField3 :=
      spatial3.d i (spatial3.d k base)

    let H : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r =>
        spatial3.d i
          (spatial3.d k
            (spatial3.d r base))

    let K : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r =>
        spatial3.d i
          (spatial3.d k
            (spatial3.d r
              (spatial3.d r base)))

    have hf1 : SpatialC1 f := by
      dsimp only [f, base]
      exact
        (hClass.velocity_spatial_five
          t htTail j i k).of_le
          (by norm_num)

    have hH1 : ∀ r, SpatialC1 (H r) := by
      intro r
      dsimp only [H, base]
      have hkr3 :
          SpatialC3
            (spatial3.d k
              (spatial3.d r
                (loggedVelocityComponent u t j))) :=
        hClass.velocity_spatial_five
          t htTail j k r
      exact
        (hkr3.partialDeriv_contDiff_two i).of_le
          (by norm_num)

    have hDf : ∀ r, spatial3.d r f = H r := by
      intro r
      dsimp only [f, H, base]

      have hri :
          spatial3.d r
              (spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u t j)))
            =
          spatial3.d i
              (spatial3.d r
                (spatial3.d k
                  (loggedVelocityComponent u t j))) := by
        funext x
        exact
          ((hBase3 j).partialDeriv_contDiff_two k).spatial_d_comm
            x r i

      have hrk :
          spatial3.d r
              (spatial3.d k
                (loggedVelocityComponent u t j))
            =
          spatial3.d k
              (spatial3.d r
                (loggedVelocityComponent u t j)) := by
        funext x
        exact
          (hBase2 j).spatial_d_comm x r k

      rw [hri, hrk]

    have hDH : ∀ r, spatial3.d r (H r) = K r := by
      intro r
      dsimp only [H, K, base]

      have hri :
          spatial3.d r
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d r
                    (loggedVelocityComponent u t j))))
            =
          spatial3.d i
              (spatial3.d r
                (spatial3.d k
                  (spatial3.d r
                    (loggedVelocityComponent u t j)))) := by
        funext x
        have hkr2 :
            SpatialC2
              (spatial3.d k
                (spatial3.d r
                  (loggedVelocityComponent u t j))) :=
          (hClass.velocity_spatial_five
            t htTail j k r).toSpatialC2
        exact
          hkr2.spatial_d_comm x r i

      have hrk :
          spatial3.d r
              (spatial3.d k
                (spatial3.d r
                  (loggedVelocityComponent u t j)))
            =
          spatial3.d k
              (spatial3.d r
                (spatial3.d r
                  (loggedVelocityComponent u t j))) := by
        funext x
        have hr2 :
            SpatialC2
              (spatial3.d r
                (loggedVelocityComponent u t j)) :=
          (hBase3 j).partialDeriv_contDiff_two r
        exact
          hr2.spatial_d_comm x r k

      rw [hri, hrk]

    have hg :
        momentumDiffusion2Component
            (logSpaceTimeVectorField u) t i k j
          =
        fun x : Point3 =>
          K xAxis x + (K yAxis x + K zAxis x) := by
      simpa only [K, base] using
        (momentumDiffusion2Component_eq_fourthJetSum_h3DiffusionSign
          hClass ht i k j)

    exact
      diffusionPairingIntegrationByParts_of_coordinateFactorization
        H K
        hf1 hH1
        (by simpa only [f, base] using hMem2 i k j)
        (by
          intro r
          simpa only [H, base] using hMem3 i k r j)
        (by
          intro r
          simpa only [K, base] using hJet.1 i k r j)
        hDf hDH hg

  · intro i k l j

    let base : ScalarField3 :=
      loggedVelocityComponent u t j

    let f : ScalarField3 :=
      spatial3.d i
        (spatial3.d k
          (spatial3.d l base))

    let H : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r =>
        spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (spatial3.d r base)))

    let K : PrimeTensor.Axis Depth.three → ScalarField3 :=
      fun r =>
        spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (spatial3.d r
                (spatial3.d r base))))

    have hf1 : SpatialC1 f := by
      dsimp only [f, base]
      have hkl3 :
          SpatialC3
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityComponent u t j))) :=
        hClass.velocity_spatial_five
          t htTail j k l
      exact
        (hkl3.partialDeriv_contDiff_two i).of_le
          (by norm_num)

    have hH1 : ∀ r, SpatialC1 (H r) := by
      intro r
      dsimp only [H, base]
      have hlr3 :
          SpatialC3
            (spatial3.d l
              (spatial3.d r
                (loggedVelocityComponent u t j))) :=
        hClass.velocity_spatial_five
          t htTail j l r
      have hklr2 :
          SpatialC2
            (spatial3.d k
              (spatial3.d l
                (spatial3.d r
                  (loggedVelocityComponent u t j)))) :=
        hlr3.partialDeriv_contDiff_two k
      exact
        hklr2.partialDeriv_contDiff_one i

    have hDf : ∀ r, spatial3.d r f = H r := by
      intro r
      dsimp only [f, H, base]

      have hri :
          spatial3.d r
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j))))
            =
          spatial3.d i
              (spatial3.d r
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u t j)))) := by
        funext x
        have hkl2 :
            SpatialC2
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j))) :=
          (hClass.velocity_spatial_five
            t htTail j k l).toSpatialC2
        exact
          hkl2.spatial_d_comm x r i

      have hrk :
          spatial3.d r
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j)))
            =
          spatial3.d k
              (spatial3.d r
                (spatial3.d l
                  (loggedVelocityComponent u t j))) := by
        funext x
        have hl2 :
            SpatialC2
              (spatial3.d l
                (loggedVelocityComponent u t j)) :=
          (hBase3 j).partialDeriv_contDiff_two l
        exact
          hl2.spatial_d_comm x r k

      have hrl :
          spatial3.d r
              (spatial3.d l
                (loggedVelocityComponent u t j))
            =
          spatial3.d l
              (spatial3.d r
                (loggedVelocityComponent u t j)) := by
        funext x
        exact
          (hBase2 j).spatial_d_comm x r l

      rw [hri, hrk, hrl]

    have hDH : ∀ r, spatial3.d r (H r) = K r := by
      intro r
      dsimp only [H, K, base]

      have hri :
          spatial3.d r
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (spatial3.d r
                      (loggedVelocityComponent u t j)))))
            =
          spatial3.d i
              (spatial3.d r
                (spatial3.d k
                  (spatial3.d l
                    (spatial3.d r
                      (loggedVelocityComponent u t j))))) := by
        funext x
        have hlr3 :
            SpatialC3
              (spatial3.d l
                (spatial3.d r
                  (loggedVelocityComponent u t j))) :=
          hClass.velocity_spatial_five
            t htTail j l r
        have hklr2 :
            SpatialC2
              (spatial3.d k
                (spatial3.d l
                  (spatial3.d r
                    (loggedVelocityComponent u t j)))) :=
          hlr3.partialDeriv_contDiff_two k
        exact
          hklr2.spatial_d_comm x r i

      have hrk :
          spatial3.d r
              (spatial3.d k
                (spatial3.d l
                  (spatial3.d r
                    (loggedVelocityComponent u t j))))
            =
          spatial3.d k
              (spatial3.d r
                (spatial3.d l
                  (spatial3.d r
                    (loggedVelocityComponent u t j)))) := by
        funext x
        have hlr2 :
            SpatialC2
              (spatial3.d l
                (spatial3.d r
                  (loggedVelocityComponent u t j))) :=
          (hClass.velocity_spatial_five
            t htTail j l r).toSpatialC2
        exact
          hlr2.spatial_d_comm x r k

      have hrl :
          spatial3.d r
              (spatial3.d l
                (spatial3.d r
                  (loggedVelocityComponent u t j)))
            =
          spatial3.d l
              (spatial3.d r
                (spatial3.d r
                  (loggedVelocityComponent u t j))) := by
        funext x
        have hr2 :
            SpatialC2
              (spatial3.d r
                (loggedVelocityComponent u t j)) :=
          (hBase3 j).partialDeriv_contDiff_two r
        exact
          hr2.spatial_d_comm x r l

      rw [hri, hrk, hrl]

    have hg :
        momentumDiffusion3Component
            (logSpaceTimeVectorField u) t i k l j
          =
        fun x : Point3 =>
          K xAxis x + (K yAxis x + K zAxis x) := by
      simpa only [K, base] using
        (momentumDiffusion3Component_eq_fifthJetSum_h3DiffusionSign
          hClass ht i k l j)

    exact
      diffusionPairingIntegrationByParts_of_coordinateFactorization
        H K
        hf1 hH1
        (by simpa only [f, base] using hMem3 i k l j)
        (by
          intro r
          simpa only [H, base] using hArb4 i k l r j)
        (by
          intro r
          simpa only [K, base] using hJet.2 i k l r j)
        hDf hDH hg

/-- The full H³ diffusion contribution is nonpositive at every strict path
energy-class time. -/
def H3PathEnergyClassProducesDiffusionNonpositivity : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              velocityH3DiffusionDerivativeAt u t ≤ 0

/-- Diffusion nonpositivity is now closed outright. -/
theorem h3PathEnergyClassProducesDiffusionNonpositivity_closed :
    H3PathEnergyClassProducesDiffusionNonpositivity := by
  intro u T hH3 a hClass t ht
  exact
    velocityH3DiffusionDerivativeAt_nonpos
      (h3PathEnergyClassProducesDiffusionIntegrationByParts_closed
        u T hH3 a hClass t ht)

/-! ## Reduce scalar signs to pressure cancellation -/

/-- Pressure cancellation is the only remaining scalar-sign input. -/
def H3PathEnergyClassProducesPressureCancellation : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              velocityH3PressureDerivativeAt
                  u
                  (h3EnergyClassSplitPressureAt hClass ht)
                  t
                =
              0

/-- Closed diffusion plus pressure cancellation reconstructs the historical
full scalar-sign package. -/
theorem h3PathEnergyClassProducesFullScalarSigns_of_pressureCancellation
    (hPressure : H3PathEnergyClassProducesPressureCancellation) :
    H3PathEnergyClassProducesFullScalarSigns := by
  intro u T hH3 a hClass t ht
  exact
    ⟨
      hPressure u T hH3 a hClass t ht,
      h3PathEnergyClassProducesDiffusionNonpositivity_closed
        u T hH3 a hClass t ht
    ⟩

/-- With physical diffusion IBP closed, the current BKM frontier retains only
low-tail control, the exact energy derivative identities, and pressure
cancellation. -/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_pressureCancellation
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPressure :
      H3PathEnergyClassProducesPressureCancellation) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_fullScalarSigns
      hLow
      hDerivative
      (h3PathEnergyClassProducesFullScalarSigns_of_pressureCancellation
        hPressure)

end

end Euclidean
end Bridge
end PrimeTensor
