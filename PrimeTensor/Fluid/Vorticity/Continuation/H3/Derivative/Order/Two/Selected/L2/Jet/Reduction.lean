import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Second.Velocity.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.L2.Jet.Reduction
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Reduce selected order-two H³ energy differentiation to strong L² second-jet derivatives

The selected restart already has:

* exact pointwise order-two mixed time-space differentiation;
* physical `L²` control of every ordered second spatial velocity derivative.

Package each selected second jet as an `H3ScalarL2` path.  On the open restart
interval its squared Hilbert norm is exactly the corresponding
`spatialSquareEnergy`.

Therefore a genuine strong `L²` derivative for each of the 27 second-jet slots

    d/dq [∂ᵢ∂ₖ Sⱼ]_{L²}
      = [∂ᵢ∂ₖ∂ₜ Sⱼ]_{L²}

immediately gives the exact selected order-two scalar energy derivative by
Hilbert norm-square calculus and finite summation.

The package is made total on `ℝ` by using zero outside the strict restart
interval.  All derivative arguments occur at interior points, where the package
is exactly the physical selected second jet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedL2JetReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderTwoSelectedL2JetReduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every selected second spatial velocity coordinate belongs to physical `L²`
at a strict elapsed restart time. -/
theorem h3PreterminalSelectedWeakStrongVelocity_spatial_d_two_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hr :
      r ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j i k : PrimeTensor.Axis Depth.three) :
    MemLp
      (spatial3.d i
        (spatial3.d k
          (fun x : Point3 =>
            ((h3PreterminalSelectedWeakStrongVelocity
              (one_pos : (0 : ℝ) < 1)
              hNS ht₀ hE hTail)
              r x).component j)))
      2
      (volume : Measure Point3) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hEpos hU₀

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hSelectedComponent :
      (fun x : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht₀ hE hTail)
          r x).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W r jf) := by
    funext x

    unfold h3PreterminalSelectedWeakStrongVelocity
    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

    rw [h3SpectralRealVelocityOfPath_component]

    rfl

  have hRep :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r jf))))
        2
        (volume : Measure Point3) := by
    dsimp only [W]

    exact
      h3SelectedRestartRealVelocity_spatial_d_two_memLp2
        (one_pos : (0 : ℝ) < 1)
        U₀ hEpos hU₀
        hr.1 hr.2
        jf i k

  have hDerivativeEq :
      spatial3.d i
          (spatial3.d k
            (fun x : Point3 =>
              ((h3PreterminalSelectedWeakStrongVelocity
                (one_pos : (0 : ℝ) < 1)
                hNS ht₀ hE hTail)
                r x).component j))
        =
      spatial3.d i
        (spatial3.d k
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r jf))) :=
    congrArg
      (fun f : ScalarField3 =>
        spatial3.d i (spatial3.d k f))
      hSelectedComponent

  exact
    (memLp_congr_ae
      (Filter.Eventually.of_forall
        (fun x =>
          congrFun hDerivativeEq x))).2
      hRep

/-- One selected second spatial jet, canonically packaged in physical `L²`.
Outside the strict restart interval the package is set to zero; this makes the
path total on `ℝ` while preserving the genuine field on every interior
neighborhood used below. -/
noncomputable def h3PreterminalSelectedSecondJetScalarL2At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (r : ℝ)
    (j i k : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  if hr :
      r ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)
  then
    (h3PreterminalSelectedWeakStrongVelocity_spatial_d_two_memLp_two
      hNS ht₀ hE hTail hr j i k).toLp
      (spatial3.d i
        (spatial3.d k
          (fun x : Point3 =>
            ((h3PreterminalSelectedWeakStrongVelocity
              (one_pos : (0 : ℝ) < 1)
              hNS ht₀ hE hTail)
              r x).component j)))
  else
    0

/-- On the strict restart interval the second-jet `L²` package represents the
literal selected second spatial derivative almost everywhere. -/
theorem h3PreterminalSelectedSecondJetScalarL2At_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hr :
      r ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j i k : PrimeTensor.Axis Depth.three) :
    (((h3PreterminalSelectedSecondJetScalarL2At
          hNS ht₀ hE hTail r j i k : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d i
      (spatial3.d k
        (fun x : Point3 =>
          ((h3PreterminalSelectedWeakStrongVelocity
            (one_pos : (0 : ℝ) < 1)
            hNS ht₀ hE hTail)
            r x).component j))) := by
  unfold h3PreterminalSelectedSecondJetScalarL2At
  rw [dif_pos hr]

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3PreterminalSelectedWeakStrongVelocity_spatial_d_two_memLp_two
        hNS ht₀ hE hTail hr j i k)

/-- On the strict restart interval the squared Hilbert norm of one selected
second-jet package is its literal spatial square energy. -/
theorem norm_sq_h3PreterminalSelectedSecondJetScalarL2At_eq_spatialSquareEnergy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hr :
      r ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j i k : PrimeTensor.Axis Depth.three) :
    ‖h3PreterminalSelectedSecondJetScalarL2At
        hNS ht₀ hE hTail r j i k‖ ^ 2
      =
    spatialSquareEnergy
      (spatial3.d i
        (spatial3.d k
          (fun x : Point3 =>
            ((h3PreterminalSelectedWeakStrongVelocity
              (one_pos : (0 : ℝ) < 1)
              hNS ht₀ hE hTail)
              r x).component j))) := by
  rw [h3ScalarL2_norm_sq_eq_spatialSquareEnergy_coe]

  unfold spatialSquareEnergy

  apply integral_congr_ae

  filter_upwards [
    h3PreterminalSelectedSecondJetScalarL2At_ae
      hNS ht₀ hE hTail hr j i k
  ] with x hx

  rw [hx]

/-- The remaining selected order-two Banach-valued frontier.

At every strict elapsed restart time and every ordered second spatial jet slot,
the canonical physical `L²` path has a genuine strong derivative whose a.e.
representative is the literal second spatial derivative of the selected
temporal derivative. -/
def H3CanonicalSelectedOrder2RelativePhysicalL2StrongDerivativeOnRestartRadius :
    Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        ∀ j i k : PrimeTensor.Axis Depth.three,
          ∃ D : H3ScalarL2,
            HasDerivAt
              (fun r : ℝ =>
                h3PreterminalSelectedSecondJetScalarL2At
                  hNS ht₀ hE hTail r j i k)
              D
              q
            ∧
            (((D : H3ScalarL2) : Point3 → ℝ)
              =ᵐ[(volume : Measure Point3)]
            spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  temporal.d
                    (fun r : ℝ =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        (h3PreterminalSelectedDecoderAnchorState
                          hNS ht₀ hTail)
                        (lt_of_lt_of_le zero_lt_one hE)
                        (norm_h3PreterminalSelectedDecoderAnchorState_le
                          hNS ht₀ hE hTail)
                        r y).component j)
                    q)))

/-- Pure selected-restart relative order-two scalar energy differentiation
target. -/
def H3CanonicalSelectedOrder2RelativeEnergyDerivativeOnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        HasDerivAt
          (fun r : ℝ =>
            ∑ j : PrimeTensor.Axis Depth.three,
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  spatialSquareEnergy
                    (spatial3.d i
                      (spatial3.d k
                        (fun y : Point3 =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            (h3PreterminalSelectedDecoderAnchorState
                              hNS ht₀ hTail)
                            (lt_of_lt_of_le zero_lt_one hE)
                            (norm_h3PreterminalSelectedDecoderAnchorState_le
                              hNS ht₀ hE hTail)
                            r y).component j))))
          (∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d i
                    (spatial3.d k
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          (h3PreterminalSelectedDecoderAnchorState
                            hNS ht₀ hTail)
                          (lt_of_lt_of_le zero_lt_one hE)
                          (norm_h3PreterminalSelectedDecoderAnchorState_le
                            hNS ht₀ hE hTail)
                          q y).component j)))
                  (spatial3.d i
                    (spatial3.d k
                      (fun y : Point3 =>
                        temporal.d
                          (fun r : ℝ =>
                            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                              (one_pos : (0 : ℝ) < 1)
                              (h3PreterminalSelectedDecoderAnchorState
                                hNS ht₀ hTail)
                              (lt_of_lt_of_le zero_lt_one hE)
                              (norm_h3PreterminalSelectedDecoderAnchorState_le
                                hNS ht₀ hE hTail)
                              r y).component j)
                          q))))
          q

/-- Strong selected second-jet `L²` differentiation implies the complete
selected relative order-two scalar energy derivative. -/
theorem h3CanonicalSelectedOrder2RelativeEnergyDerivativeOnRestartRadius_of_physicalL2StrongDerivative
    (hStrong :
      H3CanonicalSelectedOrder2RelativePhysicalL2StrongDerivativeOnRestartRadius) :
    H3CanonicalSelectedOrder2RelativeEnergyDerivativeOnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail
  intro q hq

  let selected :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht₀ hE hTail

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hNeighborhood :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 q := by
    exact
      IsOpen.mem_nhds
        isOpen_Ioo
        (by simpa only [R] using hq)

  have hEach :
      ∀ j i k : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun r : ℝ =>
            spatialSquareEnergy
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      (h3PreterminalSelectedDecoderAnchorState
                        hNS ht₀ hTail)
                      (lt_of_lt_of_le zero_lt_one hE)
                      (norm_h3PreterminalSelectedDecoderAnchorState_le
                        hNS ht₀ hE hTail)
                      r y).component j))))
          (spatialEnergyPairing
            (spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalSelectedDecoderAnchorState
                      hNS ht₀ hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalSelectedDecoderAnchorState_le
                      hNS ht₀ hE hTail)
                    q y).component j)))
            (spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  temporal.d
                    (fun r : ℝ =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        (h3PreterminalSelectedDecoderAnchorState
                          hNS ht₀ hTail)
                        (lt_of_lt_of_le zero_lt_one hE)
                        (norm_h3PreterminalSelectedDecoderAnchorState_le
                          hNS ht₀ hE hTail)
                        r y).component j)
                    q))))
          q := by
    intro j i k

    rcases
      hStrong E u T t₀ hNS ht₀ hE hTail
        q hq j i k
    with
      ⟨D, hD, hDae⟩

    let X : H3ScalarL2 :=
      h3PreterminalSelectedSecondJetScalarL2At
        hNS ht₀ hE hTail q j i k

    have hXae :
        (((X : H3ScalarL2) : Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d i
          (spatial3.d k
            (fun y : Point3 =>
              (selected q y).component j))) := by
      dsimp only [X]
      simpa only [selected] using
        h3PreterminalSelectedSecondJetScalarL2At_ae
          hNS ht₀ hE hTail hq j i k

    have hDaeSelected :
        (((D : H3ScalarL2) : Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d i
          (spatial3.d k
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (selected r y).component j)
                q))) := by
      simpa only [
        selected,
        h3PreterminalSelectedWeakStrongVelocity
      ] using hDae

    have hCoefficient :
        2 * inner ℝ X D
          =
        spatialEnergyPairing
          (spatial3.d i
            (spatial3.d k
              (fun y : Point3 =>
                (selected q y).component j)))
          (spatial3.d i
            (spatial3.d k
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    (selected r y).component j)
                  q))) := by
      unfold spatialEnergyPairing
      congr 1

      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae

      filter_upwards [hXae, hDaeSelected] with y hX hDy

      rw [hX, hDy]
      simp [RCLike.inner_apply, mul_comm]

    have hNorm :
        HasDerivAt
          (fun r : ℝ =>
            ‖h3PreterminalSelectedSecondJetScalarL2At
                hNS ht₀ hE hTail r j i k‖ ^ 2)
          (2 * inner ℝ X D)
          q := by
      have h := hD.norm_sq
      dsimp only [X] at h ⊢
      exact h

    have hNormCoefficient :
        HasDerivAt
          (fun r : ℝ =>
            ‖h3PreterminalSelectedSecondJetScalarL2At
                hNS ht₀ hE hTail r j i k‖ ^ 2)
          (spatialEnergyPairing
            (spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  (selected q y).component j)))
            (spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  temporal.d
                    (fun r : ℝ =>
                      (selected r y).component j)
                    q))))
          q :=
      hNorm.congr_deriv hCoefficient

    have hEnergyEq :
        (fun r : ℝ =>
          ‖h3PreterminalSelectedSecondJetScalarL2At
              hNS ht₀ hE hTail r j i k‖ ^ 2)
          =ᶠ[𝓝 q]
        (fun r : ℝ =>
          spatialSquareEnergy
            (spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  (selected r y).component j)))) := by
      filter_upwards [hNeighborhood] with r hr

      simpa only [selected, R] using
        norm_sq_h3PreterminalSelectedSecondJetScalarL2At_eq_spatialSquareEnergy
          hNS ht₀ hE hTail
          (by simpa only [R] using hr)
          j i k

    have hSelected :
        HasDerivAt
          (fun r : ℝ =>
            spatialSquareEnergy
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    (selected r y).component j))))
          (spatialEnergyPairing
            (spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  (selected q y).component j)))
            (spatial3.d i
              (spatial3.d k
                (fun y : Point3 =>
                  temporal.d
                    (fun r : ℝ =>
                      (selected r y).component j)
                    q))))
          q :=
      hNormCoefficient.congr_of_eventuallyEq
        hEnergyEq.symm

    simpa only [
      selected,
      h3PreterminalSelectedWeakStrongVelocity
    ] using hSelected

  have hK :
      ∀ j i : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun r : ℝ =>
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        (h3PreterminalSelectedDecoderAnchorState
                          hNS ht₀ hTail)
                        (lt_of_lt_of_le zero_lt_one hE)
                        (norm_h3PreterminalSelectedDecoderAnchorState_le
                          hNS ht₀ hE hTail)
                        r y).component j))))
          (∑ k : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      (one_pos : (0 : ℝ) < 1)
                      (h3PreterminalSelectedDecoderAnchorState
                        hNS ht₀ hTail)
                      (lt_of_lt_of_le zero_lt_one hE)
                      (norm_h3PreterminalSelectedDecoderAnchorState_le
                        hNS ht₀ hE hTail)
                      q y).component j)))
              (spatial3.d i
                (spatial3.d k
                  (fun y : Point3 =>
                    temporal.d
                      (fun r : ℝ =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          (h3PreterminalSelectedDecoderAnchorState
                            hNS ht₀ hTail)
                          (lt_of_lt_of_le zero_lt_one hE)
                          (norm_h3PreterminalSelectedDecoderAnchorState_le
                            hNS ht₀ hE hTail)
                          r y).component j)
                      q))))
          q := by
    intro j i
    apply HasDerivAt.fun_sum
    intro k hk
    exact hEach j i k

  have hI :
      ∀ j : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun r : ℝ =>
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d i
                    (spatial3.d k
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          (h3PreterminalSelectedDecoderAnchorState
                            hNS ht₀ hTail)
                          (lt_of_lt_of_le zero_lt_one hE)
                          (norm_h3PreterminalSelectedDecoderAnchorState_le
                            hNS ht₀ hE hTail)
                          r y).component j))))
          (∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        (h3PreterminalSelectedDecoderAnchorState
                          hNS ht₀ hTail)
                        (lt_of_lt_of_le zero_lt_one hE)
                        (norm_h3PreterminalSelectedDecoderAnchorState_le
                          hNS ht₀ hE hTail)
                        q y).component j)))
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      temporal.d
                        (fun r : ℝ =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            (h3PreterminalSelectedDecoderAnchorState
                              hNS ht₀ hTail)
                            (lt_of_lt_of_le zero_lt_one hE)
                            (norm_h3PreterminalSelectedDecoderAnchorState_le
                              hNS ht₀ hE hTail)
                            r y).component j)
                        q))))
          q := by
    intro j
    apply HasDerivAt.fun_sum
    intro i hi
    exact hK j i

  have hSum :
      HasDerivAt
        (fun r : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d i
                    (spatial3.d k
                      (fun y : Point3 =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          (h3PreterminalSelectedDecoderAnchorState
                            hNS ht₀ hTail)
                          (lt_of_lt_of_le zero_lt_one hE)
                          (norm_h3PreterminalSelectedDecoderAnchorState_le
                            hNS ht₀ hE hTail)
                          r y).component j))))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        (h3PreterminalSelectedDecoderAnchorState
                          hNS ht₀ hTail)
                        (lt_of_lt_of_le zero_lt_one hE)
                        (norm_h3PreterminalSelectedDecoderAnchorState_le
                          hNS ht₀ hE hTail)
                        q y).component j)))
                (spatial3.d i
                  (spatial3.d k
                    (fun y : Point3 =>
                      temporal.d
                        (fun r : ℝ =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            (h3PreterminalSelectedDecoderAnchorState
                              hNS ht₀ hTail)
                            (lt_of_lt_of_le zero_lt_one hE)
                            (norm_h3PreterminalSelectedDecoderAnchorState_le
                              hNS ht₀ hE hTail)
                            r y).component j)
                        q))))
        q := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact hI j

  exact hSum

end

end Euclidean
end Bridge
end PrimeTensor
