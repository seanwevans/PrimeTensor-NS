import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderThreeEnergyDerivativeFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedCubicVelocityPhysicalL2Identification

/-!
# Reduce selected order-three energy differentiation to strong physical L²

The public BKM frontier is now the order-three scalar energy identity alone.
The selected third spatial velocity jet is already packaged in physical real
`L²` by the earlier cubic-velocity chain.  This file puts that existing package
into the same Hilbert-space architecture that closed order two.

For every ordered third jet we define a total `H3ScalarL2` path and isolate the
remaining Banach-valued target

    d/dq D³S_j(q) = D³ ∂_q S_j(q)     in physical L².

As before, this strong derivative differentiates the squared Hilbert norm, and
finite summation gives the selected relative order-three scalar energy
identity.  No new PDE estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedL2JetReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Total physical `L²` package for one ordered selected third spatial jet. -/
noncomputable def h3PreterminalSelectedThirdJetScalarL2At
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (r : ℝ)
    (j i k l : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  if hr :
      r ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)
  then
    h3SelectedRestartRealVelocityThirdCoordinateL2
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      ⟨r, hr⟩
      (h3ClassicalizationFinOfAxis j)
      i k l
  else
    0

/-- On the strict restart interval the third-jet package represents the literal
ordered third spatial derivative of the selected real velocity. -/
theorem h3PreterminalSelectedThirdJetScalarL2At_ae
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
    (j i k l : PrimeTensor.Axis Depth.three) :
    (((h3PreterminalSelectedThirdJetScalarL2At
          hNS ht₀ hE hTail r j i k l : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d i
      (spatial3.d k
        (spatial3.d l
          (fun y : Point3 =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              r y).component j)))) := by

  unfold h3PreterminalSelectedThirdJetScalarL2At
  rw [dif_pos hr]

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxis :
      h3AxisOfFin3 jf = j := by
    dsimp only [jf]
    exact h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hComponent :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ r y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W r jf) := by
    funext y
    rw [← hAxis]
    simp only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      W
    ]

  have hSpatial :
      spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (fun y : Point3 =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  (one_pos : (0 : ℝ) < 1)
                  U₀ hA hU₀ r y).component j)))
        =
      spatial3.d i
        (spatial3.d k
          (spatial3.d l
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r jf)))) := by
    exact
      congrArg
        (fun f : ScalarField3 =>
          spatial3.d i
            (spatial3.d k
              (spatial3.d l f)))
        hComponent

  rw [
    h3SelectedRestartRealVelocityThirdCoordinateL2_eq_rawPhysicalL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      ⟨r, hr⟩ jf i k l
  ]

  have hPackage :=
    h3SelectedRestartRawThirdCoordinatePhysicalL2_ae_eq_spatial_d_three
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hr.1 hr.2 jf i k l

  filter_upwards [hPackage] with y hy

  rw [hy]
  exact congrFun hSpatial y |>.symm

/-- Squared Hilbert norm of one selected third-jet package equals its literal
spatial square energy on the strict restart interval. -/
theorem norm_sq_h3PreterminalSelectedThirdJetScalarL2At_eq_spatialSquareEnergy
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
    (j i k l : PrimeTensor.Axis Depth.three) :
    ‖h3PreterminalSelectedThirdJetScalarL2At
        hNS ht₀ hE hTail r j i k l‖ ^ 2
      =
    spatialSquareEnergy
      (spatial3.d i
        (spatial3.d k
          (spatial3.d l
            (fun y : Point3 =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                r y).component j)))) := by

  rw [h3ScalarL2_norm_sq_eq_spatialSquareEnergy_coe]
  unfold spatialSquareEnergy
  apply integral_congr_ae
  filter_upwards [
    h3PreterminalSelectedThirdJetScalarL2At_ae
      hNS ht₀ hE hTail hr j i k l
  ] with y hy
  rw [hy]

/-- Remaining selected order-three Banach-valued frontier. -/
def H3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius :
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
        ∀ j i k l : PrimeTensor.Axis Depth.three,
          ∃ D : H3ScalarL2,
            HasDerivAt
              (fun r : ℝ =>
                h3PreterminalSelectedThirdJetScalarL2At
                  hNS ht₀ hE hTail r j i k l)
              D
              q
            ∧
            (((D : H3ScalarL2) : Point3 → ℝ)
              =ᵐ[(volume : Measure Point3)]
            spatial3.d i
              (spatial3.d k
                (spatial3.d l
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

/-- Pure selected-restart relative order-three scalar energy differentiation
target. -/
def H3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius : Prop :=
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
                  ∑ l : PrimeTensor.Axis Depth.three,
                    spatialSquareEnergy
                      (spatial3.d i
                        (spatial3.d k
                          (spatial3.d l
                            (fun y : Point3 =>
                              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                                (one_pos : (0 : ℝ) < 1)
                                (h3PreterminalSelectedDecoderAnchorState
                                  hNS ht₀ hTail)
                                (lt_of_lt_of_le zero_lt_one hE)
                                (norm_h3PreterminalSelectedDecoderAnchorState_le
                                  hNS ht₀ hE hTail)
                                r y).component j)))))
          (∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  spatialEnergyPairing
                    (spatial3.d i
                      (spatial3.d k
                        (spatial3.d l
                          (fun y : Point3 =>
                            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                              (one_pos : (0 : ℝ) < 1)
                              (h3PreterminalSelectedDecoderAnchorState
                                hNS ht₀ hTail)
                              (lt_of_lt_of_le zero_lt_one hE)
                              (norm_h3PreterminalSelectedDecoderAnchorState_le
                                hNS ht₀ hE hTail)
                              q y).component j))))
                    (spatial3.d i
                      (spatial3.d k
                        (spatial3.d l
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
                              q)))))
          q

/-- Strong selected third-jet `L²` differentiation implies the selected
relative order-three scalar energy derivative. -/
theorem h3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius_of_physicalL2StrongDerivative
    (hStrong :
      H3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius) :
    H3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

  let selected :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hNeighborhood :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 q := by
    exact
      IsOpen.mem_nhds
        isOpen_Ioo
        (by simpa only [R] using hq)

  have hEach :
      ∀ j i k l : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun r : ℝ =>
            spatialSquareEnergy
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (fun y : Point3 =>
                      (selected r y).component j)))))
          (spatialEnergyPairing
            (spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (fun y : Point3 =>
                    (selected q y).component j))))
            (spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (fun y : Point3 =>
                    temporal.d
                      (fun r : ℝ =>
                        (selected r y).component j)
                      q)))))
          q := by

    intro j i k l

    rcases
      hStrong E u T t₀ hNS ht₀ hE hTail
        q hq j i k l
    with
      ⟨D, hD, hDae⟩

    let X : H3ScalarL2 :=
      h3PreterminalSelectedThirdJetScalarL2At
        hNS ht₀ hE hTail q j i k l

    have hXae :
        (((X : H3ScalarL2) : Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (fun y : Point3 =>
                (selected q y).component j)))) := by
      dsimp only [X]
      simpa only [selected] using
        h3PreterminalSelectedThirdJetScalarL2At_ae
          hNS ht₀ hE hTail hq j i k l

    have hDaeSelected :
        (((D : H3ScalarL2) : Point3 → ℝ)
          =ᵐ[(volume : Measure Point3)]
        spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    (selected r y).component j)
                  q)))) := by
      simpa only [selected] using hDae

    have hCoefficient :
        2 * inner ℝ X D
          =
        spatialEnergyPairing
          (spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (fun y : Point3 =>
                  (selected q y).component j))))
          (spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (fun y : Point3 =>
                  temporal.d
                    (fun r : ℝ =>
                      (selected r y).component j)
                    q)))) := by
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
            ‖h3PreterminalSelectedThirdJetScalarL2At
                hNS ht₀ hE hTail r j i k l‖ ^ 2)
          (2 * inner ℝ X D)
          q := by
      have h := hD.norm_sq
      dsimp only [X] at h ⊢
      exact h

    have hNormCoefficient :=
      hNorm.congr_deriv hCoefficient

    have hEnergyEq :
        (fun r : ℝ =>
          ‖h3PreterminalSelectedThirdJetScalarL2At
              hNS ht₀ hE hTail r j i k l‖ ^ 2)
          =ᶠ[𝓝 q]
        (fun r : ℝ =>
          spatialSquareEnergy
            (spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (fun y : Point3 =>
                    (selected r y).component j))))) := by
      filter_upwards [hNeighborhood] with r hr
      simpa only [selected, R] using
        norm_sq_h3PreterminalSelectedThirdJetScalarL2At_eq_spatialSquareEnergy
          hNS ht₀ hE hTail
          (by simpa only [R] using hr)
          j i k l

    exact
      hNormCoefficient.congr_of_eventuallyEq
        hEnergyEq.symm

  have hL :
      ∀ j i k : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun r : ℝ =>
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (fun y : Point3 =>
                        (selected r y).component j)))))
          (∑ l : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (fun y : Point3 =>
                      (selected q y).component j))))
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (fun y : Point3 =>
                      temporal.d
                        (fun r : ℝ =>
                          (selected r y).component j)
                        q)))))
          q := by
    intro j i k
    apply HasDerivAt.fun_sum
    intro l hl
    exact hEach j i k l

  have hK :
      ∀ j i : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun r : ℝ =>
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (fun y : Point3 =>
                          (selected r y).component j)))))
          (∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (fun y : Point3 =>
                        (selected q y).component j))))
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (fun y : Point3 =>
                        temporal.d
                          (fun r : ℝ =>
                            (selected r y).component j)
                          q)))))
          q := by
    intro j i
    apply HasDerivAt.fun_sum
    intro k hk
    exact hL j i k

  have hI :
      ∀ j : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun r : ℝ =>
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  spatialSquareEnergy
                    (spatial3.d i
                      (spatial3.d k
                        (spatial3.d l
                          (fun y : Point3 =>
                            (selected r y).component j)))))
          (∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (fun y : Point3 =>
                          (selected q y).component j))))
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (fun y : Point3 =>
                          temporal.d
                            (fun r : ℝ =>
                              (selected r y).component j)
                            q)))))
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
                ∑ l : PrimeTensor.Axis Depth.three,
                  spatialSquareEnergy
                    (spatial3.d i
                      (spatial3.d k
                        (spatial3.d l
                          (fun y : Point3 =>
                            (selected r y).component j)))))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (fun y : Point3 =>
                          (selected q y).component j))))
                  (spatial3.d i
                    (spatial3.d k
                      (spatial3.d l
                        (fun y : Point3 =>
                          temporal.d
                            (fun r : ℝ =>
                              (selected r y).component j)
                            q)))))
        q := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact hI j

  simpa only [selected] using hSum

end

end Euclidean
end Bridge
end PrimeTensor
