import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalActualAntiHeatFourierCompensation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticLowBandSourceLipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedSpatialComponentSpikes
import Mathlib.Tactic

/-!
# Actual three-coordinate sharp Fourier kinetic compensation

The previous source theorem required an abstract low/high decomposition and
cross-orthogonality certificates. Here both are provided by the SAME genuine
sharp radial physical Fourier cutoff, first for scalar real L² and then for
three-component physical velocity and projected momentum source.

The accepted real Plancherel pairing and disjoint Fourier indicators prove
exact cross-orthogonality. The existing kinetic-only low-frequency projected
source estimate then yields a concrete source ceiling, while the monotone
order-zero physical kinetic energy bounds the lowpass velocity.

For any actual strict time t after kinetic anchor b, if the ACTUAL highpass
projected momentum source nearly agrees with positive scalar rate times the
ACTUAL highpass velocity, then

  (rate-eps)*||Uhi||² <= 3*sqrt(E0(b))*Ckin(rho,E0(b)).

The right side grows with cutoff radius. This is a real physical PDE
necessary constraint, NOT a radius-uniform estimate or H³ continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeSharpPhysicalKinetic244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSharpPhysicalKinetic244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Two different arbitrary complex Fourier L² states are exactly orthogonal
when the first is sharply low-passed and the second sharply high-passed. -/
theorem thirdFullKinetic_sharpFourierLowHigh_crossInner_zero244
    (ρ : ℝ) (F G : H3FourierComplexL2) :
    inner ℂ (h3CriticalFourierSharpLowCutoffCLM ρ F)
      (G - h3CriticalFourierSharpLowCutoffCLM ρ G) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hAE : ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      inner ℂ
        ((h3CriticalFourierSharpLowCutoffCLM ρ F : H3FourierComplexL2) ξ)
        ((G - h3CriticalFourierSharpLowCutoffCLM ρ G : H3FourierComplexL2) ξ)
        = (0 : ℂ) := by
    filter_upwards [
      h3Critical_fourierSharpLowCutoffApply_ae ρ F,
      h3Critical_fourierSharpHighpass_ae ρ G
    ] with ξ hLo hHi
    -- The CLM and its underlying sharp indicator have the same toFun,
    -- but `rw` does not unfold the CLM automatically. Expose that
    -- definitional equality before rewriting the a.e. representatives.
    change inner ℂ
      ((h3CriticalFourierSharpLowCutoffApply ρ F : H3FourierComplexL2) ξ)
      ((G - h3CriticalFourierSharpLowCutoffCLM ρ G : H3FourierComplexL2) ξ) = 0
    rw [hLo, hHi]
    by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
    · have hNot : ξ ∉ (h3TerminalRadialFrequencyBelow ρ)ᶜ := by
        simpa only [Set.mem_compl_iff, not_not] using hξ
      rw [Set.indicator_of_mem hξ, Set.indicator_of_notMem hNot]
      simp
    · have hIn : ξ ∈ (h3TerminalRadialFrequencyBelow ρ)ᶜ := hξ
      rw [Set.indicator_of_notMem hξ, Set.indicator_of_mem hIn]
      simp
  have hIntegral := integral_congr_ae hAE
  simpa only [integral_zero] using hIntegral

/-- The actual REAL physical Fourier projector inherits exact low/high
cross-orthogonality by the established real-part Plancherel identity. -/
theorem thirdFullPhysical_sharpScalarLowHigh_crossInner_zero244
    (ρ : ℝ) (f g : H3ScalarL2) :
    inner ℝ (h3CriticalPhysicalSharpLowCutoffApply ρ f)
      (g - h3CriticalPhysicalSharpLowCutoffApply ρ g) = 0 := by
  calc
    inner ℝ (h3CriticalPhysicalSharpLowCutoffApply ρ f)
        (g - h3CriticalPhysicalSharpLowCutoffApply ρ g) =
      (inner ℂ
        (h3ScalarFourierL2 (h3CriticalPhysicalSharpLowCutoffApply ρ f))
        (h3ScalarFourierL2 (g - h3CriticalPhysicalSharpLowCutoffApply ρ g))).re :=
      (re_inner_h3ScalarFourierL2_eq_inner _ _).symm
    _ = (inner ℂ
          (h3CriticalFourierSharpLowCutoffCLM ρ (h3ScalarFourierL2 f))
          (h3ScalarFourierL2 g -
            h3CriticalFourierSharpLowCutoffCLM ρ (h3ScalarFourierL2 g))).re := by
      rw [h3Critical_scalarFourier_physicalSharpLowCutoff_eq,
        h3ScalarFourierL2_sub,
        h3Critical_scalarFourier_physicalSharpLowCutoff_eq]
    _ = 0 := by
      rw [thirdFullKinetic_sharpFourierLowHigh_crossInner_zero244]
      simp

/-- The ACTUAL three-component physical sharp Fourier projector, assembled
coordinatewise rather than identified with an abstract Hilbert projection. -/
noncomputable def thirdFullPhysicalSharpLowCutoffHilbert244
    (ρ : ℝ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2 (fun j : Fin 3 =>
    h3CriticalPhysicalSharpLowCutoffApply ρ (V.ofLp j))

/-- The genuine componentwise real cutoff is orthogonal to the genuine
highpass of ANY second physical three-component L² state. -/
theorem thirdFullPhysical_sharpVectorLowHigh_crossInner_zero244
    (ρ : ℝ) (V W : H3PhysicalRealFinVectorL2Hilbert) :
    inner ℝ (thirdFullPhysicalSharpLowCutoffHilbert244 ρ V)
      (W - thirdFullPhysicalSharpLowCutoffHilbert244 ρ W) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j _
  change inner ℝ
      (h3CriticalPhysicalSharpLowCutoffApply ρ (V.ofLp j))
      (W.ofLp j - h3CriticalPhysicalSharpLowCutoffApply ρ (W.ofLp j)) = 0
  exact thirdFullPhysical_sharpScalarLowHigh_crossInner_zero244 ρ
    (V.ofLp j) (W.ofLp j)

/-- The reverse cross term vanishes, for the SAME actual sharp projector. -/
theorem thirdFullPhysical_sharpVectorHighLow_crossInner_zero244
    (ρ : ℝ) (V W : H3PhysicalRealFinVectorL2Hilbert) :
    inner ℝ (V - thirdFullPhysicalSharpLowCutoffHilbert244 ρ V)
      (thirdFullPhysicalSharpLowCutoffHilbert244 ρ W) = 0 := by
  rw [real_inner_comm]
  exact thirdFullPhysical_sharpVectorLowHigh_crossInner_zero244 ρ W V

/-- Native physical three-vector sharp Plancherel Pythagoras: no abstract
projection or assumption about its operator norm is required. -/
theorem thirdFullPhysical_sharpVectorLowHigh_normSquare244
    (ρ : ℝ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    ‖V‖ ^ 2 =
      ‖thirdFullPhysicalSharpLowCutoffHilbert244 ρ V‖ ^ 2 +
      ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 ρ V‖ ^ 2 := by
  let P : H3PhysicalRealFinVectorL2Hilbert :=
    thirdFullPhysicalSharpLowCutoffHilbert244 ρ V
  have hOrth : inner ℝ P (V - P) = 0 :=
    thirdFullPhysical_sharpVectorLowHigh_crossInner_zero244 ρ V V
  calc
    ‖V‖ ^ 2 = ‖P + (V - P)‖ ^ 2 := by
      congr 1
      abel
    _ = ‖P‖ ^ 2 + ‖V - P‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero P (V - P) hOrth)

/-- Consequently the actual physical sharp lowpass is an L² contraction. -/
theorem thirdFullPhysical_sharpVectorLowpass_norm_le244
    (ρ : ℝ) (V : H3PhysicalRealFinVectorL2Hilbert) :
    ‖thirdFullPhysicalSharpLowCutoffHilbert244 ρ V‖ ≤ ‖V‖ := by
  have hSq := thirdFullPhysical_sharpVectorLowHigh_normSquare244 ρ V
  have hLe : ‖thirdFullPhysicalSharpLowCutoffHilbert244 ρ V‖ ^ 2 ≤
      ‖V‖ ^ 2 := by
    nlinarith only [hSq,
      sq_nonneg (‖V - thirdFullPhysicalSharpLowCutoffHilbert244 ρ V‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hLe

/-- Genuine physical lowpass kinetic energy is controlled solely by the
kinetic energy at an earlier strict physical time. -/
theorem thirdFullPhysical_sharpActualVelocity_kineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    ‖thirdFullPhysicalSharpLowCutoffHilbert244 ρ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ≤
      Real.sqrt (velocityH3Energy0At u b) := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hbAbs.1 ht.1, ht.2⟩
  have hKin : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    (h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3)
      hbAbs htAbs ht.1.le
  have hNorm : ‖U‖ ^ 2 = velocityH3Energy0At u t :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t htAbs
  have hP : ‖thirdFullPhysicalSharpLowCutoffHilbert244 ρ U‖ ≤ ‖U‖ :=
    thirdFullPhysical_sharpVectorLowpass_norm_le244 ρ U
  have hE : 0 ≤ velocityH3Energy0At u b := velocityH3Energy0At_nonneg u b
  have hRoot := Real.sq_sqrt hE
  have hRootNonneg := Real.sqrt_nonneg (velocityH3Energy0At u b)
  change ‖thirdFullPhysicalSharpLowCutoffHilbert244 ρ U‖ ≤ _
  nlinarith only [hKin, hNorm, hP, hRoot, hRootNonneg,
    norm_nonneg U, norm_nonneg (thirdFullPhysicalSharpLowCutoffHilbert244 ρ U)]

/-- The actual PHYSICAL three-component lowpass momentum source has a
kinetic-only ceiling for every fixed radius: one accepted scalar ceiling
per coordinate, with no full-H³ norm on the right. -/
theorem thirdFullPhysical_sharpActualSource_kineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    ‖thirdFullPhysicalSharpLowCutoffHilbert244 ρ
        (h3PathActualProjectedMomentumSource244 hH3 t)‖ ≤
      3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        ρ (velocityH3Energy0At u b) := by
  apply h3Critical_fin3_hilbert_norm_le_three_mul_coordinate_ceiling
  · exact thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 _ _
  · intro j
    change ‖h3CriticalPhysicalSharpLowCutoffApply ρ
      ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp j)‖ ≤ _
    exact thirdFullPhysical_actualLowBandSource_kineticCeiling244
      hH3 hClass b hb ρ hρ t ht j

/-- No more assumed low/high decomposition or orthogonality: the accepted
actual kinetic pairing and the ACTUAL sharp physical projector force this
precise mass ceiling under a specified highpass anti-heat approximation. -/
theorem thirdFullPhysical_sharpActualHighMass_compensation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (rate eps : ℝ)
    (hErr :
      ‖(h3PathActualProjectedMomentumSource244 hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3PathActualProjectedMomentumSource244 hH3 t)) -
        rate • (h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ ≤
        eps * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖) :
    (rate - eps) *
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        thirdFullPhysicalSharpLowCutoffHilbert244 ρ
          (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2 ≤
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          ρ (velocityH3Energy0At u b)) := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let Ulo := thirdFullPhysicalSharpLowCutoffHilbert244 ρ U
  let Rlo := thirdFullPhysicalSharpLowCutoffHilbert244 ρ R
  have hU : U = Ulo + (U - Ulo) := by abel
  have hR : R = Rlo + (R - Rlo) := by abel
  have hCrossLo : inner ℝ Ulo (R - Rlo) = 0 :=
    thirdFullPhysical_sharpVectorLowHigh_crossInner_zero244 ρ U R
  have hCrossHi : inner ℝ (U - Ulo) Rlo = 0 :=
    thirdFullPhysical_sharpVectorHighLow_crossInner_zero244 ρ U R
  have hUlo : ‖Ulo‖ ≤ Real.sqrt (velocityH3Energy0At u b) :=
    thirdFullPhysical_sharpActualVelocity_kineticAnchor244
      hH3 hClass b hb ρ t ht
  have hRlo : ‖Rlo‖ ≤
      3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        ρ (velocityH3Energy0At u b) :=
    thirdFullPhysical_sharpActualSource_kineticAnchor244
      hH3 hClass b hb ρ hρ t ht
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1
      (lt_trans hb.1 ht.1), ht.2⟩
  exact thirdFullPhysical_kineticSplit_highMassGate244
    hH3 t htAbs Ulo (U - Ulo) Rlo (R - Rlo)
    hU hR hCrossLo hCrossHi rate eps
    (Real.sqrt (velocityH3Energy0At u b))
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      ρ (velocityH3Energy0At u b))
    (Real.sqrt_nonneg _) hUlo hRlo hErr

/-- Quantitative obstruction to near-saturation on a physical sharp
highpass: a carrier exceeding the explicit kinetic low-band budget must
have more than `eps` relative anti-heat mismatch. This remains a one-time
condition, NOT a terminal high-frequency uniformity theorem. -/
theorem thirdFullPhysical_sharpActualHighMass_forces_mismatch244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (rate eps : ℝ)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          ρ (velocityH3Energy0At u b)) <
      (rate - eps) *
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2) :
    eps * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
      thirdFullPhysicalSharpLowCutoffHilbert244 ρ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ <
      ‖(h3PathActualProjectedMomentumSource244 hH3 t -
        thirdFullPhysicalSharpLowCutoffHilbert244 ρ
          (h3PathActualProjectedMomentumSource244 hH3 t)) -
        rate • (h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ := by
  by_contra hNot
  have hErr :
      ‖(h3PathActualProjectedMomentumSource244 hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3PathActualProjectedMomentumSource244 hH3 t)) -
        rate • (h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t))‖ ≤
      eps * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          thirdFullPhysicalSharpLowCutoffHilbert244 ρ
            (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ :=
    le_of_not_gt hNot
  have hGate := thirdFullPhysical_sharpActualHighMass_compensation244
    hH3 hClass b hb ρ hρ t ht rate eps hErr
  exact (not_lt_of_ge hGate) hExcess

end
end PrimeTensor.FirstMonomialTriad
