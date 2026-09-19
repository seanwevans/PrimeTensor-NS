import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathReducedAnalysis
import PrimeTensor.Fluid.Vorticity.Logarithmic.Gronwall
import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate.Landau.Canonical
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.TailClosure

/-!
# H³-path BKM continuation from the analytic tail alone

`H3PathReducedAnalysis` left two fields in the path-specific canonical-analysis
frontier:

* local `C¹` regularity of the canonical H³ energy;
* `H3EnergyEstimateAnalyticOnTail`.

The local-`C¹` field is stronger than the scalar Osgood argument actually
uses.  The proof of logarithmic Grönwall only needs

* continuity of the energy on each compact tail interval;
* a derivative identity at each strict interior time.

For `LoggedPreterminalH3PathAdmissible`, compact-tail continuity is already
available from `energy_continuousAt`.  The analytic tail supplies
`H3OrderEnergyDerivativeIdentities`, hence the required `HasDerivAt`.

This file therefore removes local `C¹` from the BKM frontier entirely.

The remaining named analytic obligation is exactly

    H3EnergyEstimateAnalyticOnTail

on every high-order energy-class tail of an H³-path-admissible solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathAnalyticOnly
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The reduced remaining frontier -/

/--
The only remaining canonical H³ analysis required by the H³-path BKM route.

H³ integrability and scalar-energy continuity belong to the path class itself.
Split regularity remains inside `H3EnergyEstimateAnalyticOnTail` for now and
will be reduced separately.
-/
def H3PathEnergyClassProducesAnalyticTail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          H3EnergyEstimateAnalyticOnTail
            u a T

/--
The previously isolated reduced canonical-analysis interface implies the new
analytic-only interface by projection.
-/
theorem h3PathEnergyClassProducesAnalyticTail_of_reducedAnalysis
    (hAnalysis :
      H3PathEnergyClassProducesCanonicalAnalysis) :
    H3PathEnergyClassProducesAnalyticTail := by
  intro u T hH3 a hClass
  exact
    (hAnalysis u T hH3 a hClass).2

/-! ## Tail restriction -/

/-! ## Canonical profile from the H³ path -/

/--
The canonical finite-sum H³ energy is an `H3EnergyProfileFrom` on every strict
positive path tail.  No local-C¹ hypothesis is involved.
-/
theorem h3EnergyProfileFrom_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T) :
    H3EnergyProfileFrom
      u a T
      (velocityH3EnergyAt u) := by

  intro t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_of_lt_of_le ha.1 ht.1,
        ht.2
      ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  exact
    ⟨
      one_le_velocityH3EnergyAt u t,
      velocityH3BoundAt_canonical
        u t hInt
    ⟩

/-! ## Kinetic monotonicity without local C¹ -/

/--
The order-zero physical velocity energy has nonpositive derivative at each
strict tail time using only path H³-integrability and the analytic energy tail.
-/
theorem deriv_velocityH3Energy0At_nonpos_of_h3Path_analytic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAnalytic : H3EnergyEstimateAnalyticOnTail u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3Energy0At u) t ≤ 0 := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hH3At :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  rcases hAnalytic with
    ⟨p, hPDE, hTail⟩

  rcases hTail t ht with
    ⟨
      hDerivative,
      hRegular,
      hPairing,
      hPressureIBP,
      hDiffusionIBP
    ⟩

  let h : ℝ → ℝ :=
    fun s =>
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        * velocityH3EnergyAt u s

  have hGradient :
      VelocityGradientEnvelope u h t := by

    intro i j x

    have hBound :=
      norm_loggedVelocityComponent_spatial_d_le_h3Energy
        hClass ht hH3At i j x

    change
      abs
        (spatial3.d
          i
          (loggedVelocityComponent u t j)
          x)
        ≤
      h t

    dsimp only [h]

    simpa only [Real.norm_eq_abs] using hBound

  have hTransportIBP :
      H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient

  have hFlux :
      H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts
      hTransportIBP

  have hTransportZero :
      velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass
      hClass ht hFlux

  have hDiv :
      H3DifferentiatedIncompressibilityAt u t :=
    preterminalH3EnergyClass_produces_differentiatedIncompressibility
      hClass ht

  have hPressureZero :
      velocityH3PressureDerivative0At u p t = 0 :=
    velocityH3PressureDerivative0At_eq_zero
      hPressureIBP hDiv

  have hDiffusion :
      velocityH3DiffusionDerivative0At u t ≤ 0 :=
    velocityH3DiffusionDerivative0At_nonpos
      hDiffusionIBP

  have hFormalPDE :
      velocityH3FormalDerivative0At u t
        =
      velocityH3PDEDerivative0At u p t :=
    velocityH3FormalDerivative0At_eq_pde
      hPDE htAbs

  have hSplit :
      velocityH3PDEDerivative0At u p t
        =
      velocityH3DiffusionDerivative0At u t
        -
      velocityH3TransportDerivative0At u t
        -
      velocityH3PressureDerivative0At u p t :=
    velocityH3PDEDerivative0At_eq_split
      hPairing

  calc
    deriv (velocityH3Energy0At u) t
        =
      velocityH3FormalDerivative0At u t :=
      hDerivative.1.deriv

    _ =
      velocityH3PDEDerivative0At u p t :=
      hFormalPDE

    _ =
      velocityH3DiffusionDerivative0At u t
        -
      velocityH3TransportDerivative0At u t
        -
      velocityH3PressureDerivative0At u p t :=
      hSplit

    _ =
      velocityH3DiffusionDerivative0At u t := by
      rw [hTransportZero, hPressureZero]
      ring

    _ ≤ 0 :=
      hDiffusion

/--
The zeroth-order physical energy is antitone on the strict analytic H³-path
tail.  Only pointwise differentiability is needed by the mean-value theorem.
-/
theorem antitoneOn_velocityH3Energy0At_of_h3Path_analytic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAnalytic : H3EnergyEstimateAnalyticOnTail u a T) :
    AntitoneOn
      (velocityH3Energy0At u)
      (Set.Ioo a T) := by

  have hDifferentiable :
      DifferentiableOn ℝ
        (velocityH3Energy0At u)
        (Set.Ioo a T) := by

    intro t ht

    rcases hAnalytic with
      ⟨p, hPDE, hTail⟩

    exact
      ((hTail t ht).1.1).differentiableAt.differentiableWithinAt

  refine
    antitoneOn_of_deriv_nonpos
      (convex_Ioo a T)
      hDifferentiable.continuousOn
      (hDifferentiable.mono interior_subset)
      ?_

  intro t htInterior

  exact
    deriv_velocityH3Energy0At_nonpos_of_h3Path_analytic
      hH3
      hClass
      hAnalytic
      (interior_subset htInterior)

/--
After midpoint restart, the kinetic energy is controlled by its midpoint value
without any local-C¹ energy hypothesis.
-/
theorem bkmKineticEnergyControlledFromAnchor_midpoint_of_h3Path_analytic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAnalytic : H3EnergyEstimateAnalyticOnTail u a T) :
    BKMKineticEnergyControlledFromAnchor
      u
      (h3BKMKineticTailMidpoint a T)
      T := by

  have hAnti :=
    antitoneOn_velocityH3Energy0At_of_h3Path_analytic
      hH3 hClass hAnalytic

  have hMid :
      h3BKMKineticTailMidpoint a T
        ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo
      hClass.terminal_start.2

  intro t ht

  have htOld :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hMid.1 ht.1,
      ht.2
    ⟩

  exact
    hAnti
      hMid
      htOld
      (le_of_lt ht.1)

/-! ## Landau transport closure from path integrability + analytic tail -/

/--
The concrete Landau transport commutator estimate needs no scalar local-C¹
regularity.  Path H³-integrability replaces the first field of the old
canonical-data package; the analytic tail supplies the PDE pairing.
-/
theorem h3TransportControlledOnTail_of_h3Path_analytic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAnalytic : H3EnergyEstimateAnalyticOnTail u a T)
    (hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VelocityGradientEnvelope u h t) :
    H3TransportControlledOnTail
      u a T h 4422 := by

  have hSobolev6 :
      WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv
      wholeSpaceC1FDerivL2ToL6_cutoff

  have hSobolev :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      hSobolev6

  rcases hAnalytic with
    ⟨pEnergy, hPDEEnergy, hAnalyticTail⟩

  intro t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hH3At :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  have hGradientAt :
      VelocityGradientEnvelope u h t :=
    hGradient t ht

  have hIBP0 :
      H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradientAt

  have hIBP1 :
      H3FirstDerivativeTransportIntegrationByPartsAt u t :=
    h3FirstDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradientAt

  have hIBP2 :
      H3SecondDerivativeTransportIntegrationByPartsAt u t :=
    h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradientAt

  have hFlux0 :
      H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts
      hIBP0

  have hFlux1 :
      H3FirstDerivativeTransportFluxVanishesAt u t :=
    h3FirstDerivativeTransportFluxVanishesAt_of_integrationByParts
      hIBP1

  have hPurePairing1 :
      H3OrderOnePureTransportPairingIntegrableAt u t :=
    h3OrderOnePureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP1

  have hFlux2 :
      H3SecondDerivativeTransportFluxVanishesAt u t :=
    h3SecondDerivativeTransportFluxVanishesAt_of_integrationByParts
      hIBP2

  have hPurePairing2 :
      H3OrderTwoPureTransportPairingIntegrableAt u t :=
    h3OrderTwoPureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP2

  have hAnalyticCore3 :
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt
        u h t := by
    simpa [
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt
    ] using
      hGradientAt

  have hAnalytic3 :
      H3OrderThreeInterpolationLandauAnalyticDataAt
        u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev
      wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass
      ht
      hH3At
      hAnalyticCore3

  have hPairing1 :
      H3OrderOneTransportPairingIntegrableAt u t :=
    h3OrderOneTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hH3At
      hGradientAt
      hPurePairing1

  have hPairing2 :
      H3OrderTwoTransportPairingIntegrableAt u t :=
    h3OrderTwoTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hH3At
      hGradientAt
      hPurePairing2

  have hRegular3 :
      H3OrderThreeTransportRegularityAt u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass ht

  have hGradientPairing3 :
      H3OrderThreeGradientPairingIntegrableAt u t :=
    h3OrderThreeGradientPairingIntegrableAt_of_energyClass
      hClass
      ht
      hH3At
      hGradientAt

  have hMonomialPairing3 :
      H3OrderThreeInterpolationMonomialPairingIntegrableAt u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic3

  have hInterpolationPairing3 :
      H3OrderThreeInterpolationPairingIntegrableAt u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing3

  have hPDEPairing :
      H3PDEPairingIntegrableAt u pEnergy t :=
    (hAnalyticTail t ht).2.2.1

  have hFlux3 :
      H3ThirdDerivativeTransportFluxVanishesAt u t :=
    h3ThirdDerivativeTransportFluxVanishesAt_of_pde
      hClass
      ht
      hH3At
      hPDEPairing
      hGradientPairing3
      hInterpolationPairing3

  have hPairing3 :
      H3OrderThreeTransportPairingIntegrableAt u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pde
      hClass
      ht
      hPDEPairing
      hGradientPairing3
      hInterpolationPairing3

  have hTransport :
      H3TransportCommutatorBoundAt
        u h 4422 t :=
    h3TransportCommutatorBoundAt_of_landauAnalyticData
      hClass
      ht
      hFlux0
      hFlux1
      hPairing1
      hFlux2
      hPairing2
      hRegular3
      hFlux3
      hPairing3
      hGradientPairing3
      hH3At
      hAnalytic3

  exact
    ⟨
      hGradientAt,
      hTransport
    ⟩

/-! ## Scalar Osgood with continuity + pointwise derivative -/

/--
Scalar logarithmic Grönwall with the minimal regularity actually used by the
interval-integral proof.

`hContinuous` replaces local `C¹`: continuity is needed on the closed interval,
while `hDerivative` supplies the interior derivative formula explicitly.
-/
theorem logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
    {a T : ℝ}
    {g E : ℝ → ℝ}
    {C : ℝ}
    (haT : a < T)
    (hg :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo a T))
    (hC : 0 ≤ C)
    (hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          1 ≤ E t)
    (hContinuous :
      ∀ b : ℝ,
        b ∈ Set.Ico a T →
          ContinuousOn E (Set.Icc a b))
    (hDerivative :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          HasDerivAt E (deriv E s) s)
    (hGrowth :
      BKMLogGrowthInequalityFrom
        a T g E C) :
    ∃ M : ℝ,
      0 ≤ M
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ico a T →
          E t ≤ M := by

  let k : ℝ → ℝ :=
    fun s =>
      C * (1 + |g s|)

  let W : ℝ → ℝ :=
    fun s =>
      Real.log
        (1 + Real.log (E s))

  have hgInterval :
      IntervalIntegrable
        g
        MeasureTheory.volume
        a T := by
    apply
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (le_of_lt haT)).2
    exact hg

  have hkInterval :
      IntervalIntegrable
        k
        MeasureTheory.volume
        a T := by

    have hOne :
        IntervalIntegrable
          (fun _ : ℝ => (1 : ℝ))
          MeasureTheory.volume
          a T :=
      intervalIntegrable_const

    have hAbs :
        IntervalIntegrable
          (fun s : ℝ => |g s|)
          MeasureTheory.volume
          a T :=
      hgInterval.abs

    have hSum :
        IntervalIntegrable
          (fun s : ℝ => 1 + |g s|)
          MeasureTheory.volume
          a T :=
      hOne.add hAbs

    simpa only [k] using
      hSum.const_mul C

  have hkNonnegative :
      0 ≤ᵐ[
        MeasureTheory.volume.restrict
          (Set.Ioc a T)
      ] k := by

    filter_upwards [] with s

    dsimp only [k]

    exact
      mul_nonneg
        hC
        (by positivity)

  let K : ℝ :=
    ∫ s : ℝ in a..T, k s

  let B : ℝ :=
    W a + K

  let M : ℝ :=
    Real.exp
      (Real.exp B - 1)

  refine
    ⟨
      M,
      le_of_lt (Real.exp_pos _),
      ?_
    ⟩

  intro t ht

  have hat :
      a ≤ t :=
    ht.1

  have htT :
      t ≤ T :=
    le_of_lt ht.2

  have hIccSubset :
      Set.uIcc a t
        ⊆
      Set.uIcc a T := by

    intro s hs

    rw [Set.uIcc_of_le hat] at hs
    rw [Set.uIcc_of_le (le_of_lt haT)]

    exact
      ⟨
        hs.1,
        hs.2.trans htT
      ⟩

  have hkIntervalAt :
      IntervalIntegrable
        k
        MeasureTheory.volume
        a t :=
    hkInterval.mono_set
      hIccSubset

  have hkIntegrableOnIcc :
      MeasureTheory.IntegrableOn
        k
        (Set.Icc a t)
        MeasureTheory.volume := by

    apply
      (intervalIntegrable_iff_integrableOn_Icc_of_le hat).1

    exact hkIntervalAt

  have hECont :
      ContinuousOn E (Set.Icc a t) :=
    hContinuous t ht

  have hEOneIcc :
      ∀ s : ℝ,
        s ∈ Set.Icc a t →
          1 ≤ E s := by

    intro s hs

    exact
      hEOne
        s
        ⟨
          hs.1,
          lt_of_le_of_lt hs.2 ht.2
        ⟩

  have hENeIcc :
      ∀ s : ℝ,
        s ∈ Set.Icc a t →
          E s ≠ 0 := by

    intro s hs

    exact
      ne_of_gt
        (lt_of_lt_of_le
          zero_lt_one
          (hEOneIcc s hs))

  have hLogECont :
      ContinuousOn
        (fun s : ℝ => Real.log (E s))
        (Set.Icc a t) :=
    hECont.log
      hENeIcc

  have hYCont :
      ContinuousOn
        (fun s : ℝ => 1 + Real.log (E s))
        (Set.Icc a t) :=
    continuousOn_const.add
      hLogECont

  have hYNeIcc :
      ∀ s : ℝ,
        s ∈ Set.Icc a t →
          1 + Real.log (E s) ≠ 0 := by

    intro s hs

    have hLogNonnegative :
        0 ≤ Real.log (E s) :=
      Real.log_nonneg
        (hEOneIcc s hs)

    linarith

  have hWCont :
      ContinuousOn W (Set.Icc a t) := by

    dsimp only [W]

    exact
      hYCont.log
        hYNeIcc

  let w' : ℝ → ℝ :=
    fun s =>
      (deriv E s / E s)
        /
      (1 + Real.log (E s))

  have hWDeriv :
      ∀ s : ℝ,
        s ∈ Set.Ioo a t →
          HasDerivWithinAt
            W
            (w' s)
            (Set.Ioi s)
            s := by

    intro s hs

    have hsTail :
        s ∈ Set.Ioo a T :=
      ⟨
        hs.1,
        lt_trans hs.2 ht.2
      ⟩

    have hEsOne :
        1 ≤ E s :=
      hEOne
        s
        ⟨
          le_of_lt hs.1,
          hsTail.2
        ⟩

    have hEsNe :
        E s ≠ 0 :=
      ne_of_gt
        (lt_of_lt_of_le zero_lt_one hEsOne)

    have hYsNe :
        1 + Real.log (E s) ≠ 0 := by
      have hLogNonnegative :
          0 ≤ Real.log (E s) :=
        Real.log_nonneg hEsOne
      linarith

    have hEHas :
        HasDerivAt E (deriv E s) s :=
      hDerivative s hsTail

    have hLogEHas :
        HasDerivAt
          (fun r : ℝ => Real.log (E r))
          (deriv E s / E s)
          s :=
      hEHas.log
        hEsNe

    have hYHas :
        HasDerivAt
          (fun r : ℝ => 1 + Real.log (E r))
          (deriv E s / E s)
          s :=
      hLogEHas.const_add 1

    have hWHas :
        HasDerivAt
          W
          ((deriv E s / E s)
            /
           (1 + Real.log (E s)))
          s := by

      dsimp only [W]

      exact
        hYHas.log
          hYsNe

    dsimp only [w']

    exact
      hWHas.hasDerivWithinAt

  have hwLe :
      ∀ s : ℝ,
        s ∈ Set.Ioo a t →
          w' s ≤ k s := by

    intro s hs

    have hsGrowth :
        s ∈ Set.Ioo a T :=
      ⟨
        hs.1,
        lt_trans hs.2 ht.2
      ⟩

    have hEsOne :
        1 ≤ E s :=
      hEOne
        s
        ⟨
          le_of_lt hs.1,
          hsGrowth.2
        ⟩

    have hEsPos :
        0 < E s :=
      lt_of_lt_of_le
        zero_lt_one
        hEsOne

    have hLogEsNonnegative :
        0 ≤ Real.log (E s) :=
      Real.log_nonneg
        hEsOne

    have hYsPos :
        0 < 1 + Real.log (E s) := by
      linarith

    have hDenPos :
        0 <
          E s
            *
          (1 + Real.log (E s)) :=
      mul_pos
        hEsPos
        hYsPos

    have hGrowthAt :=
      hGrowth s hsGrowth

    have hDiv :
        deriv E s
            /
          (E s * (1 + Real.log (E s)))
          ≤
        C * (1 + |g s|) := by

      apply
        (div_le_iff₀ hDenPos).2

      calc
        deriv E s
            ≤
          C
            * (1 + |g s|)
            * E s
            * (1 + Real.log (E s)) :=
          hGrowthAt

        _ =
          (C * (1 + |g s|))
            *
          (E s * (1 + Real.log (E s))) := by
            ring

    dsimp only [w', k]

    simpa only [div_div] using hDiv

  have hWSubIntegral :
      W t - W a
        ≤
      ∫ s : ℝ in a..t, k s := by

    apply
      intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
        hat
        hWCont
        hWDeriv
        hkIntegrableOnIcc
        hwLe

  have hIntegralMono :
      (∫ s : ℝ in a..t, k s)
        ≤
      ∫ s : ℝ in a..T, k s := by

    exact
      intervalIntegral.integral_mono_interval
        le_rfl
        hat
        htT
        hkNonnegative
        hkInterval

  have hWt :
      W t ≤ B := by

    dsimp only [B, K]

    linarith

  have hEtOne :
      1 ≤ E t :=
    hEOne t ht

  have hEtPos :
      0 < E t :=
    lt_of_lt_of_le
      zero_lt_one
      hEtOne

  have hYtPos :
      0 < 1 + Real.log (E t) := by

    have hLogEtNonnegative :
        0 ≤ Real.log (E t) :=
      Real.log_nonneg hEtOne

    linarith

  have hYtLe :
      1 + Real.log (E t)
        ≤
      Real.exp B := by

    have hExp :=
      Real.exp_le_exp.mpr hWt

    dsimp only [W] at hExp

    simpa only [
      Real.exp_log hYtPos
    ] using hExp

  have hLogEtLe :
      Real.log (E t)
        ≤
      Real.exp B - 1 := by
    linarith

  have hEtLe :
      E t
        ≤
      Real.exp (Real.exp B - 1) := by

    have hExp :=
      Real.exp_le_exp.mpr hLogEtLe

    simpa only [
      Real.exp_log hEtPos
    ] using hExp

  dsimp only [M]

  exact hEtLe

/-! ## BKM growth and continuation from the analytic tail alone -/

/--
The H³-path BKM estimate closes terminal-tail H³ control assuming only the
analytic energy tail on every high-order energy-class tail.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_analyticTail
    (hAnalyticClosure :
      H3PathEnergyClassProducesAnalyticTail) :
    H3PathVorticityL1LinfProducesH3Control := by

  intro u T hH3 hControl

  rcases hControl with
    ⟨g, hgIntegrable, hgEnvelope⟩

  obtain
    ⟨a, hClass⟩ :=
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3

  have ha :
      a ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hAnalytic :
      H3EnergyEstimateAnalyticOnTail u a T :=
    hAnalyticClosure
      u T hH3 a hClass

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hbOld :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        ha.2

  have hb :
      b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo_zero
        ha

  have hClassB :
      PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hbOld.1)
      hbOld.2

  have hAnalyticB :
      H3EnergyEstimateAnalyticOnTail u b T :=
    h3EnergyEstimateAnalyticOnTail_mono_start
      (le_of_lt hbOld.1)
      hAnalytic

  have hgTail :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VorticityEnvelope u g t := by

    intro t ht

    exact
      hgEnvelope
        t
        ⟨
          lt_trans hb.1 ht.1,
          ht.2
        ⟩

  have hProfile :
      H3EnergyProfileFrom
        u b T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3 hb

  have hKinetic :
      BKMKineticEnergyControlledFromAnchor
        u b T := by

    dsimp only [b]

    exact
      bkmKineticEnergyControlledFromAnchor_midpoint_of_h3Path_analytic
        hH3
        hClass
        hAnalytic

  have hActual :
      ActualVelocityGradientLogBoundFrom
        u b T g
        (velocityH3EnergyAt u)
        (h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt
            (velocityH3Energy0At u b))) :=
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_kineticEnergyControlledFromAnchor
      hH3.navier_stokes
      hb
      hgTail
      hProfile
      hKinetic

  let B : ℝ :=
    h3BKMCanonicalSelectedLogGradientConstant
      (Real.sqrt
        (velocityH3Energy0At u b))

  have hB :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3BKMCanonicalSelectedLogGradientConstant_nonneg
        (Real.sqrt_nonneg _)

  let h : ℝ → ℝ :=
    h3BKMLogarithmicGradientEnvelope
      g
      (velocityH3EnergyAt u)
      B

  have hGradient :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          VelocityGradientEnvelope u h t := by

    intro t ht

    dsimp only [h, B]

    exact
      velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
        hActual
        ht

  have hEndpointBound :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          1 + |h t|
            ≤
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t)) := by

    intro t ht

    have hEt :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    dsimp only [h]

    exact
      one_add_abs_h3BKMLogarithmicGradientEnvelope_le
        hB
        hEt

  have hTransport :
      H3TransportControlledOnTail
        u b T h 4422 :=
    h3TransportControlledOnTail_of_h3Path_analytic
      hH3
      hClassB
      hAnalyticB
      hGradient

  have hEnergyGrowth :
      H3GradientGrowthInequalityFrom
        b T h
        (velocityH3EnergyAt u)
        4422 :=
    h3GradientGrowthInequalityFrom_canonical
      hClassB
      hAnalyticB
      hTransport

  let C : ℝ :=
    4422 * (B + 1)

  have hC :
      0 ≤ C := by
    dsimp only [C]
    exact
      mul_nonneg
        (by norm_num)
        (by linarith)

  have hGrowth :
      BKMLogGrowthInequalityFrom
        b T g
        (velocityH3EnergyAt u)
        C := by

    intro t ht

    have hEtOne :
        1 ≤ velocityH3EnergyAt u t :=
      (hProfile
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    have hEtNonneg :
        0 ≤ velocityH3EnergyAt u t :=
      le_trans
        (by norm_num)
        hEtOne

    have hEndpointAt :
        1 + |h t|
          ≤
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)) :=
      hEndpointBound t ht

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
        hEnergyGrowth t ht

      _ ≤
        4422
          *
        ((B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t)))
          * velocityH3EnergyAt u t := by

        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              hEndpointAt
              (by norm_num))
            hEtNonneg

      _ =
        C
          * (1 + |g t|)
          * velocityH3EnergyAt u t
          * (1 + Real.log (velocityH3EnergyAt u t)) := by

        dsimp only [C]
        ring

  have hgTailIntegrable :
      MeasureTheory.IntegrableOn
        g
        (Set.Ioo b T) := by

    apply
      hgIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hb.1 ht.1,
        ht.2
      ⟩

  have hEOne :
      ∀ t : ℝ,
        t ∈ Set.Ico b T →
          1 ≤ velocityH3EnergyAt u t := by

    intro t ht

    exact
      (hProfile t ht).1

  have hContinuous :
      ∀ q : ℝ,
        q ∈ Set.Ico b T →
          ContinuousOn
            (velocityH3EnergyAt u)
            (Set.Icc b q) :=
    hH3.canonicalH3EnergyContinuousOnTail
      hb

  have hDerivative :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          HasDerivAt
            (velocityH3EnergyAt u)
            (deriv (velocityH3EnergyAt u) s)
            s := by

    rcases hAnalyticB with
      ⟨p, hPDE, hAnalyticTail⟩

    intro s hs

    have hIds :
        H3OrderEnergyDerivativeIdentities u s :=
      (hAnalyticTail s hs).1

    have hDeriv :
        deriv (velocityH3EnergyAt u) s
          =
        velocityH3FormalDerivativeAt u s :=
      deriv_velocityH3EnergyAt
        hIds

    rw [hDeriv]

    exact
      hasDerivAt_velocityH3EnergyAt
        hIds

  obtain
    ⟨M, hM, hEM⟩ :=
    logarithmicGronwallClosesEnergy_of_continuous_of_hasDeriv
      hb.2
      hgTailIntegrable
      hC
      hEOne
      hContinuous
      hDerivative
      hGrowth

  refine
    ⟨
      b,
      M,
      hb,
      hM,
      ?_
    ⟩

  intro t ht

  exact
    velocityH3BoundAt_mono
      (hProfile t ht).2
      (hEM t ht)

/--
H³-path BKM continuation now depends only on the analytic H³ energy tail.

The scalar local-C¹ hypothesis has disappeared: path continuity and the
pointwise derivative identities already suffice for Osgood.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_analyticTail
    (hAnalyticClosure :
      H3PathEnergyClassProducesAnalyticTail) :
    H3PathVorticityL1LinfProducesExtension := by

  intro u T hH3 hControl

  have hTail :
      TerminalTailH3Control u T :=
    h3PathVorticityL1LinfProducesH3Control_of_analyticTail
      hAnalyticClosure
      u T
      hH3
      hControl

  exact
    h3PathH3ControlProducesExtension
      u T
      hH3
      hTail

end

end Euclidean
end Bridge
end PrimeTensor
