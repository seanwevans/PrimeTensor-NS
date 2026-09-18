import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.Automatic
import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure.Landau

/-!
# Downstream closure of the Landau top-flux tail datum

The H³ energy tree intentionally does not import the spectral
restart/classicalization machinery used by `TopFlux.VelocityEnvelope`.
Consequently the automatic top-flux theorem lives downstream in the
continuation tree.

This file closes the interface at that downstream seam.

Given

* an H³ energy-class tail;
* canonical H³ tail data;
* a velocity-gradient envelope on the strict tail;

the existing Landau interpolation machinery supplies the gradient and
interpolation pairing integrability, the canonical PDE package supplies the
PDE pairing integrability, and `TopFlux.Automatic` proves the top-order
whole-space transport-flux cancellation.

Thus the older `H3LandauTransportAnalyticOnTail` package can be reconstructed
from the gradient envelope alone.  Top-order boundary cancellation is no
longer an independent analytic input at the continuation layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable section

/--
Canonical H³ tail data plus a velocity-gradient envelope automatically
reconstruct the full older Landau tail package, including top-order
whole-space transport-flux cancellation.
-/
theorem h3LandauTransportAnalyticOnTail_of_gradientEnvelope
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hData :
        CanonicalH3EnergyDataOnTail
          u a T
    )
    (
      hGradient :
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            VelocityGradientEnvelope
              u h t
    ) :
    H3LandauTransportAnalyticOnTail
      u a T h := by

  have hSobolev6 :
      WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv
      wholeSpaceC1FDerivL2ToL6_cutoff

  have hSobolev :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      hSobolev6

  intro t ht

  have hGradientAt :
      VelocityGradientEnvelope
        u h t :=
    hGradient t ht

  have htIco :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  have hH3 :
      VelocityH3IntegrableAt
        u t :=
    hData.1 t htIco

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
      hH3
      hAnalyticCore3

  have hGradientPairing3 :
      H3OrderThreeGradientPairingIntegrableAt
        u t :=
    h3OrderThreeGradientPairingIntegrableAt_of_energyClass
      hClass
      ht
      hH3
      hGradientAt

  have hMonomialPairing3 :
      H3OrderThreeInterpolationMonomialPairingIntegrableAt
        u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic3

  have hInterpolationPairing3 :
      H3OrderThreeInterpolationPairingIntegrableAt
        u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing3

  have hPDEInt :
      ∃ p :
          PrimeTensor.SpaceTimeScalarField
            ℝ ℝ ℝ Depth.three,
        H3PDEPairingIntegrableAt
          u p t := by
    rcases hData.2.2 with
      ⟨p, hNS, hAnalytic⟩

    exact
      ⟨
        p,
        (hAnalytic t ht).2.2.1
      ⟩

  rcases hPDEInt with
    ⟨pEnergy, hPDEPairing⟩

  have hFlux3 :
      H3ThirdDerivativeTransportFluxVanishesAt
        u t :=
    h3ThirdDerivativeTransportFluxVanishesAt_of_pde
      hClass
      ht
      hH3
      hPDEPairing
      hGradientPairing3
      hInterpolationPairing3

  exact
    ⟨
      hFlux3,
      hGradientAt
    ⟩

/--
At the continuation layer, the older Landau transport-analytic closure follows
from the already-named canonical-data and gradient-envelope closures.

This removes top-order transport-flux cancellation as an independent
energy-class frontier.
-/
theorem energyClassProducesLandauTransportAnalytic_of_gradientEnvelope
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hGradient :
        EnergyClassProducesGradientEnvelope
    ) :
    EnergyClassProducesLandauTransportAnalytic := by

  intro
    u a T
    hClass

  have hData :
      CanonicalH3EnergyDataOnTail
        u a T :=
    hCanonical
      u a T hClass

  rcases
      hGradient
        u a T hClass
    with
      ⟨h, hEnvelope⟩

  exact
    ⟨
      h,
      h3LandauTransportAnalyticOnTail_of_gradientEnvelope
        hClass
        hData
        hEnvelope
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
