import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedEnergyCauchy244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzH3CrossEnergyInvariant244

/-!
# Reference independence for weighted H³ matched real Schwartz transport completion

The preceding theorem constructs a real Schwartz E₂/E₃-energy-Cauchy approximation
for an arbitrary weighted spectral H³ velocity. The scalar signed 243-slot
transport completion must also be independent of its arbitrary compact-frequency
approximation choices.

A pair of Schwartz families is *matched* when all 27 and 81 literal derivative
L² classes are exactly the real physical spectral reconstructions of their
own weighted H³ state. If those weighted state sequences converge to the same
U, this file shows that the cross-family E₂ and E₃ difference energies both
converge to zero. The previously compiled H³ cross-energy invariance theorem
then identifies their completed signed transport scalars.

No assumption of div-free Schwartz approximants or identification with the
original physical Navier--Stokes transport is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev J2 := A3 × (A3 × A3)
private abbrev J3 := A3 × (A3 × (A3 × A3))

noncomputable local instance axisFintypeWeightedReferenceIndependence244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- All 27 second-order real Fourier L² states reconstructed from one
weighted H³ spectral velocity, with the component-axis permutation fixed. -/
noncomputable def matchedSpectralSecondFourierJets244
    (U : H3SpectralVelocityState) : J2 → H3FourierRealL2 :=
  fun p => h3ToFourierRealL2
    (h3SpectralVelocitySecondPhysicalJetFamily244 U
      (h3ClassicalizationFinOfAxis p.1) p.2.1 p.2.2)

/-- All 81 third-order real Fourier L² states, identically indexed. -/
noncomputable def matchedSpectralThirdFourierJets244
    (U : H3SpectralVelocityState) : J3 → H3FourierRealL2 :=
  fun p => h3ToFourierRealL2
    (h3SpectralVelocityThirdPhysicalJetFamily244 U
      (h3ClassicalizationFinOfAxis p.1) p.2.1 p.2.2.1 p.2.2.2)

/-- The complete quadratic matched Fourier-jet family is continuous in the
original weighted spectral H³ Hilbert topology. -/
theorem continuous_matchedSpectralSecondFourierJets244 :
    Continuous matchedSpectralSecondFourierJets244 := by
  unfold matchedSpectralSecondFourierJets244
  apply continuous_pi
  rintro ⟨j, a, b⟩
  have hCoordinate : Continuous
      (fun U : H3SpectralVelocityState =>
        h3SpectralVelocitySecondPhysicalJetFamily244 U
          (h3ClassicalizationFinOfAxis j) a b) :=
    (continuous_apply b).comp
      ((continuous_apply a).comp
        ((continuous_apply (h3ClassicalizationFinOfAxis j)).comp
          continuous_h3SpectralVelocitySecondPhysicalJetFamily244))
  exact continuous_h3ToFourierRealL2.comp hCoordinate

/-- The complete cubic matched Fourier-jet family is continuous in the
weighted H³ Hilbert topology. -/
theorem continuous_matchedSpectralThirdFourierJets244 :
    Continuous matchedSpectralThirdFourierJets244 := by
  unfold matchedSpectralThirdFourierJets244
  apply continuous_pi
  rintro ⟨j, a, b, c⟩
  have hCoordinate : Continuous
      (fun U : H3SpectralVelocityState =>
        h3SpectralVelocityThirdPhysicalJetFamily244 U
          (h3ClassicalizationFinOfAxis j) a b c) :=
    (continuous_apply c).comp
      ((continuous_apply b).comp
        ((continuous_apply a).comp
          ((continuous_apply (h3ClassicalizationFinOfAxis j)).comp
            continuous_h3SpectralVelocityThirdPhysicalJetFamily244)))
  exact continuous_h3ToFourierRealL2.comp hCoordinate

/-- A finite family of L² coordinates converging twice to one common limit
has a vanishing full sum of squared cross differences. All ordered
coordinates are counted, and no norm-equivalence coefficient is inserted. -/
theorem finite_pi_L2_crossSquare_tendsto_zero244
    {J : Type*} [Fintype J]
    (F G : ℕ → J → H3FourierRealL2)
    (L : J → H3FourierRealL2)
    (hF : Tendsto F atTop (𝓝 L))
    (hG : Tendsto G atTop (𝓝 L)) :
    Tendsto (fun n => ∑ p : J, ‖F n p - G n p‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  have hDiff :
      Tendsto (fun n => F n - G n) atTop
        (𝓝 (0 : J → H3FourierRealL2)) := by
    simpa only [sub_self] using hF.sub hG
  have hTerm (p : J) :
      Tendsto (fun n => ‖F n p - G n p‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    have hCoord : Tendsto (fun n => F n p - G n p)
        atTop (𝓝 (0 : H3FourierRealL2)) := by
      have h := (continuous_apply p).continuousAt.tendsto.comp hDiff
      simpa only [Function.comp_def, Pi.sub_apply, Pi.zero_apply] using h
    simpa using (hCoord.norm.pow 2)
  have hSum (s : Finset J) :
      Tendsto (fun n => ∑ p ∈ s, ‖F n p - G n p‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
        simpa only [Finset.sum_insert hp, zero_add] using (hTerm p).add ih
  exact hSum (Finset.univ : Finset J)

/-- Exact second-order energy identity for TWO distinct derivative-matched
Schwartz families, expressed using their own weighted spectral states. -/
theorem matchedSpectral_crossEnergy2_eq_squareSum244
    (F G : SchwartzH3CauchyFamily244)
    (V W : ℕ → H3SpectralVelocityState)
    (hF : ∀ n j a b,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (F.approximants n j))).toLp
          2 (volume : Measure V3) =
        matchedSpectralSecondFourierJets244 (V n) (j, (a, b)))
    (hG : ∀ n j a b,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (G.approximants n j))).toLp
          2 (volume : Measure V3) =
        matchedSpectralSecondFourierJets244 (W n) (j, (a, b)))
    (n : ℕ) :
    lowNormalRealSchwartzH3Energy2
      (schwartzVelocityDifference244 (F.approximants n) (G.approximants n)) =
      ∑ p : J2, ‖matchedSpectralSecondFourierJets244 (V n) p -
        matchedSpectralSecondFourierJets244 (W n) p‖ ^ 2 := by
  rw [h3RealSchwartz_differenceEnergy2_eq_Lp244]
  simp only [Fintype.sum_prod_type]
  simp_rw [hF, hG]

/-- Exact 81-slot third-order cross difference energy identity. -/
theorem matchedSpectral_crossEnergy3_eq_squareSum244
    (F G : SchwartzH3CauchyFamily244)
    (V W : ℕ → H3SpectralVelocityState)
    (hF : ∀ n j a b c,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (F.approximants n j)))).toLp
            2 (volume : Measure V3) =
        matchedSpectralThirdFourierJets244 (V n) (j, (a, (b, c))))
    (hG : ∀ n j a b c,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (G.approximants n j)))).toLp
            2 (volume : Measure V3) =
        matchedSpectralThirdFourierJets244 (W n) (j, (a, (b, c))))
    (n : ℕ) :
    lowNormalRealSchwartzH3Energy3
      (schwartzVelocityDifference244 (F.approximants n) (G.approximants n)) =
      ∑ p : J3, ‖matchedSpectralThirdFourierJets244 (V n) p -
        matchedSpectralThirdFourierJets244 (W n) p‖ ^ 2 := by
  rw [h3RealSchwartz_differenceEnergy3_eq_Lp244]
  simp only [Fintype.sum_prod_type]
  simp_rw [hF, hG]

/-- The two independent matched compact-frequency approximations to the
SAME weighted H³ state have vanishing genuine cross-family E₂ and E₃.
Unlike an ordinary individual Cauchy statement this compares TWO choices. -/
theorem matchedSpectral_crossEnergy_vanishes_of_sameLimit244
    (U : H3SpectralVelocityState)
    (F G : SchwartzH3CauchyFamily244)
    (V W : ℕ → H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U))
    (hW : Tendsto W atTop (𝓝 U))
    (hF2 : ∀ n j a b,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (F.approximants n j))).toLp
          2 (volume : Measure V3) =
        matchedSpectralSecondFourierJets244 (V n) (j, (a, b)))
    (hG2 : ∀ n j a b,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (G.approximants n j))).toLp
          2 (volume : Measure V3) =
        matchedSpectralSecondFourierJets244 (W n) (j, (a, b)))
    (hF3 : ∀ n j a b c,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (F.approximants n j)))).toLp
            2 (volume : Measure V3) =
        matchedSpectralThirdFourierJets244 (V n) (j, (a, (b, c))))
    (hG3 : ∀ n j a b c,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (G.approximants n j)))).toLp
            2 (volume : Measure V3) =
        matchedSpectralThirdFourierJets244 (W n) (j, (a, (b, c)))) :
    SchwartzH3FamiliesCrossEnergyVanishing244 F G := by
  have hSecondV : Tendsto
      (fun n => matchedSpectralSecondFourierJets244 (V n))
      atTop (𝓝 (matchedSpectralSecondFourierJets244 U)) :=
    continuous_matchedSpectralSecondFourierJets244.continuousAt.tendsto.comp hV
  have hSecondW : Tendsto
      (fun n => matchedSpectralSecondFourierJets244 (W n))
      atTop (𝓝 (matchedSpectralSecondFourierJets244 U)) :=
    continuous_matchedSpectralSecondFourierJets244.continuousAt.tendsto.comp hW
  have hThirdV : Tendsto
      (fun n => matchedSpectralThirdFourierJets244 (V n))
      atTop (𝓝 (matchedSpectralThirdFourierJets244 U)) :=
    continuous_matchedSpectralThirdFourierJets244.continuousAt.tendsto.comp hV
  have hThirdW : Tendsto
      (fun n => matchedSpectralThirdFourierJets244 (W n))
      atTop (𝓝 (matchedSpectralThirdFourierJets244 U)) :=
    continuous_matchedSpectralThirdFourierJets244.continuousAt.tendsto.comp hW
  have hE2 := finite_pi_L2_crossSquare_tendsto_zero244
    (fun n => matchedSpectralSecondFourierJets244 (V n))
    (fun n => matchedSpectralSecondFourierJets244 (W n))
    (matchedSpectralSecondFourierJets244 U) hSecondV hSecondW
  have hE3 := finite_pi_L2_crossSquare_tendsto_zero244
    (fun n => matchedSpectralThirdFourierJets244 (V n))
    (fun n => matchedSpectralThirdFourierJets244 (W n))
    (matchedSpectralThirdFourierJets244 U) hThirdV hThirdW
  constructor
  · have hId (n : ℕ) :=
      matchedSpectral_crossEnergy2_eq_squareSum244 F G V W hF2 hG2 n
    simpa only [hId] using hE2
  · have hId (n : ℕ) :=
      matchedSpectral_crossEnergy3_eq_squareSum244 F G V W hF3 hG3 n
    simpa only [hId] using hE3

/-- The completed signed 243-slot Schwartz observable does NOT depend on
which spectrally convergent, derivative-matched H³ Schwartz approximation
family was used. This is reference independence, not merely existence of
one completion. -/
theorem completedSchwartzH3FirstMonomial_eq_of_sameWeightedLimit244
    (U : H3SpectralVelocityState)
    (F G : SchwartzH3CauchyFamily244)
    (V W : ℕ → H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U))
    (hW : Tendsto W atTop (𝓝 U))
    (hF2 : ∀ n j a b,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (F.approximants n j))).toLp
          2 (volume : Measure V3) =
        matchedSpectralSecondFourierJets244 (V n) (j, (a, b)))
    (hG2 : ∀ n j a b,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (G.approximants n j))).toLp
          2 (volume : Measure V3) =
        matchedSpectralSecondFourierJets244 (W n) (j, (a, b)))
    (hF3 : ∀ n j a b c,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (F.approximants n j)))).toLp
            2 (volume : Measure V3) =
        matchedSpectralThirdFourierJets244 (V n) (j, (a, (b, c))))
    (hG3 : ∀ n j a b c,
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (G.approximants n j)))).toLp
            2 (volume : Measure V3) =
        matchedSpectralThirdFourierJets244 (W n) (j, (a, (b, c)))) :
    completedSchwartzH3FirstMonomial244 F =
      completedSchwartzH3FirstMonomial244 G :=
  completedSchwartzH3FirstMonomial_eq_of_crossEnergy244 F G
    (matchedSpectral_crossEnergy_vanishes_of_sameLimit244
      U F G V W hV hW hF2 hG2 hF3 hG3)

end
end PrimeTensor.FirstMonomialTriad
