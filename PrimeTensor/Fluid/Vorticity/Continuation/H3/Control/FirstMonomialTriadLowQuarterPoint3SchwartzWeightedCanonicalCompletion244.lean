import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedReferenceIndependence244

/-!
# Canonical signed first-monomial completion on weighted spectral H³

The Schwartz H³ difference-energy completion produces a real signed 243-slot
transport scalar for a *family*. The prior cross-energy theorem proves that
two families with exact second/third derivative matching and spectral limits
at the same weighted H³ state have the same scalar. However the original
existence result had forgotten these exact-matching witnesses.

We first use the strengthened (but conservative) existence theorem exported
from the matched energy-Cauchy module. This is not a new approximation
hypothesis: the matching equations were already proved as hMatch2/hMatch3 in
that theorem's body. They are now retained in the returned structure.

Classical choice of one such witness gives a total real-valued functional on
the existing weighted spectral H³ velocity state. The main theorem proves
that its value agrees with the signed completed observable of *every* other
matched Schwartz witness with the same spectral limit. The choice is
therefore mathematically harmless on this exact matching class.

This is a canonical H³ signed Schwartz completion, not an identification
with a general physical Navier--Stokes transport integral. Solenoidality and
physical trilinear identification remain independent proof obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeWeightedCanonicalCompletion244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A concrete weighted-spectral approximation with one genuine real Schwartz
H³-Cauchy family and exact L² identities for every one of its 27 second and
81 third ordered derivatives. The spectral limit is the indexed parameter. -/
structure WeightedH3MatchedSchwartzCompletion244
    (U : H3SpectralVelocityState) where
  spectral : ℕ → H3SpectralVelocityState
  family : SchwartzH3CauchyFamily244
  spectral_tendsto : Tendsto spectral atTop (𝓝 U)
  second_exact : ∀ n j a b,
    (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} (family.approximants n j))).toLp
        2 (volume : Measure V3) =
      matchedSpectralSecondFourierJets244 (spectral n) (j, (a, b))
  third_exact : ∀ n j a b c,
    (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} (family.approximants n j)))).toLp
          2 (volume : Measure V3) =
      matchedSpectralThirdFourierJets244 (spectral n) (j, (a, (b, c)))

/-- The class of matched H³ Schwartz completions is nonempty for *every*
weighted spectral velocity state. The energy-Cauchy condition and exact jet
identifications are obtained simultaneously from the SAME approximants. -/
theorem exists_weightedH3MatchedSchwartzCompletion244
    (U : H3SpectralVelocityState) :
    Nonempty (WeightedH3MatchedSchwartzCompletion244 U) := by
  obtain ⟨V, Ψ, hWeighted, hEnergy, hSecond, hThird⟩ :=
    exists_h3SmoothCompactWeighted_SchwartzH3EnergyCauchy_matched244 U
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  let F : SchwartzH3CauchyFamily244 :=
    ⟨f, hEnergy⟩
  refine ⟨{
    spectral := V
    family := F
    spectral_tendsto := hWeighted
    second_exact := ?_
    third_exact := ?_
  }⟩
  · intro n j a b
    change (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} (f n j))).toLp
        2 (volume : Measure V3) =
      h3ToFourierRealL2
        (h3SpectralVelocitySecondPhysicalJetFamily244 (V n)
          (h3ClassicalizationFinOfAxis j) a b)
    exact hSecond n j a b
  · intro n j a b c
    change (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} (f n j)))).toLp
          2 (volume : Measure V3) =
      h3ToFourierRealL2
        (h3SpectralVelocityThirdPhysicalJetFamily244 (V n)
          (h3ClassicalizationFinOfAxis j) a b c)
    exact hThird n j a b c

/-- Two separate matched Schwartz realizations of one weighted H³ velocity
have the same completed signed first-monomial scalar, regardless of their
spectral approximation choices or indexwise representatives. -/
theorem weightedH3MatchedSchwartzCompletion_completed_eq244
    (U : H3SpectralVelocityState)
    (F G : WeightedH3MatchedSchwartzCompletion244 U) :
    completedSchwartzH3FirstMonomial244 F.family =
      completedSchwartzH3FirstMonomial244 G.family :=
  completedSchwartzH3FirstMonomial_eq_of_sameWeightedLimit244
    U F.family G.family F.spectral G.spectral
    F.spectral_tendsto G.spectral_tendsto
    F.second_exact G.second_exact F.third_exact G.third_exact

/-- Choose one concrete matched real Schwartz H³ completion. Because the
previous theorem proves reference independence, this choice will NOT enter
the numerical value of the canonical signed transport scalar. -/
noncomputable def weightedH3CanonicalSchwartzWitness244
    (U : H3SpectralVelocityState) :
    WeightedH3MatchedSchwartzCompletion244 U :=
  Classical.choice (exists_weightedH3MatchedSchwartzCompletion244 U)

/-- A total, choice-independent signed first-monomial completion functional
on the repository's native weighted spectral H³ velocity Hilbert state. -/
noncomputable def weightedH3CanonicalSignedFirstMonomial244
    (U : H3SpectralVelocityState) : ℝ :=
  completedSchwartzH3FirstMonomial244
    (weightedH3CanonicalSchwartzWitness244 U).family

/-- Every derivative-matched real Schwartz H³ approximation of the same
weighted spectral target converges to the one canonical signed value. -/
theorem weightedH3CanonicalSignedFirstMonomial_eq_of_matched244
    (U : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U) :
    weightedH3CanonicalSignedFirstMonomial244 U =
      completedSchwartzH3FirstMonomial244 F.family := by
  exact weightedH3MatchedSchwartzCompletion_completed_eq244 U
    (weightedH3CanonicalSchwartzWitness244 U) F

/-- The signed physical Schwartz 243-slot monomial of any matched family
converges to the canonical weighted H³ scalar, not merely an unspecified
real limit. -/
theorem weightedH3CanonicalSignedFirstMonomial_tendsto244
    (U : H3SpectralVelocityState)
    (F : WeightedH3MatchedSchwartzCompletion244 U) :
    Tendsto
      (fun n => lowNormalRealSchwartzPoint3Monomial
        (F.family.approximants n))
      atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 U)) := by
  rw [weightedH3CanonicalSignedFirstMonomial_eq_of_matched244 U F]
  exact completedSchwartzH3FirstMonomial_tendsto244 F.family

/-- Two independent derivative-matched approximation choices yield the
identical real functional value at their common weighted spectral state. -/
theorem weightedH3CanonicalSignedFirstMonomial_unique244
    (U : H3SpectralVelocityState)
    (F G : WeightedH3MatchedSchwartzCompletion244 U) :
    completedSchwartzH3FirstMonomial244 F.family =
      weightedH3CanonicalSignedFirstMonomial244 U ∧
    completedSchwartzH3FirstMonomial244 G.family =
      weightedH3CanonicalSignedFirstMonomial244 U := by
  constructor
  · exact (weightedH3CanonicalSignedFirstMonomial_eq_of_matched244 U F).symm
  · exact (weightedH3CanonicalSignedFirstMonomial_eq_of_matched244 U G).symm

end
end PrimeTensor.FirstMonomialTriad
