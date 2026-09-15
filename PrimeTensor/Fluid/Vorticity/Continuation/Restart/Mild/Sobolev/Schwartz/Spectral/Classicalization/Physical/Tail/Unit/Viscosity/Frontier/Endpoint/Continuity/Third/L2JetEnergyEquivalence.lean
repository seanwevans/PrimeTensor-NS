import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.L2JetDirectContinuation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EndpointPressureFreeEnergy

/-!
# Full physical H³ L²-jet continuity and scalar energy continuity are equivalent

The direct-continuation reduction makes the complete physical 120-coordinate
H³ `L²` jet the only topology frontier.

The pressure-free weak theory plus the exact weighted spectral difference
identity show that this is not a stronger analytic requirement than scalar
H³-energy continuity:

* scalar energy continuity gives strong weighted H³ spectral continuity;
* every one of the 120 physical `L²` jet-coordinate differences is bounded by
  the weighted spectral difference of its velocity component;
* hence every physical jet coordinate is strongly continuous.

Combined with `EnergyFromL2Jet`, this proves the converse too.  Thus, under the
retained canonical H³ tail hypotheses,

    full physical H³ L²-jet continuity
      ↔
    scalar physical H³-energy continuity.

So the direct L²-jet route removes derivative bookkeeping from the continuation
stack, but it does not hide or evade the single remaining norm-continuity
obstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3L2JetEnergyEquivalence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Velocity-component index carried by one semantic H³ jet slot. -/
def h3JetVelocityComponent : H3JetIndex → Fin 3
  | Sum.inl j => j
  | Sum.inr (Sum.inl ji) => ji.1
  | Sum.inr (Sum.inr (Sum.inl jik)) => jik.1
  | Sum.inr (Sum.inr (Sum.inr jikl)) => jikl.1

/-- Zeroth-order Fourier-jet differences are bounded by the complete weighted
H³ spectral difference of the same velocity component. -/
theorem norm_h3PreterminalCanonicalFourierJetOnElapsed_slot0_sub_le_spectralCoordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (j : Fin 3)
    (q r : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q
        -
      h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) r‖
      ≤
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j
        -
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r j‖ := by
  have hEnergy :
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2
        =
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) r‖ ^ 2
        +
      (∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) r‖ ^ 2) := by
    exact
      norm_velocityH3SpectralScalarAt_sub_sq
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail r)
        j

  have h1 :
      0 ≤
      ∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ => sq_nonneg _)

  have h2 :
      0 ≤
      ∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ =>
        Finset.sum_nonneg
          (fun b _ => sq_nonneg _))

  have h3 :
      0 ≤
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ =>
        Finset.sum_nonneg
          (fun b _ =>
            Finset.sum_nonneg
              (fun c _ => sq_nonneg _)))

  have hSq :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
        ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2 := by
    calc
      _ ≤
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2) :=
        le_add_of_nonneg_right h1
      _ ≤
        (‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2))
          +
        (∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2) :=
        le_add_of_nonneg_right h2
      _ ≤
        (‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2))
          +
        (∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2)
          +
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2) :=
        le_add_of_nonneg_right h3
      _ =
        ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j
            -
          h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail r j‖ ^ 2 :=
        hEnergy.symm

  have hLeft :
      0 ≤
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) r‖ :=
    norm_nonneg _

  have hRight :
      0 ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ :=
    norm_nonneg _

  nlinarith

/-- First-order Fourier-jet differences are bounded by the same complete
weighted spectral difference. -/
theorem norm_h3PreterminalCanonicalFourierJetOnElapsed_slot1_sub_le_spectralCoordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (j i : Fin 3)
    (q r : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot1 j i) q
        -
      h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot1 j i) r‖
      ≤
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j
        -
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r j‖ := by
  have hEnergy :
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2
        =
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) r‖ ^ 2
        +
      (∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) r‖ ^ 2) := by
    exact
      norm_velocityH3SpectralScalarAt_sub_sq
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail r)
        j

  have hOne :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) r‖ ^ 2
        ≤
      ∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2 :=
    Finset.single_le_sum
      (fun a _ =>
        sq_nonneg
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖)
      (Finset.mem_univ i)

  have h0 :
      0 ≤
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2 :=
    sq_nonneg _

  have h2 :
      0 ≤
      ∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ =>
        Finset.sum_nonneg
          (fun b _ => sq_nonneg _))

  have h3 :
      0 ≤
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ =>
        Finset.sum_nonneg
          (fun b _ =>
            Finset.sum_nonneg
              (fun c _ => sq_nonneg _)))

  have hSq :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) r‖ ^ 2
        ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2 := by
    calc
      _ ≤
        ∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2 :=
        hOne
      _ ≤
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2) := by
        exact le_add_of_nonneg_left h0
      _ ≤
        (‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2))
          +
        (∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2) :=
        le_add_of_nonneg_right h2
      _ ≤
        (‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2))
          +
        (∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2)
          +
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2) :=
        le_add_of_nonneg_right h3
      _ =
        ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j
            -
          h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail r j‖ ^ 2 :=
        hEnergy.symm

  have hLeft :
      0 ≤
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot1 j i) r‖ :=
    norm_nonneg _

  have hRight :
      0 ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ :=
    norm_nonneg _

  nlinarith

/-- Second-order Fourier-jet differences are bounded by the same complete
weighted spectral difference. -/
theorem norm_h3PreterminalCanonicalFourierJetOnElapsed_slot2_sub_le_spectralCoordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (j i k : Fin 3)
    (q r : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot2 j i k) q
        -
      h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot2 j i k) r‖
      ≤
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j
        -
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r j‖ := by
  have hEnergy :
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2
        =
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) r‖ ^ 2
        +
      (∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j a) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j a b) r‖ ^ 2)
        +
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j a b c) r‖ ^ 2) := by
    exact
      norm_velocityH3SpectralScalarAt_sub_sq
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail r)
        j

  have hK :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) r‖ ^ 2
        ≤
      ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j i b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j i b) r‖ ^ 2 :=
    Finset.single_le_sum
      (fun b _ =>
        sq_nonneg
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j i b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j i b) r‖)
      (Finset.mem_univ k)

  have hI :
      (∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j i b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j i b) r‖ ^ 2)
        ≤
      ∑ a : Fin 3, ∑ b : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2 :=
    Finset.single_le_sum
      (fun a _ =>
        Finset.sum_nonneg
          (fun b _ =>
            sq_nonneg
              ‖h3PreterminalCanonicalFourierJetOnElapsed
                    hNS ht hEnd hTail (h3JetSlot2 j a b) q
                  -
                h3PreterminalCanonicalFourierJetOnElapsed
                    hNS ht hEnd hTail (h3JetSlot2 j a b) r‖))
      (Finset.mem_univ i)

  have h0 :
      0 ≤
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2 :=
    sq_nonneg _

  have h1 :
      0 ≤
      ∑ a : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ => sq_nonneg _)

  have h3 :
      0 ≤
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2 :=
    Finset.sum_nonneg
      (fun a _ =>
        Finset.sum_nonneg
          (fun b _ =>
            Finset.sum_nonneg
              (fun c _ => sq_nonneg _)))

  have hSq :
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) r‖ ^ 2
        ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ ^ 2 := by
    calc
      _ ≤
        ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j i b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j i b) r‖ ^ 2 :=
        hK
      _ ≤
        ∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2 :=
        hI
      _ ≤
        (‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2))
          +
        (∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2) := by
        exact
          le_add_of_nonneg_left
            (add_nonneg h0 h1)
      _ ≤
        (‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) r‖ ^ 2
          +
        (∑ a : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot1 j a) r‖ ^ 2))
          +
        (∑ a : Fin 3, ∑ b : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot2 j a b) r‖ ^ 2)
          +
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail (h3JetSlot3 j a b c) r‖ ^ 2) :=
        le_add_of_nonneg_right h3
      _ =
        ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j
            -
          h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail r j‖ ^ 2 :=
        hEnergy.symm

  have hLeft :
      0 ≤
      ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot2 j i k) r‖ :=
    norm_nonneg _

  have hRight :
      0 ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j
          -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail r j‖ :=
    norm_nonneg _

  nlinarith

/-- Every Fourier H³ jet-coordinate difference is bounded by the complete
weighted spectral difference of its velocity component. -/
theorem norm_h3PreterminalCanonicalFourierJetOnElapsed_sub_le_spectralCoordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (a : H3JetIndex)
    (q r : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail a q
        -
      h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail a r‖
      ≤
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q (h3JetVelocityComponent a)
        -
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r (h3JetVelocityComponent a)‖ := by
  rcases a with j | a
  · simpa [h3JetVelocityComponent, h3JetSlot0] using
      norm_h3PreterminalCanonicalFourierJetOnElapsed_slot0_sub_le_spectralCoordinate
        hNS ht hEnd hTail j q r

  · rcases a with ji | a
    · rcases ji with ⟨j, i⟩
      simpa [h3JetVelocityComponent, h3JetSlot1] using
        norm_h3PreterminalCanonicalFourierJetOnElapsed_slot1_sub_le_spectralCoordinate
          hNS ht hEnd hTail j i q r

    · rcases a with jik | jikl
      · rcases jik with ⟨j, ⟨i, k⟩⟩
        simpa [h3JetVelocityComponent, h3JetSlot2] using
          norm_h3PreterminalCanonicalFourierJetOnElapsed_slot2_sub_le_spectralCoordinate
            hNS ht hEnd hTail j i k q r

      · rcases jikl with ⟨j, ⟨i, ⟨k, l⟩⟩⟩
        simpa [h3JetVelocityComponent, h3JetSlot3] using
          norm_h3PreterminalCanonicalFourierJetOnElapsed_slot3_sub_le_spectralCoordinate
            hNS ht hEnd hTail j i k l q r

/-- Every physical H³ `L²` jet-coordinate difference obeys the same spectral
difference bound, by scalar Plancherel. -/
theorem norm_h3PreterminalCanonicalL2JetOnElapsed_sub_le_spectralCoordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (a : H3JetIndex)
    (q r : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail a q
        -
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail a r‖
      ≤
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q (h3JetVelocityComponent a)
        -
      h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r (h3JetVelocityComponent a)‖ := by
  calc
    ‖h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail a q
        -
      h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail a r‖
        =
      ‖h3ScalarFourierL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail a q
            -
           h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail a r)‖ := by
          symm
          exact
            norm_h3ScalarFourierL2
              (h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail a q
                -
               h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail a r)
    _ =
      ‖h3ScalarFourierL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail a q)
        -
        h3ScalarFourierL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail a r)‖ := by
          rw [h3ScalarFourierL2_sub]
    _ =
      ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail a q
        -
        h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail a r‖ := by
          rw [
            ← h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
              hNS ht hEnd hTail a q,
            ← h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
              hNS ht hEnd hTail a r
          ]
    _ ≤
      ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q (h3JetVelocityComponent a)
        -
        h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail r (h3JetVelocityComponent a)‖ :=
      norm_h3PreterminalCanonicalFourierJetOnElapsed_sub_le_spectralCoordinate
        hNS ht hEnd hTail a q r

/-- Strong weighted H³ spectral-state continuity gives strong continuity of
all 120 physical H³ `L²` jet coordinates. -/
theorem h3PreterminalCanonicalL2JetContinuousOnElapsed_of_spectralState
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSpectral :
      H3PreterminalCanonicalSpectralStateContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2JetContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro a

  rw [continuous_iff_continuousAt]
  intro q₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hCoordinate :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q (h3JetVelocityComponent a)) :=
    (continuous_apply (h3JetVelocityComponent a)).comp
      hSpectral

  have hCoordinateAt :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) tau =>
          ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q (h3JetVelocityComponent a)
              -
            h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q₀ (h3JetVelocityComponent a)‖)
        (𝓝 q₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hCoordinate.continuousAt

  exact
    squeeze_zero
      (fun q =>
        norm_nonneg
          (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q
            -
           h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q₀))
      (fun q =>
        norm_h3PreterminalCanonicalL2JetOnElapsed_sub_le_spectralCoordinate
          hNS ht hEnd hTail a q q₀)
      hCoordinateAt

/-- Pressure-free scalar H³-energy continuity therefore gives strong continuity
of the complete physical H³ `L²` jet. -/
theorem h3PreterminalCanonicalL2JetContinuousOnElapsed_of_physicalEnergy_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2JetContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2JetContinuousOnElapsed_of_spectralState
      hNS ht hEnd hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_physicalEnergy_pressureFree
        hNS ht hEnd hE hTail hPhysical)

/-- Locally, complete physical H³ `L²`-jet continuity is equivalent to scalar
physical H³-energy continuity. -/
theorem h3PreterminalCanonicalL2JetContinuousOnElapsed_iff_physicalEnergy_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail
      ↔
    H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail := by
  constructor

  · intro hL2
    exact
      h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_l2Jet
        hNS ht hEnd hTail hL2

  · intro hPhysical
    exact
      h3PreterminalCanonicalL2JetContinuousOnElapsed_of_physicalEnergy_pressureFree
        hNS ht hEnd hE hTail hPhysical

/-- The radius-wide full-jet frontier and scalar-energy frontier are exactly
equivalent. -/
theorem h3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontierOnRestartRadius_iff_energy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail
      ↔
    H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail := by
  constructor

  · intro hL2 q hqPos hEnd
    exact
      h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_l2Jet
        hNS ht hEnd hTail
        (hL2 q hqPos hEnd)

  · intro hEnergy q hqPos hEnd
    exact
      h3PreterminalCanonicalL2JetContinuousOnElapsed_of_physicalEnergy_pressureFree
        hNS ht hEnd hE hTail
        (hEnergy q hqPos hEnd)

/-- Globally, the full physical H³ `L²`-jet frontier and scalar physical
H³-energy frontier are the same analytic requirement. -/
theorem h3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontier_iff_energy :
    H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontier
      ↔
    H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier := by
  constructor

  · intro hL2 E hE u T t hNS ht hTail
    exact
      (h3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontierOnRestartRadius_iff_energy
        hNS ht hE hTail).1
        (hL2 E hE u T t hNS ht hTail)

  · intro hEnergy E hE u T t hNS ht hTail
    exact
      (h3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontierOnRestartRadius_iff_energy
        hNS ht hE hTail).2
        (hEnergy E hE u T t hNS ht hTail)

/-- The direct full-jet continuation theorem can therefore be driven by the
single scalar physical H³-energy continuity frontier. -/
theorem h3ControlProducesExtension_of_unitViscosityPhysicalH3EnergyContinuity_via_l2Jet
    (hEnergy :
      H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityPhysicalL2JetContinuity
      ((h3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontier_iff_energy).2
        hEnergy)

end

end Euclidean
end Bridge
end PrimeTensor
