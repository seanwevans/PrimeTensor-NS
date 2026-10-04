import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Velocity.Truncation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncation.Convergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Strong cutoff removal for generic natural-radial Fourier L² states

For the generic bounded multiplier

    T[m,R] f = 1_{|ξ| < R} |ξ|^m f,

the natural radii `R_n = n+1` exhaust frequency space.  Thus, whenever a
genuine Fourier `L²` state `G` satisfies

    G(ξ) = |ξ|^m F(ξ)

almost everywhere, we have

    T[m,n+1] F -> G

strongly in Fourier `L²`.

The proof is completely order-independent.  The square error is exactly the
square `L²` mass of `G` on the complementary high-frequency tail.

This file also records the pointwise-domain estimate

    ‖T[m,R] F‖ ≤ ‖G‖,

which is the domination needed by the forthcoming Banach-valued dominated
convergence / FTC argument.

Finally, the generic statements are specialized to the two selected objects
already built on a positive terminal-half slab:

* arbitrary radial selected velocity;
* arbitrary radial selected projected RHS.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityNatRadialConvergence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Natural high-frequency exhaustion -/

/--
Complement of the generic natural radial cutoff ball at radius `n+1`.
-/
def h3SelectedNatRadialNaturalHighSet
    (n : ℕ) :
    Set H3FourierPoint3 :=
  (
    h3SelectedNatRadialFrequencyBelow
      ((n : ℝ) + 1)
  )ᶜ

theorem measurableSet_h3SelectedNatRadialNaturalHighSet
    (n : ℕ) :
    MeasurableSet
      (h3SelectedNatRadialNaturalHighSet n) := by
  unfold h3SelectedNatRadialNaturalHighSet
  exact
    (
      measurableSet_h3SelectedNatRadialFrequencyBelow
        ((n : ℝ) + 1)
    ).compl

/--
The natural generic high-frequency tails are antitone.
-/
theorem antitone_h3SelectedNatRadialNaturalHighSet :
    Antitone h3SelectedNatRadialNaturalHighSet := by

  intro m n hmn
  intro ξ hξ

  simp only [
    h3SelectedNatRadialNaturalHighSet,
    Set.mem_compl_iff,
    h3SelectedNatRadialFrequencyBelow,
    Metric.mem_ball,
    dist_zero_right
  ] at hξ ⊢

  intro hLow

  apply hξ

  have hCast :
      (m : ℝ) + 1
        ≤
      (n : ℝ) + 1 := by
    exact_mod_cast
      (Nat.add_le_add_right hmn 1)

  exact
    lt_of_lt_of_le hLow hCast

/--
The natural generic high-frequency tails shrink to the empty set.
-/
theorem iInter_h3SelectedNatRadialNaturalHighSet_eq_empty :
    (⋂ n : ℕ, h3SelectedNatRadialNaturalHighSet n)
      =
    (∅ : Set H3FourierPoint3) := by

  ext ξ

  simp only [
    Set.mem_iInter,
    Set.mem_empty_iff_false,
    iff_false
  ]

  intro hAll

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt ‖ξ‖

  have hHigh :=
    hAll N

  simp only [
    h3SelectedNatRadialNaturalHighSet,
    Set.mem_compl_iff,
    h3SelectedNatRadialFrequencyBelow,
    Metric.mem_ball,
    dist_zero_right
  ] at hHigh

  apply hHigh

  have hNN :
      (N : ℝ) < (N : ℝ) + 1 := by
    linarith

  exact
    lt_trans hN hNN

/--
Every fixed Fourier `L²` state has vanishing square mass on the generic
natural high-frequency tails.
-/
theorem tendsto_h3FourierComplexL2_selectedNatRadial_high_squareMass_zero
    (G : H3FourierComplexL2) :
    Tendsto
      (fun n : ℕ =>
        ∫ ξ in h3SelectedNatRadialNaturalHighSet n,
          ‖G ξ‖ ^ 2
        ∂volume)
      atTop
      (𝓝 0) := by

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖G ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp G).norm.integrable_sq

  have hTail :=
    tendsto_setIntegral_of_antitone
      (f :=
        fun ξ : H3FourierPoint3 =>
          ‖G ξ‖ ^ 2)
      (fun n =>
        measurableSet_h3SelectedNatRadialNaturalHighSet n)
      antitone_h3SelectedNatRadialNaturalHighSet
      ⟨0, hInt.integrableOn⟩

  rw [
    iInter_h3SelectedNatRadialNaturalHighSet_eq_empty
  ] at hTail

  simpa using hTail

/-! ## Exact truncation error -/

/--
If `G = |ξ|^m F` almost everywhere, the square error of the natural cutoff is
exactly the square mass of `G` on the complementary high-frequency tail.
-/
theorem norm_sq_h3SelectedTruncatedNatRadialL2_sub_eq_high_squareMass
    (m : ℕ)
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          F ξ))
    (n : ℕ) :
    ‖(
      h3SelectedTruncatedNatRadialL2
          m
          ((n : ℝ) + 1)
          (by positivity)
          F
        -
      G
    )‖ ^ 2
      =
    ∫ ξ in h3SelectedNatRadialNaturalHighSet n,
      ‖G ξ‖ ^ 2
    ∂volume := by

  rw [
    h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
  ]

  rw [
    ← integral_indicator
      (measurableSet_h3SelectedNatRadialNaturalHighSet n)
  ]

  apply integral_congr_ae

  have hTrunc :=
    h3SelectedTruncatedNatRadialL2_ae
      m
      ((n : ℝ) + 1)
      (by positivity)
      F

  filter_upwards [hTrunc, hFG]
    with ξ hTruncξ hFGξ

  rw [hTruncξ]

  unfold
    h3SelectedTruncatedNatRadialFunction
    h3SelectedTruncatedNatRadialMultiplier

  by_cases hLow :
      ξ ∈
        h3SelectedNatRadialFrequencyBelow
          ((n : ℝ) + 1)

  · rw [Set.indicator_of_mem hLow]
    rw [hFGξ]

    have hNotHigh :
        ξ ∉ h3SelectedNatRadialNaturalHighSet n := by
      simp only [
        h3SelectedNatRadialNaturalHighSet,
        Set.mem_compl_iff,
        not_not
      ]
      exact hLow

    rw [Set.indicator_of_notMem hNotHigh]

    simp

  · rw [Set.indicator_of_notMem hLow]

    have hHigh :
        ξ ∈ h3SelectedNatRadialNaturalHighSet n := by
      simpa only [
        h3SelectedNatRadialNaturalHighSet,
        Set.mem_compl_iff
      ] using hLow

    rw [Set.indicator_of_mem hHigh]

    simp

/-! ## Strong convergence and domination -/

/--
Generic strong cutoff removal for the natural radial multiplier.
-/
theorem tendsto_h3SelectedTruncatedNatRadialL2_of_ae_eq
    (m : ℕ)
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          F ξ)) :
    Tendsto
      (fun n : ℕ =>
        h3SelectedTruncatedNatRadialL2
          m
          ((n : ℝ) + 1)
          (by positivity)
          F)
      atTop
      (𝓝 G) := by

  apply
    tendsto_iff_norm_sub_tendsto_zero.2

  have hTail :=
    tendsto_h3FourierComplexL2_selectedNatRadial_high_squareMass_zero
      G

  have hSq :
      Tendsto
        (fun n : ℕ =>
          ‖(
            h3SelectedTruncatedNatRadialL2
                m
                ((n : ℝ) + 1)
                (by positivity)
                F
              -
            G
          )‖ ^ 2)
        atTop
        (𝓝 0) := by

    apply
      hTail.congr'

    filter_upwards with n

    exact
      (
        norm_sq_h3SelectedTruncatedNatRadialL2_sub_eq_high_squareMass
          m F G hFG n
      ).symm

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp
      hSq

  change
    Tendsto
      (fun n : ℕ =>
        Real.sqrt
          (
            ‖(
              h3SelectedTruncatedNatRadialL2
                  m
                  ((n : ℝ) + 1)
                  (by positivity)
                  F
                -
              G
            )‖ ^ 2
          ))
      atTop
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

/--
Every bounded truncation is norm-dominated by the full radial state whenever
the latter represents `|ξ|^m F`.
-/
theorem norm_h3SelectedTruncatedNatRadialL2_le_of_ae_eq
    (m : ℕ)
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          F ξ))
    {R : ℝ}
    (hR : 0 ≤ R) :
    ‖h3SelectedTruncatedNatRadialL2
        m R hR F‖
      ≤
    ‖G‖ := by

  apply Lp.norm_le_norm_of_ae_le

  have hTrunc :=
    h3SelectedTruncatedNatRadialL2_ae
      m R hR F

  filter_upwards [hTrunc, hFG]
    with ξ hTruncξ hFGξ

  rw [hTruncξ, hFGξ]

  unfold
    h3SelectedTruncatedNatRadialFunction
    h3SelectedTruncatedNatRadialMultiplier

  by_cases hLow :
      ξ ∈ h3SelectedNatRadialFrequencyBelow R

  · rw [Set.indicator_of_mem hLow]

  · rw [
      Set.indicator_of_notMem hLow,
      zero_mul,
      norm_zero
    ]
    exact norm_nonneg _

/-! ## Selected velocity specialization -/

/--
Natural radial truncations of the raw selected velocity converge strongly to
the arbitrary radial selected-velocity package.
-/
theorem tendsto_h3SelectedTruncatedNatRadialL2_selectedVelocityOnSlab
    (m : ℕ)
    (hm : 2 ≤ m)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    let F : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        (s : ℝ)
        i
    Tendsto
      (fun n : ℕ =>
        h3SelectedTruncatedNatRadialL2
          m
          ((n : ℝ) + 1)
          (by positivity)
          F)
      atTop
      (
        𝓝
          (
            h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
              m hm
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (by positivity : 0 < Q / 2)
              hQR s i
          )
      ) := by

  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let F : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (s : ℝ)
      i

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (by positivity : 0 < Q / 2)
      hQR s i

  have hFG :
      ((G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          F ξ) := by
    dsimp only [G, F]
    exact
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
        m hm
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        (by positivity : 0 < Q / 2)
        hQR s i

  exact
    tendsto_h3SelectedTruncatedNatRadialL2_of_ae_eq
      m _ _ hFG

/-! ## Selected projected-RHS specialization -/

/--
Natural radial truncations of the unweighted selected projected RHS converge
strongly to the arbitrary radial projected-RHS package.
-/
theorem tendsto_h3SelectedTruncatedNatRadialL2_selectedProjectedRHSOnSlab
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let qRadius :=
      h3SelectedProjectedRHSSlabRadius hE hQ hQR s
    let F : H3FourierComplexL2 :=
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht₀ hE hTail qRadius i
    Tendsto
      (fun n : ℕ =>
        h3SelectedTruncatedNatRadialL2
          m
          ((n : ℝ) + 1)
          (by positivity)
          F)
      atTop
      (
        𝓝
          (
            h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
              m hNS ht₀ hE hTail hQ hQR i s
          )
      ) := by

  dsimp only

  let qRadius :=
    h3SelectedProjectedRHSSlabRadius
      hE hQ hQR s

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i s

  have hFG :
      ((G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          F ξ) := by
    dsimp only [G, F, qRadius]
    exact
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
        m hNS ht₀ hE hTail hQ hQR i s

  exact
    tendsto_h3SelectedTruncatedNatRadialL2_of_ae_eq
      m _ _ hFG

/--
Every natural radial truncation of the selected projected RHS is norm
dominated by the full arbitrary-radial projected-RHS state.
-/
theorem norm_h3SelectedTruncatedNatRadialL2_selectedProjectedRHSOnSlab_le
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q)
    (n : ℕ) :
    let qRadius :=
      h3SelectedProjectedRHSSlabRadius hE hQ hQR s
    let F : H3FourierComplexL2 :=
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht₀ hE hTail qRadius i
    ‖h3SelectedTruncatedNatRadialL2
        m
        ((n : ℝ) + 1)
        (by positivity)
        F‖
      ≤
    ‖h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        m hNS ht₀ hE hTail hQ hQR i s‖ := by

  dsimp only

  let qRadius :=
    h3SelectedProjectedRHSSlabRadius
      hE hQ hQR s

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i s

  have hFG :
      ((G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          F ξ) := by
    dsimp only [G, F, qRadius]
    exact
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
        m hNS ht₀ hE hTail hQ hQR i s

  exact
    norm_h3SelectedTruncatedNatRadialL2_le_of_ae_eq
      m _ _ hFG
      (by positivity)

end

end Euclidean
end Bridge
end PrimeTensor
