import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative.Adjacent.Envelope.Pair.StateMass.Primitive

/-!
# Canonical primitive forcing rate

The preceding checkpoint freezes a genuine primitive forcing witness while
retaining the canonical state-mass reciprocal-width rate.

This layer sharpens the rate itself to one fixed primitive.  The second-q
branch uses the existing six primitive factors.  For the current modular
fourth-q hierarchy we introduce a nonconflicting six-way selector over exactly
the same primitive quantities: two raw-L2 factors and four order-ten
moment/raw-L1 factors.

In either branch a finite extraction freezes one primitive and preserves

    δ / (12 Δt_n) < C_pair^2 * C_prim * P(n)^4,

with `P(n) -> +∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000

/-! ## Modular fourth-q six-way primitive selector -/

noncomputable def h3TerminalForcingFourthQModularPrimitiveFactorAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 6) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ![
    ‖h3SpectralScalarRawFourierConjL2 (U k)‖,
    ‖h3SpectralScalarRawFourierL2 (U l)‖,
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U k),
    h3SpectralScalarRawFourierL1Mass (U l),
    h3SpectralScalarRawFourierL1Mass (U k),
    h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U l)
  ] q

theorem h3TerminalForcingFourthQModularPrimitiveFactorAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3)
    (q : Fin 6) :
    0 ≤
      h3TerminalForcingFourthQModularPrimitiveFactorAt
        hH3 hClass ht k l q := by

  fin_cases q <;>
    simp [
      h3TerminalForcingFourthQModularPrimitiveFactorAt,
      h3SpectralScalarRawFourierMomentMass_nonneg,
      h3SpectralScalarRawFourierL1Mass_nonneg
    ]

/--
The modular fourth-q fixed-pair state envelope is bounded by a universal
coefficient times the fourth power of one of its six actual primitive masses.
-/
theorem exists_primitive_h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four_modular
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    ∃ q : Fin 6,
      h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
          hH3 hClass ht k l
        ≤
      (
        2 * h3FourierMomentSplitCoefficient (10 : ℝ)
      )
        *
      (
        h3TerminalForcingFourthQModularPrimitiveFactorAt
          hH3 hClass ht k l q
      ) ^ 4 := by

  classical

  let f : Fin 6 → ℝ :=
    fun q =>
      h3TerminalForcingFourthQModularPrimitiveFactorAt
        hH3 hClass ht k l q

  have hUnivNonempty :
      (Finset.univ : Finset (Fin 6)).Nonempty :=
    ⟨0, Finset.mem_univ _⟩

  obtain ⟨q, _hqMem, hqMax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin 6))
      f
      hUnivNonempty

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let F := U k
  let G := U l
  let H : ℝ := f q

  have hH0 :
      0 ≤ H := by
    dsimp only [H, f]
    exact
      h3TerminalForcingFourthQModularPrimitiveFactorAt_nonneg
        hH3 hClass ht k l q

  have hL2F :
      ‖h3SpectralScalarRawFourierConjL2 F‖ ≤ H := by
    have h := hqMax 0 (Finset.mem_univ _)
    simpa [
      H, f, F, U,
      h3TerminalForcingFourthQModularPrimitiveFactorAt
    ] using h

  have hL2G :
      ‖h3SpectralScalarRawFourierL2 G‖ ≤ H := by
    have h := hqMax 1 (Finset.mem_univ _)
    simpa [
      H, f, G, U,
      h3TerminalForcingFourthQModularPrimitiveFactorAt
    ] using h

  have hM10F :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) F ≤ H := by
    have h := hqMax 2 (Finset.mem_univ _)
    simpa [
      H, f, F, U,
      h3TerminalForcingFourthQModularPrimitiveFactorAt
    ] using h

  have hL1G :
      h3SpectralScalarRawFourierL1Mass G ≤ H := by
    have h := hqMax 3 (Finset.mem_univ _)
    simpa [
      H, f, G, U,
      h3TerminalForcingFourthQModularPrimitiveFactorAt
    ] using h

  have hL1F :
      h3SpectralScalarRawFourierL1Mass F ≤ H := by
    have h := hqMax 4 (Finset.mem_univ _)
    simpa [
      H, f, F, U,
      h3TerminalForcingFourthQModularPrimitiveFactorAt
    ] using h

  have hM10G :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) G ≤ H := by
    have h := hqMax 5 (Finset.mem_univ _)
    simpa [
      H, f, G, U,
      h3TerminalForcingFourthQModularPrimitiveFactorAt
    ] using h

  have hL2F0 :
      0 ≤ ‖h3SpectralScalarRawFourierConjL2 F‖ :=
    norm_nonneg _

  have hL2G0 :
      0 ≤ ‖h3SpectralScalarRawFourierL2 G‖ :=
    norm_nonneg _

  have hM10F0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (10 : ℝ) F :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hM10G0 :
      0 ≤ h3SpectralScalarRawFourierMomentMass (10 : ℝ) G :=
    h3SpectralScalarRawFourierMomentMass_nonneg _ _

  have hL1F0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass F :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hL1G0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass G :=
    h3SpectralScalarRawFourierL1Mass_nonneg _

  have hC0 :
      0 ≤ h3FourierMomentSplitCoefficient (10 : ℝ) :=
    h3FourierMomentSplitCoefficient_nonneg (10 : ℝ)

  have hL2Product :
      ‖h3SpectralScalarRawFourierConjL2 F‖
          *
        ‖h3SpectralScalarRawFourierL2 G‖
        ≤
      H ^ 2 := by

    have hMul :
        ‖h3SpectralScalarRawFourierConjL2 F‖
            *
          ‖h3SpectralScalarRawFourierL2 G‖
          ≤
        H * H :=
      mul_le_mul
        hL2F
        hL2G
        hL2G0
        hH0

    simpa [pow_two] using hMul

  have hFirstMomentProduct :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
          *
        h3SpectralScalarRawFourierL1Mass G
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
            *
          h3SpectralScalarRawFourierL1Mass G
          ≤
        H * H :=
      mul_le_mul
        hM10F
        hL1G
        hL1G0
        hH0

    simpa [pow_two] using hMul

  have hSecondMomentProduct :
      h3SpectralScalarRawFourierL1Mass F
          *
        h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        ≤
      H ^ 2 := by

    have hMul :
        h3SpectralScalarRawFourierL1Mass F
            *
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
          ≤
        H * H :=
      mul_le_mul
        hL1F
        hM10G
        hM10G0
        hH0

    simpa [pow_two] using hMul

  have hMomentSum :
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
            *
          h3SpectralScalarRawFourierL1Mass G
        +
      h3SpectralScalarRawFourierL1Mass F
            *
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        ≤
      2 * H ^ 2 := by
    linarith

  have hWeightedMoment :
      h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
              *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        )
        ≤
      h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left
      hMomentSum
      hC0

  have hWeightedMoment0 :
      0 ≤
        h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (
          h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
              *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
        ) := by

    apply mul_nonneg hC0

    exact
      add_nonneg
        (mul_nonneg hM10F0 hL1G0)
        (mul_nonneg hL1F0 hM10G0)

  have hEnvelope :
      h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
          hH3 hClass ht k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (2 * H ^ 2)
      ) := by

    unfold h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
    dsimp only [F, G, U]

    exact
      mul_le_mul
        hL2Product
        hWeightedMoment
        hWeightedMoment0
        (sq_nonneg H)

  refine ⟨q, ?_⟩

  calc
    h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
        hH3 hClass ht k l
        ≤
      H ^ 2
        *
      (
        h3FourierMomentSplitCoefficient (10 : ℝ)
          *
        (2 * H ^ 2)
      ) :=
      hEnvelope
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (10 : ℝ)
      ) * H ^ 4 := by
      ring
    _ =
      (
        2 * h3FourierMomentSplitCoefficient (10 : ℝ)
      )
        *
      (
        h3TerminalForcingFourthQModularPrimitiveFactorAt
          hH3 hClass ht k l q
      ) ^ 4 := by
      rfl

/-! ## Canonical primitive rate package -/

def H3TerminalPhysicalTopDissipationFixedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ ψ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        StrictMono ψ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              ∃ hr :
                ∀ n : ℕ,
                  r (φ (ψ n)) ∈ Set.Ioo a T,
                Tendsto
                    (fun n : ℕ => s (φ (ψ n)))
                    atTop
                    (𝓝 T)
                  ∧
                Tendsto
                    (fun n : ℕ => σ (m (q (φ (ψ n)))))
                    atTop
                    (𝓝 T)
                  ∧
                (
                  ∀ n : ℕ,
                    s (φ (ψ n))
                      <
                    σ (m (q (φ (ψ n))))
                )
                  ∧
                (
                  ∀ n : ℕ,
                    r (φ (ψ n)) ∈
                      Set.Icc
                        (s (φ (ψ n)))
                        (σ (m (q (φ (ψ n)))))
                )
                  ∧
                Tendsto
                    (fun n : ℕ => r (φ (ψ n)))
                    atTop
                    (𝓝 T)
                  ∧
                (
                  (
                    ∃ k₀ l₀ : Fin 3,
                      ∃ χ : ℕ → ℕ,
                        StrictMono χ
                          ∧
                        ∃ q₀ : Fin 6,
                          ∃ ω : ℕ → ℕ,
                            StrictMono ω
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  s (φ (ψ (χ (ω n)))))
                                atTop
                                (𝓝 T)
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  σ (m (q (φ (ψ (χ (ω n)))))))
                                atTop
                                (𝓝 T)
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  r (φ (ψ (χ (ω n)))))
                                atTop
                                (𝓝 T)
                              ∧
                            (
                              ∀ n : ℕ,
                                δ
                                    /
                                  (
                                    12
                                      *
                                    (
                                      σ (m (q (φ (ψ (χ (ω n))))))
                                        -
                                      s (φ (ψ (χ (ω n))))
                                    )
                                  )
                                  <
                                (
                                  h3TerminalForcingSecondQFixedPairCoefficient
                                ) ^ 2
                                  *
                                (
                                  2 *
                                    h3FourierMomentSplitCoefficient (6 : ℝ)
                                )
                                  *
                                (
                                  h3TerminalForcingSecondQPrimitiveFactorAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    k₀ l₀ q₀
                                ) ^ 4
                            )
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  h3TerminalForcingSecondQPrimitiveFactorAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    k₀ l₀ q₀
                              )
                              atTop
                              atTop
                  )
                    ∨
                  (
                    ∃ k₀ l₀ : Fin 3,
                      ∃ χ : ℕ → ℕ,
                        StrictMono χ
                          ∧
                        ∃ q₀ : Fin 6,
                          ∃ ω : ℕ → ℕ,
                            StrictMono ω
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  s (φ (ψ (χ (ω n)))))
                                atTop
                                (𝓝 T)
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  σ (m (q (φ (ψ (χ (ω n)))))))
                                atTop
                                (𝓝 T)
                              ∧
                            Tendsto
                                (fun n : ℕ =>
                                  r (φ (ψ (χ (ω n)))))
                                atTop
                                (𝓝 T)
                              ∧
                            (
                              ∀ n : ℕ,
                                δ
                                    /
                                  (
                                    12
                                      *
                                    (
                                      σ (m (q (φ (ψ (χ (ω n))))))
                                        -
                                      s (φ (ψ (χ (ω n))))
                                    )
                                  )
                                  <
                                (
                                  h3TerminalForcingFourthQFixedPairCoefficient
                                ) ^ 2
                                  *
                                (
                                  2 *
                                    h3FourierMomentSplitCoefficient (10 : ℝ)
                                )
                                  *
                                (
                                  h3TerminalForcingFourthQModularPrimitiveFactorAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    k₀ l₀ q₀
                                ) ^ 4
                            )
                              ∧
                            Tendsto
                              (
                                fun n : ℕ =>
                                  h3TerminalForcingFourthQModularPrimitiveFactorAt
                                    hH3 hClass
                                    (hr (χ (ω n)))
                                    k₀ l₀ q₀
                              )
                              atTop
                              atTop
                  )
                )

theorem fixedForcingPrimitiveCanonicalRateEscapeSubsequenceOf_of_stateMassCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hState :
      H3TerminalPhysicalTopDissipationFixedForcingProductStateMassCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
      hH3 hClass σ := by

  classical

  obtain
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      hBranch
    ⟩ :=
    hState

  refine
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hr,
      hsTendsto,
      hSigmaTendsto,
      hForward,
      hPoint,
      hrTendsto,
      ?_
    ⟩

  rcases hBranch with hSecond | hFourth

  · rcases hSecond with
      ⟨
        k₀,
        l₀,
        χ,
        hChiMono,
        hsChi,
        hSigmaChi,
        hrChi,
        hRate,
        hEnvelopeTop
      ⟩

    have hChoice :
        ∀ n : ℕ,
          ∃ p : Fin 6,
            h3TerminalForcingSecondQStateMassEnvelopeAt
                hH3 hClass (hr (χ n)) k₀ l₀
              ≤
            (
              2 * h3FourierMomentSplitCoefficient (6 : ℝ)
            )
              *
            (
              h3TerminalForcingSecondQPrimitiveFactorAt
                hH3 hClass (hr (χ n)) k₀ l₀ p
            ) ^ 4 := by
      intro n
      exact
        exists_primitive_h3TerminalForcingSecondQStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four
          hH3 hClass (hr (χ n)) k₀ l₀

    choose p hp using hChoice

    let C : ℝ :=
      2 * h3FourierMomentSplitCoefficient (6 : ℝ)

    have hC0 :
        0 ≤ C := by
      dsimp only [C]
      exact
        mul_nonneg
          (by norm_num)
          (h3FourierMomentSplitCoefficient_nonneg (6 : ℝ))

    have hPairSq0 :
        0 ≤
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2 :=
      sq_nonneg _

    have hChosenRate :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ (χ n)))))
                  -
                s (φ (ψ (χ n)))
              )
            )
            <
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
            *
          C
            *
          (
            h3TerminalForcingSecondQPrimitiveFactorAt
              hH3 hClass (hr (χ n)) k₀ l₀ (p n)
          ) ^ 4 := by

      intro n

      have hScaled :
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
              *
            h3TerminalForcingSecondQStateMassEnvelopeAt
              hH3 hClass (hr (χ n)) k₀ l₀
            ≤
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
              *
            (
              C
                *
              (
                h3TerminalForcingSecondQPrimitiveFactorAt
                  hH3 hClass (hr (χ n)) k₀ l₀ (p n)
              ) ^ 4
            ) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [C] using hp n)
          hPairSq0

      have hRaw :=
        (hRate n).trans_le
          hScaled

      simpa only [mul_assoc] using
        hRaw

    have hChosenTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingSecondQPrimitiveFactorAt
                hH3 hClass (hr (χ n)) k₀ l₀ (p n)
          )
          atTop
          atTop := by

      refine tendsto_atTop.2 ?_
      intro M

      let R : ℝ := max M 1

      have hMLe :
          M ≤ R := by
        dsimp only [R]
        exact le_max_left M 1

      have hR0 :
          0 ≤ R := by
        dsimp only [R]
        exact
          le_trans
            (by norm_num)
            (le_max_right M 1)

      have hLarge :
          ∀ᶠ n : ℕ in atTop,
            C * R ^ 4 + 1
              <
            h3TerminalForcingSecondQStateMassEnvelopeAt
              hH3 hClass (hr (χ n)) k₀ l₀ :=
        hEnvelopeTop.eventually
          (eventually_gt_atTop (C * R ^ 4 + 1))

      filter_upwards [hLarge] with n hn

      let P : ℝ :=
        h3TerminalForcingSecondQPrimitiveFactorAt
          hH3 hClass (hr (χ n)) k₀ l₀ (p n)

      have hP0 :
          0 ≤ P := by
        dsimp only [P]
        exact
          h3TerminalForcingSecondQPrimitiveFactorAt_nonneg
            hH3 hClass (hr (χ n)) k₀ l₀ (p n)

      have hBound :
          h3TerminalForcingSecondQStateMassEnvelopeAt
              hH3 hClass (hr (χ n)) k₀ l₀
            ≤
          C * P ^ 4 := by
        dsimp only [C, P]
        exact hp n

      have hRLtP :
          R < P := by
        by_contra hNot

        have hPLe :
            P ≤ R :=
          le_of_not_gt hNot

        have hPowLe :
            P ^ 4 ≤ R ^ 4 :=
          pow_le_pow_left₀ hP0 hPLe 4

        have hScaled :
            C * P ^ 4 ≤ C * R ^ 4 :=
          mul_le_mul_of_nonneg_left
            hPowLe
            hC0

        have hEnvelopeLe :
            h3TerminalForcingSecondQStateMassEnvelopeAt
                hH3 hClass (hr (χ n)) k₀ l₀
              ≤
            C * R ^ 4 :=
          hBound.trans hScaled

        linarith

      exact
        hMLe.trans
          (le_of_lt hRLtP)

    have hFrequentlySome :
        ∃ᶠ n : ℕ in atTop,
          ∃ p₀ : Fin 6,
            p n = p₀ :=
      Frequently.of_forall
        (fun n => ⟨p n, rfl⟩)

    obtain ⟨q₀, hFrequently⟩ :=
      (Filter.frequently_exists).1
        hFrequentlySome

    obtain ⟨ω, hOmegaMono, hFixed⟩ :=
      extraction_of_frequently_atTop
        hFrequently

    have hOmegaTop :
        Tendsto ω atTop atTop :=
      hOmegaMono.tendsto_atTop

    have hRateFixed :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ (χ (ω n))))))
                  -
                s (φ (ψ (χ (ω n))))
              )
            )
            <
          (h3TerminalForcingSecondQFixedPairCoefficient : ℝ) ^ 2
            *
          (
            2 * h3FourierMomentSplitCoefficient (6 : ℝ)
          )
            *
          (
            h3TerminalForcingSecondQPrimitiveFactorAt
              hH3 hClass (hr (χ (ω n))) k₀ l₀ q₀
          ) ^ 4 := by

      intro n
      have hRaw :=
        hChosenRate
          (ω n)
      rw [hFixed n] at hRaw
      simpa only [C] using hRaw

    have hTopBefore :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingSecondQPrimitiveFactorAt
                hH3 hClass
                (hr (χ (ω n)))
                k₀ l₀
                (p (ω n))
          )
          atTop
          atTop :=
      hChosenTop.comp
        hOmegaTop

    have hPrimitiveTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingSecondQPrimitiveFactorAt
                hH3 hClass
                (hr (χ (ω n)))
                k₀ l₀ q₀
          )
          atTop
          atTop := by
      simpa only [hFixed] using
        hTopBefore

    exact
      Or.inl
        ⟨
          k₀,
          l₀,
          χ,
          hChiMono,
          q₀,
          ω,
          hOmegaMono,
          hsChi.comp hOmegaTop,
          hSigmaChi.comp hOmegaTop,
          hrChi.comp hOmegaTop,
          hRateFixed,
          hPrimitiveTop
        ⟩

  · rcases hFourth with
      ⟨
        k₀,
        l₀,
        χ,
        hChiMono,
        hsChi,
        hSigmaChi,
        hrChi,
        hRate,
        hEnvelopeTop
      ⟩

    have hChoice :
        ∀ n : ℕ,
          ∃ p : Fin 6,
            h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
                hH3 hClass (hr (χ n)) k₀ l₀
              ≤
            (
              2 * h3FourierMomentSplitCoefficient (10 : ℝ)
            )
              *
            (
              h3TerminalForcingFourthQModularPrimitiveFactorAt
                hH3 hClass (hr (χ n)) k₀ l₀ p
            ) ^ 4 := by
      intro n
      exact
        exists_primitive_h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_le_fixedCoefficient_mul_pow_four_modular
          hH3 hClass (hr (χ n)) k₀ l₀

    choose p hp using hChoice

    let C : ℝ :=
      2 * h3FourierMomentSplitCoefficient (10 : ℝ)

    have hC0 :
        0 ≤ C := by
      dsimp only [C]
      exact
        mul_nonneg
          (by norm_num)
          (h3FourierMomentSplitCoefficient_nonneg (10 : ℝ))

    have hPairSq0 :
        0 ≤
          (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2 :=
      sq_nonneg _

    have hChosenRate :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ (χ n)))))
                  -
                s (φ (ψ (χ n)))
              )
            )
            <
          (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
            *
          C
            *
          (
            h3TerminalForcingFourthQModularPrimitiveFactorAt
              hH3 hClass (hr (χ n)) k₀ l₀ (p n)
          ) ^ 4 := by

      intro n

      have hScaled :
          (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
              *
            h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
              hH3 hClass (hr (χ n)) k₀ l₀
            ≤
          (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
              *
            (
              C
                *
              (
                h3TerminalForcingFourthQModularPrimitiveFactorAt
                  hH3 hClass (hr (χ n)) k₀ l₀ (p n)
              ) ^ 4
            ) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [C] using hp n)
          hPairSq0

      have hRaw :=
        (hRate n).trans_le
          hScaled

      simpa only [mul_assoc] using
        hRaw

    have hChosenTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQModularPrimitiveFactorAt
                hH3 hClass (hr (χ n)) k₀ l₀ (p n)
          )
          atTop
          atTop := by

      refine tendsto_atTop.2 ?_
      intro M

      let R : ℝ := max M 1

      have hMLe :
          M ≤ R := by
        dsimp only [R]
        exact le_max_left M 1

      have hR0 :
          0 ≤ R := by
        dsimp only [R]
        exact
          le_trans
            (by norm_num)
            (le_max_right M 1)

      have hLarge :
          ∀ᶠ n : ℕ in atTop,
            C * R ^ 4 + 1
              <
            h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
              hH3 hClass (hr (χ n)) k₀ l₀ :=
        hEnvelopeTop.eventually
          (eventually_gt_atTop (C * R ^ 4 + 1))

      filter_upwards [hLarge] with n hn

      let P : ℝ :=
        h3TerminalForcingFourthQModularPrimitiveFactorAt
          hH3 hClass (hr (χ n)) k₀ l₀ (p n)

      have hP0 :
          0 ≤ P := by
        dsimp only [P]
        exact
          h3TerminalForcingFourthQModularPrimitiveFactorAt_nonneg
            hH3 hClass (hr (χ n)) k₀ l₀ (p n)

      have hBound :
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
              hH3 hClass (hr (χ n)) k₀ l₀
            ≤
          C * P ^ 4 := by
        dsimp only [C, P]
        exact hp n

      have hRLtP :
          R < P := by
        by_contra hNot

        have hPLe :
            P ≤ R :=
          le_of_not_gt hNot

        have hPowLe :
            P ^ 4 ≤ R ^ 4 :=
          pow_le_pow_left₀ hP0 hPLe 4

        have hScaled :
            C * P ^ 4 ≤ C * R ^ 4 :=
          mul_le_mul_of_nonneg_left
            hPowLe
            hC0

        have hEnvelopeLe :
            h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
                hH3 hClass (hr (χ n)) k₀ l₀
              ≤
            C * R ^ 4 :=
          hBound.trans hScaled

        linarith

      exact
        hMLe.trans
          (le_of_lt hRLtP)

    have hFrequentlySome :
        ∃ᶠ n : ℕ in atTop,
          ∃ p₀ : Fin 6,
            p n = p₀ :=
      Frequently.of_forall
        (fun n => ⟨p n, rfl⟩)

    obtain ⟨q₀, hFrequently⟩ :=
      (Filter.frequently_exists).1
        hFrequentlySome

    obtain ⟨ω, hOmegaMono, hFixed⟩ :=
      extraction_of_frequently_atTop
        hFrequently

    have hOmegaTop :
        Tendsto ω atTop atTop :=
      hOmegaMono.tendsto_atTop

    have hRateFixed :
        ∀ n : ℕ,
          δ
              /
            (
              12
                *
              (
                σ (m (q (φ (ψ (χ (ω n))))))
                  -
                s (φ (ψ (χ (ω n))))
              )
            )
            <
          (h3TerminalForcingFourthQFixedPairCoefficient : ℝ) ^ 2
            *
          (
            2 * h3FourierMomentSplitCoefficient (10 : ℝ)
          )
            *
          (
            h3TerminalForcingFourthQModularPrimitiveFactorAt
              hH3 hClass (hr (χ (ω n))) k₀ l₀ q₀
          ) ^ 4 := by

      intro n
      have hRaw :=
        hChosenRate
          (ω n)
      rw [hFixed n] at hRaw
      simpa only [C] using hRaw

    have hTopBefore :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQModularPrimitiveFactorAt
                hH3 hClass
                (hr (χ (ω n)))
                k₀ l₀
                (p (ω n))
          )
          atTop
          atTop :=
      hChosenTop.comp
        hOmegaTop

    have hPrimitiveTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingFourthQModularPrimitiveFactorAt
                hH3 hClass
                (hr (χ (ω n)))
                k₀ l₀ q₀
          )
          atTop
          atTop := by
      simpa only [hFixed] using
        hTopBefore

    exact
      Or.inr
        ⟨
          k₀,
          l₀,
          χ,
          hChiMono,
          q₀,
          ω,
          hOmegaMono,
          hsChi.comp hOmegaTop,
          hSigmaChi.comp hOmegaTop,
          hrChi.comp hOmegaTop,
          hRateFixed,
          hPrimitiveTop
        ⟩

theorem exists_fixed_terminalSequence_with_canonicalForcingPrimitiveRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
        )
        atTop
        (𝓝 0)
        ∧
      ∃ σ : ℕ → ℝ,
        ∃ hσ :
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T,
          Tendsto σ atTop (𝓝 T)
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal (ε ^ 2 / 64)
                <
              16 *
                h3TerminalPhysicalDissipationBadConeHighRadialMass
                  hH3
                  i
                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                  1
                  (σ n)
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hσ n).1,
                    (hσ n).2
                  ⟩
          )
            ∧
          H3TerminalPhysicalTopDissipationFixedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
            hH3 hClass σ := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hState
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalForcingProductStateMassRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hPrimitive :
      H3TerminalPhysicalTopDissipationFixedForcingPrimitiveCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fixedForcingPrimitiveCanonicalRateEscapeSubsequenceOf_of_stateMassCanonicalRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hState

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hPrimitive
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
