import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Amplitude.Corridor
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Energy.Kinetic.Low.Tail
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Canonical.Actual.Gradient.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.From.Derivative.Identities

/-!
# Positive-growth frequency forcing of the BKM vorticity-log factor

Fix a strict terminal anchor `b` and any scalar vorticity envelope `g` on the
tail `(b,T)`.

The closed kinetic-energy monotonicity theorem supplies the time-independent
low-frequency radius required by the selected BKM endpoint.  Therefore the
actual velocity gradient obeys the canonical logarithmic estimate

    1 + |∇u|
      ≤
    B_b (1 + |g|) (1 + log E),

where

    B_b =
      h3BKMCanonicalSelectedLogGradientConstant
        (sqrt(E₀(b))).

Using this envelope in the closed H³ transport commutator estimate gives

    -T_H3
      ≤
    4422 (B_b + 1)
      (1 + |g|) (1 + log E) E.

At a positive-growth time, exact energy balance implies

    2 D < -T_H3,

so

    2 D / E
      <
    4422 (B_b + 1)
      (1 + |g|) (1 + log E).

Under hypothetical nonextension, the full H³ energy is eventually controlled
by the top-order block,

    E ≤ C_b E₃,
    C_b = 4 + 3 E₀(b).

Since

    Λ₃² = D₃ / E₃,
    D₃ ≤ D,

we obtain, on a sufficiently late positive-growth tail,

    2 Λ₃²
      <
    C_b
      * 4422 (B_b + 1)
      * (1 + |g|)
      * (1 + log E).

Thus every admissible vorticity envelope must carry the terminal
high-frequency cascade through the BKM logarithmic factor.

This is still a necessary consequence of hypothetical nonextension.  The next
step is to combine it with the already-proved amplitude bound
`E ≤ const * Λ₃^6`, replacing `log E` by a logarithm of the characteristic
frequency.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Canonical BKM envelope on an arbitrary later anchor -/

/--
Closed derivative identities make the kinetic energy antitone, so any strict
anchor `b` supplies exactly the kinetic low-frequency control required by the
canonical selected BKM endpoint.
-/
theorem bkmKineticEnergyControlledFromAnchor_of_h3Path_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
    BKMKineticEnergyControlledFromAnchor
      u b T := by

  have hAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  intro t ht

  have htOld :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 ht.1,
      ht.2
    ⟩

  exact
    hAnti
      hb
      htOld
      (le_of_lt ht.1)

/-! ## Pointwise positive-growth BKM transport forcing -/

/--
On a strict later tail, any vorticity envelope controls the normalized
dissipation at positive-growth times through the canonical BKM logarithmic
factor.
-/
theorem two_mul_dissipation_div_energy_lt_canonicalBKM_vorticityLogFactor_of_pos_deriv
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    {g : ℝ → ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T)
    (hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope
            u g s)
    (ht :
      t ∈ Set.Ioo b T)
    (hDerivative :
      0 < deriv (velocityH3EnergyAt u) t) :
    2
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      )
      <
    4422
      *
    (
      h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt
            (velocityH3Energy0At u b))
        +
      1
    )
      *
    (1 + |g t|)
      *
    (1 + Real.log (velocityH3EnergyAt u t)) := by

  have hbAbs :
      b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        hb.1,
      hb.2
    ⟩

  have hClassB :
      PreterminalH3EnergyClass
        u b T :=
    preterminalH3EnergyClass_restrict_left
      hClass
      (le_of_lt hb.1)
      hb.2

  have hProfile :
      H3EnergyProfileFrom
        u b T
        (velocityH3EnergyAt u) :=
    h3EnergyProfileFrom_h3Path
      hH3
      hbAbs

  have hKinetic :
      BKMKineticEnergyControlledFromAnchor
        u b T :=
    bkmKineticEnergyControlledFromAnchor_of_h3Path_closed
      hH3
      hClass
      hb

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

  have hActual :
      ActualVelocityGradientLogBoundFrom
        u b T g
        (velocityH3EnergyAt u)
        B := by

    dsimp only [B]

    exact
      actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_kineticEnergyControlledFromAnchor
        hH3.navier_stokes
        hbAbs
        hg
        hProfile
        hKinetic

  let h : ℝ → ℝ :=
    h3BKMLogarithmicGradientEnvelope
      g
      (velocityH3EnergyAt u)
      B

  have hGradient :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VelocityGradientEnvelope
            u h s := by

    intro s hs

    dsimp only [h]

    exact
      velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
        hActual
        hs

  have hTransportTail :
      H3TransportControlledOnTail
        u b T h 4422 :=
    h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3
      hClassB
      hGradient

  have hTransport :=
    neg_transport_le_of_commutatorBound
      (hTransportTail t ht).2

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt
      u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hENonneg :
      0 ≤ velocityH3EnergyAt u t :=
    le_of_lt hEPos

  have hEndpoint :
      1 + |h t|
        ≤
      (B + 1)
        * (1 + |g t|)
        * (1 + Real.log (velocityH3EnergyAt u t)) := by

    dsimp only [h]

    exact
      one_add_abs_h3BKMLogarithmicGradientEnvelope_le
        hB
        hEOne

  have hTransportBKM :
      - velocityH3TransportDerivativeAt u t
        ≤
      4422
        *
      (
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t))
      )
        *
      velocityH3EnergyAt u t := by

    calc
      - velocityH3TransportDerivativeAt u t
          ≤
        4422
          * (1 + |h t|)
          * velocityH3EnergyAt u t :=
        hTransport

      _ ≤
        4422
          *
        (
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t))
        )
          *
        velocityH3EnergyAt u t := by

        exact
          mul_le_mul_of_nonneg_right
            (
              mul_le_mul_of_nonneg_left
                hEndpoint
                (by norm_num)
            )
            hENonneg

  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3
      hClassB
      ht

  have hDStrict :
      2 * velocityH3DissipationAt u t
        <
      - velocityH3TransportDerivativeAt u t := by
    linarith

  have hDTransport :
      2 * velocityH3DissipationAt u t
        <
      4422
        *
      (
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t))
      )
        *
      velocityH3EnergyAt u t :=
    lt_of_lt_of_le
      hDStrict
      hTransportBKM

  have hNormalized :
      2
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
        <
      4422
        *
      (
        (B + 1)
          * (1 + |g t|)
          * (1 + Real.log (velocityH3EnergyAt u t))
      ) := by

    have hDiv :=
      (div_lt_iff₀ hEPos).2
        hDTransport

    calc
      2
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
          =
        (
          2 * velocityH3DissipationAt u t
        )
          /
        velocityH3EnergyAt u t := by
        ring

      _ <
        4422
          *
        (
          (B + 1)
            * (1 + |g t|)
            * (1 + Real.log (velocityH3EnergyAt u t))
        ) :=
        hDiv

  dsimp only [B] at hNormalized

  simpa only [mul_assoc] using
    hNormalized

/-! ## Late-tail characteristic-frequency forcing -/

/--
Fix a strict anchor `b` and any vorticity envelope `g` on `(b,T)`.
Hypothetical nonextension forces, on a sufficiently late tail and at every
positive-growth time,

    2 Λ₃²
      <
    (4 + 3 E₀(b))
      * 4422
      * (B_b + 1)
      * (1 + |g|)
      * (1 + log E).

This is the direct bridge from the terminal frequency cascade to the BKM
vorticity-logarithm factor.
-/
theorem exists_terminalTail_positiveGrowth_characteristicFrequency_sq_lt_canonicalBKM_vorticityLogFactor_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {g : ℝ → ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T)
    (hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope
            u g s) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        0 < deriv (velocityH3EnergyAt u) t →
        2
            *
          h3TopCharacteristicFrequencyAt u t ^ 2
          <
        (
          4
            +
          3 * velocityH3Energy0At u b
        )
          *
        4422
          *
        (
          h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt
                (velocityH3Energy0At u b))
            +
          1
        )
          *
        (1 + |g t|)
          *
        (1 + Real.log (velocityH3EnergyAt u t)) := by

  let C : ℝ :=
    4
      +
    3 * velocityH3Energy0At u b

  have hE0Nonneg :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg
      u b

  have hCPos :
      0 < C := by
    dsimp only [C]
    linarith

  have hEnergyUpperEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3EnergyAt u t
          ≤
        C * velocityH3Energy3At u t := by

    dsimp only [C]

    exact
      eventually_velocityH3EnergyAt_le_anchorCoefficient_mul_energy3_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb

  obtain
    ⟨
      d,
      hdT,
      hdSubset
    ⟩ :=
    (
      mem_nhdsLT_iff_exists_Ioo_subset
    ).1
      hEnergyUpperEventually

  let c : ℝ :=
    (max d b + T) / 2

  have hMaxT :
      max d b < T :=
    max_lt
      hdT
      hb.2

  have hMaxC :
      max d b < c := by
    dsimp only [c]
    linarith

  have hcT :
      c < T := by
    dsimp only [c]
    linarith

  have hc :
      c ∈ Set.Ioo b T := by
    exact
      ⟨
        lt_of_le_of_lt
          (le_max_right d b)
          hMaxC,
        hcT
      ⟩

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht hDerivative

  have htD :
      t ∈ Set.Ioo d T :=
    ⟨
      lt_trans
        (
          lt_of_le_of_lt
            (le_max_left d b)
            hMaxC
        )
        ht.1,
      ht.2
    ⟩

  have htB :
      t ∈ Set.Ioo b T :=
    ⟨
      lt_trans hc.1 ht.1,
      ht.2
    ⟩

  have hEnergyUpper :
      velocityH3EnergyAt u t
        ≤
      C * velocityH3Energy3At u t :=
    hdSubset
      htD

  have hFrequencyRatio :
      h3TopCharacteristicFrequencyAt u t ^ 2
        ≤
      C
        *
      (
        velocityH3DissipationAt u t
          /
        velocityH3EnergyAt u t
      ) :=
    h3TopCharacteristicFrequencyAt_sq_le_coefficient_mul_dissipation_div_energy
      hCPos
      hEnergyUpper

  have hBKM :
      2
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
        <
      4422
        *
      (
        h3BKMCanonicalSelectedLogGradientConstant
            (Real.sqrt
              (velocityH3Energy0At u b))
          +
        1
      )
        *
      (1 + |g t|)
        *
      (1 + Real.log (velocityH3EnergyAt u t)) :=
    two_mul_dissipation_div_energy_lt_canonicalBKM_vorticityLogFactor_of_pos_deriv
      hH3
      hClass
      hb
      hg
      htB
      hDerivative

  have hFrequencyScaled :
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
        ≤
      C
        *
      (
        2
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
      ) := by

    calc
      2
          *
        h3TopCharacteristicFrequencyAt u t ^ 2
          ≤
        2
          *
        (
          C
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        ) :=
        mul_le_mul_of_nonneg_left
          hFrequencyRatio
          (by norm_num)

      _ =
        C
          *
        (
          2
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        ) := by
        ring

  have hBKMScaled :
      C
          *
        (
          2
            *
          (
            velocityH3DissipationAt u t
              /
            velocityH3EnergyAt u t
          )
        )
        <
      C
        *
      (
        4422
          *
        (
          h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt
                (velocityH3Energy0At u b))
            +
          1
        )
          *
        (1 + |g t|)
          *
        (1 + Real.log (velocityH3EnergyAt u t))
      ) :=
    mul_lt_mul_of_pos_left
      hBKM
      hCPos

  dsimp only [C] at hFrequencyScaled hBKMScaled

  calc
    2
        *
      h3TopCharacteristicFrequencyAt u t ^ 2
        ≤
      (
        4
          +
        3 * velocityH3Energy0At u b
      )
        *
      (
        2
          *
        (
          velocityH3DissipationAt u t
            /
          velocityH3EnergyAt u t
        )
      ) :=
      hFrequencyScaled

    _ <
      (
        4
          +
        3 * velocityH3Energy0At u b
      )
        *
      (
        4422
          *
        (
          h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt
                (velocityH3Energy0At u b))
            +
          1
        )
          *
        (1 + |g t|)
          *
        (1 + Real.log (velocityH3EnergyAt u t))
      ) :=
      hBKMScaled

    _ =
      (
        4
          +
        3 * velocityH3Energy0At u b
      )
        *
      4422
        *
      (
        h3BKMCanonicalSelectedLogGradientConstant
            (Real.sqrt
              (velocityH3Energy0At u b))
          +
        1
      )
        *
      (1 + |g t|)
        *
      (1 + Real.log (velocityH3EnergyAt u t)) := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
