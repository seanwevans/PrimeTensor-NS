import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalFiniteCoreExclusion
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialH3Criterion

/-!
# Reduce physical vorticity endpoint regularity to strong H³ endpoint control

The pure physical terminal obstruction now has no surviving spatial branch once
one fixed actual-vorticity component has

* a selected endpoint temporal modulus; and
* selected spatial equicontinuity.

Those two properties need not be introduced independently.

Each actual vorticity component is exactly the difference of two constituent
first velocity derivatives.  For example,

    ωₓ = ∂y u_z - ∂z u_y.

Both constituent derivatives are already represented by the complementary
gradient fields attached to two structural curl-gradient pairs.  The existing
strong spectral H³ endpoint criterion supplies, for each such complementary
field,

* the selected endpoint temporal modulus; and
* selected spatial equicontinuity.

Applying that criterion to the two constituent fields and using the triangle
inequality transfers both properties to the physical vorticity component.

Thus the physical endpoint package is reduced to the same pair-specific strong
H³ endpoint language used by the earlier terminal residual development.  The
last theorem threads this directly into the physical spatial-geometry
contradiction.

No claim is made here that the required strong H³ endpoint convergence follows
from the current preterminal hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalMinimalVorticityPhysicalStrongH3Endpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The two complementary-gradient fields forming each vorticity component -/

/--
The positive constituent in the standard coordinate formula for a fixed
physical vorticity component.
-/
def h3TerminalActualVorticityPositiveComplementPair
    (i : Fin 3) :
    H3TerminalCurlGradientPair :=
  if i = 0 then
    .x_zy
  else if i = 1 then
    .y_xz
  else
    .z_yx

/--
The negative constituent in the standard coordinate formula for a fixed
physical vorticity component.
-/
def h3TerminalActualVorticityNegativeComplementPair
    (i : Fin 3) :
    H3TerminalCurlGradientPair :=
  if i = 0 then
    .x_yz
  else if i = 1 then
    .y_zx
  else
    .z_xy

/--
Every fixed actual-vorticity component is the difference of its two
complementary-gradient constituent fields.
-/
theorem h3NativeActualVorticityComponentAt_eq_complement_sub
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 3)
    (t : ℝ)
    (x : Point3) :
    h3NativeActualVorticityComponentAt
        u i t x
      =
    h3TerminalComplementGradientFieldForPair
        u
        (h3TerminalActualVorticityPositiveComplementPair i)
        t x
      -
    h3TerminalComplementGradientFieldForPair
        u
        (h3TerminalActualVorticityNegativeComplementPair i)
        t x := by

  fin_cases i <;>
    simp [
      h3NativeActualVorticityComponentAt,
      h3TerminalActualVorticityPositiveComplementPair,
      h3TerminalActualVorticityNegativeComplementPair,
      h3TerminalComplementGradientFieldForPair,
      h3TerminalComplementDerivativeAxisForPair,
      h3TerminalComplementComponentAxisForPair,
      realVorticityX,
      realVorticityY,
      realVorticityZ
    ]

/-! ## Pair-specific strong H³ endpoint package for physical vorticity -/

/--
Strong H³ endpoint control for the two constituent velocity components whose
first derivatives form one fixed physical vorticity component.
-/
def H3TerminalActualVorticitySelectedStrongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (i : Fin 3) : Prop :=
  H3TerminalComplementGradientSelectedStrongH3Endpoint
      hH3
      hTauStrict
      (h3TerminalActualVorticityPositiveComplementPair i)
    ∧
  H3TerminalComplementGradientSelectedStrongH3Endpoint
      hH3
      hTauStrict
      (h3TerminalActualVorticityNegativeComplementPair i)

/-! ## A real subtraction is Lipschitz in both arguments -/

/--
For real scalars, subtracting two pairs costs at most the sum of the two input
distances.
-/
private theorem dist_sub_sub_le_add_dist
    (a b c d : ℝ) :
    dist
        (a - b)
        (c - d)
      ≤
    dist a c + dist b d := by

  simp only [Real.dist_eq]

  calc
    |(a - b) - (c - d)|
        =
      |(a - c) - (b - d)| := by
        congr 1
        ring
    _ ≤
      |a - c| + |b - d| :=
        abs_sub _ _

/-! ## Strong H³ endpoint control gives the physical endpoint temporal modulus -/

/--
Strong H³ endpoint control for the two constituent fields implies uniform
selected endpoint temporal control for their physical vorticity difference.
-/
theorem actualVorticitySelectedEndpointTemporalModulus_of_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    {z : ℕ → Point3}
    {i : Fin 3}
    (hStrong :
      H3TerminalActualVorticitySelectedStrongH3Endpoint
        hH3 hTauStrict i) :
    H3TerminalActualVorticitySelectedEndpointTemporalModulus
      u i τ z T := by

  let pPos : H3TerminalCurlGradientPair :=
    h3TerminalActualVorticityPositiveComplementPair i

  let pNeg : H3TerminalCurlGradientPair :=
    h3TerminalActualVorticityNegativeComplementPair i

  have hPositive :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u pPos τ z T :=
    selectedEndpointTemporalModulus_of_strongH3Endpoint
      hH3
      hTauStrict
      (p := pPos)
      hStrong.1

  have hNegative :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u pNeg τ z T :=
    selectedEndpointTemporalModulus_of_strongH3Endpoint
      hH3
      hTauStrict
      (p := pNeg)
      hStrong.2

  intro ε hε

  have hHalfPos :
      0 < ε / 2 := by
    linarith

  obtain
    ⟨
      ηPos,
      hηPos,
      hPos
    ⟩ :=
    hPositive
      (ε / 2)
      hHalfPos

  obtain
    ⟨
      ηNeg,
      hηNeg,
      hNeg
    ⟩ :=
    hNegative
      (ε / 2)
      hHalfPos

  refine
    ⟨
      min ηPos ηNeg,
      lt_min hηPos hηNeg,
      ?_
    ⟩

  intro r n hTime

  have hTimePos :
      dist (τ n) T < ηPos :=
    lt_of_lt_of_le
      hTime
      (min_le_left ηPos ηNeg)

  have hTimeNeg :
      dist (τ n) T < ηNeg :=
    lt_of_lt_of_le
      hTime
      (min_le_right ηPos ηNeg)

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pPos
      (τ n)
      (z r)

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pNeg
      (τ n)
      (z r)

  let C : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pPos
      T
      (z r)

  let D : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pNeg
      T
      (z r)

  have hAC :
      dist A C < ε / 2 := by

    dsimp only [A, C, pPos]

    exact
      hPos
        r
        n
        hTimePos

  have hBD :
      dist B D < ε / 2 := by

    dsimp only [B, D, pNeg]

    exact
      hNeg
        r
        n
        hTimeNeg

  have hDifference :
      dist
          (A - B)
          (C - D)
        ≤
      dist A C + dist B D :=
    dist_sub_sub_le_add_dist
      A B C D

  rw [
    h3NativeActualVorticityComponentAt_eq_complement_sub,
    h3NativeActualVorticityComponentAt_eq_complement_sub
  ]

  change
    dist
        (A - B)
        (C - D)
      < ε

  exact
    lt_of_le_of_lt
      hDifference
      (by linarith)

/-! ## Strong H³ endpoint control gives physical spatial equicontinuity -/

/--
Strong H³ endpoint control for the two constituent fields implies one selected
spatial modulus for their physical vorticity difference over the entire
selected time family.
-/
theorem actualVorticitySelectedSpatialEquicontinuity_of_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    {z : ℕ → Point3}
    {i : Fin 3}
    (hStrong :
      H3TerminalActualVorticitySelectedStrongH3Endpoint
        hH3 hTauStrict i) :
    H3TerminalActualVorticitySelectedSpatialEquicontinuity
      u i τ z := by

  let pPos : H3TerminalCurlGradientPair :=
    h3TerminalActualVorticityPositiveComplementPair i

  let pNeg : H3TerminalCurlGradientPair :=
    h3TerminalActualVorticityNegativeComplementPair i

  have hPositive :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u pPos τ z :=
    selectedSpatialEquicontinuity_of_strongH3Endpoint
      hH3
      hTauStrict
      hTau
      (p := pPos)
      hStrong.1

  have hNegative :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u pNeg τ z :=
    selectedSpatialEquicontinuity_of_strongH3Endpoint
      hH3
      hTauStrict
      hTau
      (p := pNeg)
      hStrong.2

  intro ε hε

  have hHalfPos :
      0 < ε / 2 := by
    linarith

  obtain
    ⟨
      ρPos,
      hρPos,
      hPos
    ⟩ :=
    hPositive
      (ε / 2)
      hHalfPos

  obtain
    ⟨
      ρNeg,
      hρNeg,
      hNeg
    ⟩ :=
    hNegative
      (ε / 2)
      hHalfPos

  refine
    ⟨
      min ρPos ρNeg,
      lt_min hρPos hρNeg,
      ?_
    ⟩

  intro r m n hSpace

  have hSpacePos :
      dist (z m) (z n) < ρPos :=
    lt_of_lt_of_le
      hSpace
      (min_le_left ρPos ρNeg)

  have hSpaceNeg :
      dist (z m) (z n) < ρNeg :=
    lt_of_lt_of_le
      hSpace
      (min_le_right ρPos ρNeg)

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pPos
      (τ r)
      (z m)

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pNeg
      (τ r)
      (z m)

  let C : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pPos
      (τ r)
      (z n)

  let D : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u pNeg
      (τ r)
      (z n)

  have hAC :
      dist A C < ε / 2 := by

    dsimp only [A, C, pPos]

    exact
      hPos
        r
        m
        n
        hSpacePos

  have hBD :
      dist B D < ε / 2 := by

    dsimp only [B, D, pNeg]

    exact
      hNeg
        r
        m
        n
        hSpaceNeg

  have hDifference :
      dist
          (A - B)
          (C - D)
        ≤
      dist A C + dist B D :=
    dist_sub_sub_le_add_dist
      A B C D

  rw [
    h3NativeActualVorticityComponentAt_eq_complement_sub,
    h3NativeActualVorticityComponentAt_eq_complement_sub
  ]

  change
    dist
        (A - B)
        (C - D)
      < ε

  exact
    lt_of_le_of_lt
      hDifference
      (by linarith)

/-! ## The full physical endpoint package follows from two strong H³ endpoints -/

/--
Pair-specific strong H³ endpoint control for the two constituent fields
supplies the complete physical endpoint regularity package.
-/
theorem actualVorticitySelectedEndpointRegularity_of_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    {z : ℕ → Point3}
    {i : Fin 3}
    (hStrong :
      H3TerminalActualVorticitySelectedStrongH3Endpoint
        hH3 hTauStrict i) :
    H3TerminalActualVorticitySelectedEndpointRegularity
      u i τ z T := by

  exact
    ⟨
      actualVorticitySelectedEndpointTemporalModulus_of_strongH3Endpoint
        hH3
        hTauStrict
        hStrong,
      actualVorticitySelectedSpatialEquicontinuity_of_strongH3Endpoint
        hH3
        hTauStrict
        hTau
        hStrong
    ⟩

/-! ## Strong H³ endpoint control eliminates the physical spatial geometry -/

/--
Once the two constituent fields have strong H³ endpoint control, the physical
finite-cluster versus spatial-infinity alternative is impossible for a
sequence carrying the oriented linear actual-vorticity lower bound.
-/
theorem terminal_minimalVorticityPhysical_spatialGeometry_impossible_of_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    {i : Fin 3}
    {s : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {z : ℕ → Point3}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hOrientedLower :
      ∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt
              u i (τ n) (z n)))
    (hGeometry :
      H3TerminalSelectedPointHasFiniteCluster z
        ∨
      H3TerminalSelectedPointEscapesToInfinity z)
    (hStrong :
      H3TerminalActualVorticitySelectedStrongH3Endpoint
        hH3 hTauStrict i) :
    False := by

  have hRegularity :
      H3TerminalActualVorticitySelectedEndpointRegularity
        u i τ z T :=
    actualVorticitySelectedEndpointRegularity_of_strongH3Endpoint
      hH3
      hTauStrict
      hTau
      hStrong

  exact
    terminal_minimalVorticityPhysical_spatialGeometry_impossible_of_endpointRegularity
      hH3
      hTauStrict
      hTau
      hOrientedLower
      hGeometry
      hRegularity

end

end Euclidean
end Bridge
end PrimeTensor
