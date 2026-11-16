import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalSharpPhysicalKineticCompensation
import Mathlib.Tactic

/-!
# Three-band counterexample to instantaneous Navier--Stokes transfer frustration

This is a finite Fourier-symbol test, not a terminal continuation theorem.
It uses the project's positive-depth `Tensor.Vector` and `Axis.fold` at the
established real/logarithmic semantic bridge. No additive operation is added
to the intrinsic prime-multiset carrier.

For wavevectors `a + b = c`, put the six nonzero Fourier coefficients at
`±a`, `±b`, `±c`, with `u_a = A`, `u_b = B`, `u_c = i C` and the negative
coefficients their complex conjugates. The real coefficients of the true
quadratic Navier--Stokes symbol at the three positive modes are

  S_a = -(C·b) B + (B·c) C,
  S_b = -(C·a) A + (A·c) C,
  S_c / i = -(A·b) B - (B·a) A.

Dotting these with the solenoidal amplitudes removes Leray pressure terms.
For the concrete six-mode state below the signed work is (-1,-1,+2).
Both outward fluxes at the consecutive cutoffs 3/2 and 3 are strictly
positive. Thus no universal *instantaneous* two-cutoff transfer-frustration
principle follows from the exact solenoidal Leray symbol alone.

This algebraic probe is periodic (a finite Fourier series), not a Schwartz
velocity on R^3. It does not assert persistence under PDE evolution, a
frequency-uniform flux bound, or any regularity conclusion.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev ThreeMode244 :=
  PrimeTensor.Tensor.Vector ℝ PrimeTensor.Depth.three

/-- Native rank-one, positive-three-axis tensor carrying real bridge values. -/
def thirdFullThreeBandVec244 (x y z : ℝ) : ThreeMode244 := by
  classical
  exact ⟨fun i =>
    if i = PrimeTensor.Bridge.Euclidean.xAxis then x
    else if i = PrimeTensor.Bridge.Euclidean.yAxis then y
    else z⟩

/-! Coordinate evaluation is proved once rather than repeatedly unfolding
   dependent index matches inside long rational expressions. -/
@[simp] private theorem thirdFullThreeBandVec_x244 (x y z : ℝ) :
    (thirdFullThreeBandVec244 x y z).component
      PrimeTensor.Bridge.Euclidean.xAxis = x := by
  classical
  change (if PrimeTensor.Bridge.Euclidean.xAxis =
      PrimeTensor.Bridge.Euclidean.xAxis then x else
      if PrimeTensor.Bridge.Euclidean.xAxis =
        PrimeTensor.Bridge.Euclidean.yAxis then y else z) = x
  exact if_pos rfl

@[simp] private theorem thirdFullThreeBandVec_y244 (x y z : ℝ) :
    (thirdFullThreeBandVec244 x y z).component
      PrimeTensor.Bridge.Euclidean.yAxis = y := by
  classical
  have hxy : PrimeTensor.Bridge.Euclidean.yAxis ≠
      PrimeTensor.Bridge.Euclidean.xAxis := by
    intro h
    cases h
  change (if PrimeTensor.Bridge.Euclidean.yAxis =
      PrimeTensor.Bridge.Euclidean.xAxis then x else
      if PrimeTensor.Bridge.Euclidean.yAxis =
        PrimeTensor.Bridge.Euclidean.yAxis then y else z) = y
  rw [if_neg hxy, if_pos rfl]

@[simp] private theorem thirdFullThreeBandVec_z244 (x y z : ℝ) :
    (thirdFullThreeBandVec244 x y z).component
      PrimeTensor.Bridge.Euclidean.zAxis = z := by
  classical
  have hzx : PrimeTensor.Bridge.Euclidean.zAxis ≠
      PrimeTensor.Bridge.Euclidean.xAxis := by
    intro h
    cases h
  have hzy : PrimeTensor.Bridge.Euclidean.zAxis ≠
      PrimeTensor.Bridge.Euclidean.yAxis := by
    intro h
    cases h
  change (if PrimeTensor.Bridge.Euclidean.zAxis =
      PrimeTensor.Bridge.Euclidean.xAxis then x else
      if PrimeTensor.Bridge.Euclidean.zAxis =
        PrimeTensor.Bridge.Euclidean.yAxis then y else z) = z
  rw [if_neg hzx, if_neg hzy]

/-- Ordinary dot product only in the established real semantic layer;
the index contraction remains the native nonempty axis fold. -/
def thirdFullThreeBandDot244 (v w : ThreeMode244) : ℝ :=
  PrimeTensor.Axis.fold (· + ·) PrimeTensor.Depth.three
    (fun i => v.component i * w.component i)

/-- Addition is local to the conventional Fourier bridge, never the native
prime-multiset tensor carrier. -/
def thirdFullThreeBandAdd244 (v w : ThreeMode244) : ThreeMode244 :=
  ⟨fun i => v.component i + w.component i⟩

theorem thirdFullThreeBand_dotAdd_right244
    (v w z : ThreeMode244) :
    thirdFullThreeBandDot244 v (thirdFullThreeBandAdd244 w z) =
      thirdFullThreeBandDot244 v w + thirdFullThreeBandDot244 v z := by
  simp only [thirdFullThreeBandDot244,
    PrimeTensor.Bridge.Euclidean.axis_fold_three]
  dsimp [thirdFullThreeBandAdd244]
  ring

/-- Scalar modal work of the true quadratic symbol at the low mode. -/
def thirdFullThreeBandWorkLow244
    (_a b c A B C : ThreeMode244) : ℝ :=
  -(thirdFullThreeBandDot244 C b) * thirdFullThreeBandDot244 A B +
    thirdFullThreeBandDot244 B c * thirdFullThreeBandDot244 A C

/-- Scalar modal work of the true quadratic symbol at the middle mode. -/
def thirdFullThreeBandWorkMid244
    (a _b c A B C : ThreeMode244) : ℝ :=
  -(thirdFullThreeBandDot244 C a) * thirdFullThreeBandDot244 A B +
    thirdFullThreeBandDot244 A c * thirdFullThreeBandDot244 B C

/-- Scalar modal work of the true quadratic symbol at the high mode. -/
def thirdFullThreeBandWorkHigh244
    (a b _c A B C : ThreeMode244) : ℝ :=
  -(thirdFullThreeBandDot244 A b) * thirdFullThreeBandDot244 B C -
    thirdFullThreeBandDot244 B a * thirdFullThreeBandDot244 A C

/-- Full signed cancellation, without taking absolute values or invoking an
unavailable high-order dissipation budget. -/
theorem thirdFullThreeBand_workConserves244
    (a b c A B C : ThreeMode244)
    (hClosure : c = thirdFullThreeBandAdd244 a b)
    (hA : thirdFullThreeBandDot244 A a = 0)
    (hB : thirdFullThreeBandDot244 B b = 0)
    (hC : thirdFullThreeBandDot244 C c = 0) :
    thirdFullThreeBandWorkLow244 a b c A B C +
      thirdFullThreeBandWorkMid244 a b c A B C +
      thirdFullThreeBandWorkHigh244 a b c A B C = 0 := by
  have hCsum :
      thirdFullThreeBandDot244 C a +
        thirdFullThreeBandDot244 C b = 0 := by
    rw [hClosure, thirdFullThreeBand_dotAdd_right244] at hC
    exact hC
  have hBsum :
      thirdFullThreeBandDot244 B c -
        thirdFullThreeBandDot244 B a = 0 := by
    rw [hClosure, thirdFullThreeBand_dotAdd_right244]
    rw [hB]
    ring
  have hAsum :
      thirdFullThreeBandDot244 A c -
        thirdFullThreeBandDot244 A b = 0 := by
    rw [hClosure, thirdFullThreeBand_dotAdd_right244]
    rw [hA]
    ring
  unfold thirdFullThreeBandWorkLow244 thirdFullThreeBandWorkMid244
    thirdFullThreeBandWorkHigh244
  calc
    _ = -(thirdFullThreeBandDot244 C a +
            thirdFullThreeBandDot244 C b) *
          thirdFullThreeBandDot244 A B +
        (thirdFullThreeBandDot244 B c -
            thirdFullThreeBandDot244 B a) *
          thirdFullThreeBandDot244 A C +
        (thirdFullThreeBandDot244 A c -
            thirdFullThreeBandDot244 A b) *
          thirdFullThreeBandDot244 B C := by ring
    _ = 0 := by rw [hCsum, hBsum, hAsum]; ring

/-- Explicit genuine radial Fourier modes. -/
def thirdFullThreeBandWaveLow244 : ThreeMode244 :=
  thirdFullThreeBandVec244 1 0 0

def thirdFullThreeBandWaveMid244 : ThreeMode244 :=
  thirdFullThreeBandVec244 2 1 0

def thirdFullThreeBandWaveHigh244 : ThreeMode244 :=
  thirdFullThreeBandAdd244
    thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveMid244

/-- Solenoidal amplitudes at `a` and `b`, and the real amplitude of `i C` at `c`. -/
def thirdFullThreeBandPolarLow244 : ThreeMode244 :=
  thirdFullThreeBandVec244 0 1 (-1)

def thirdFullThreeBandPolarMid244 : ThreeMode244 :=
  thirdFullThreeBandVec244 (-1) 2 1

def thirdFullThreeBandPolarHigh244 : ThreeMode244 :=
  thirdFullThreeBandVec244 0 0 (-1)

/-- The three amplitudes really are divergence-free at their respective modes. -/
theorem thirdFullThreeBand_exampleSolenoidal244 :
    thirdFullThreeBandDot244
        thirdFullThreeBandPolarLow244 thirdFullThreeBandWaveLow244 = 0 ∧
    thirdFullThreeBandDot244
        thirdFullThreeBandPolarMid244 thirdFullThreeBandWaveMid244 = 0 ∧
    thirdFullThreeBandDot244
        thirdFullThreeBandPolarHigh244 thirdFullThreeBandWaveHigh244 = 0 := by
  constructor
  · norm_num [thirdFullThreeBandDot244, thirdFullThreeBandPolarLow244,
      thirdFullThreeBandWaveLow244, PrimeTensor.Bridge.Euclidean.axis_fold_three]
  constructor
  · norm_num [thirdFullThreeBandDot244, thirdFullThreeBandPolarMid244,
      thirdFullThreeBandWaveMid244, PrimeTensor.Bridge.Euclidean.axis_fold_three]
  · norm_num [thirdFullThreeBandDot244, thirdFullThreeBandPolarHigh244,
      thirdFullThreeBandWaveHigh244, thirdFullThreeBandAdd244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- Exact nested squared-frequency separation for cutoffs N=3/2 and 2N=3. -/
theorem thirdFullThreeBand_exampleRadialOrdering244 :
    thirdFullThreeBandDot244
        thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveLow244 <
          ((3 : ℝ) / 2) ^ 2 ∧
    ((3 : ℝ) / 2) ^ 2 <
      thirdFullThreeBandDot244
        thirdFullThreeBandWaveMid244 thirdFullThreeBandWaveMid244 ∧
    thirdFullThreeBandDot244
        thirdFullThreeBandWaveMid244 thirdFullThreeBandWaveMid244 <
          (3 : ℝ) ^ 2 ∧
    (3 : ℝ) ^ 2 <
      thirdFullThreeBandDot244
        thirdFullThreeBandWaveHigh244 thirdFullThreeBandWaveHigh244 := by
  norm_num [thirdFullThreeBandDot244,
    thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
    thirdFullThreeBandWaveHigh244, thirdFullThreeBandAdd244,
    PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- Explicit low/middle losses and high-frequency gain from the exact signed
quadratic Fourier coefficients (before the Leray projection). -/
theorem thirdFullThreeBand_exampleSignedWork244 :
    thirdFullThreeBandWorkLow244
      thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveMid244
      thirdFullThreeBandWaveHigh244 thirdFullThreeBandPolarLow244
      thirdFullThreeBandPolarMid244 thirdFullThreeBandPolarHigh244 = -1 ∧
    thirdFullThreeBandWorkMid244
      thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveMid244
      thirdFullThreeBandWaveHigh244 thirdFullThreeBandPolarLow244
      thirdFullThreeBandPolarMid244 thirdFullThreeBandPolarHigh244 = -1 ∧
    thirdFullThreeBandWorkHigh244
      thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveMid244
      thirdFullThreeBandWaveHigh244 thirdFullThreeBandPolarLow244
      thirdFullThreeBandPolarMid244 thirdFullThreeBandPolarHigh244 = 2 := by
  constructor
  · norm_num [thirdFullThreeBandWorkLow244, thirdFullThreeBandDot244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandWaveHigh244, thirdFullThreeBandPolarLow244,
      thirdFullThreeBandPolarMid244, thirdFullThreeBandPolarHigh244,
      thirdFullThreeBandAdd244, PrimeTensor.Bridge.Euclidean.axis_fold_three]
  constructor
  · norm_num [thirdFullThreeBandWorkMid244, thirdFullThreeBandDot244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandWaveHigh244, thirdFullThreeBandPolarLow244,
      thirdFullThreeBandPolarMid244, thirdFullThreeBandPolarHigh244,
      thirdFullThreeBandAdd244, PrimeTensor.Bridge.Euclidean.axis_fold_three]
  · norm_num [thirdFullThreeBandWorkHigh244, thirdFullThreeBandDot244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandWaveHigh244, thirdFullThreeBandPolarLow244,
      thirdFullThreeBandPolarMid244, thirdFullThreeBandPolarHigh244,
      thirdFullThreeBandAdd244, PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- The exact Euclidean Leray symbol at a nonzero Fourier mode. The
construction uses only the conventional real bridge, not native addition. -/
def thirdFullThreeBandLeray244 (k F : ThreeMode244) : ThreeMode244 :=
  ⟨fun i => F.component i -
    (thirdFullThreeBandDot244 k F / thirdFullThreeBandDot244 k k) *
      k.component i⟩

/-- The real Fourier coefficient at the low positive mode, after using the
Hermitian pair at `-b`. -/
def thirdFullThreeBandSourceLow244
    (_a b c _A B C : ThreeMode244) : ThreeMode244 :=
  ⟨fun i =>
    -(thirdFullThreeBandDot244 C b) * B.component i +
      (thirdFullThreeBandDot244 B c) * C.component i⟩

/-- The real Fourier coefficient at the middle positive mode. -/
def thirdFullThreeBandSourceMid244
    (a _b c A _B C : ThreeMode244) : ThreeMode244 :=
  ⟨fun i =>
    -(thirdFullThreeBandDot244 C a) * A.component i +
      (thirdFullThreeBandDot244 A c) * C.component i⟩

/-- `i`-coefficient at the high positive mode, with the Fourier `-i` included. -/
def thirdFullThreeBandSourceHigh244
    (a b _c A B _C : ThreeMode244) : ThreeMode244 :=
  ⟨fun i =>
    -(thirdFullThreeBandDot244 A b) * B.component i -
      (thirdFullThreeBandDot244 B a) * A.component i⟩

/-- The actual Leray-projected modal works; pressure has not been silently
dropped from the source, only projected out by the true Fourier symbol. -/
def thirdFullThreeBandProjectedLow244 : ℝ :=
  thirdFullThreeBandDot244 thirdFullThreeBandPolarLow244
    (thirdFullThreeBandLeray244 thirdFullThreeBandWaveLow244
      (thirdFullThreeBandSourceLow244
        thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveMid244
        thirdFullThreeBandWaveHigh244 thirdFullThreeBandPolarLow244
        thirdFullThreeBandPolarMid244 thirdFullThreeBandPolarHigh244))

def thirdFullThreeBandProjectedMid244 : ℝ :=
  thirdFullThreeBandDot244 thirdFullThreeBandPolarMid244
    (thirdFullThreeBandLeray244 thirdFullThreeBandWaveMid244
      (thirdFullThreeBandSourceMid244
        thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveMid244
        thirdFullThreeBandWaveHigh244 thirdFullThreeBandPolarLow244
        thirdFullThreeBandPolarMid244 thirdFullThreeBandPolarHigh244))

def thirdFullThreeBandProjectedHigh244 : ℝ :=
  thirdFullThreeBandDot244 thirdFullThreeBandPolarHigh244
    (thirdFullThreeBandLeray244 thirdFullThreeBandWaveHigh244
      (thirdFullThreeBandSourceHigh244
        thirdFullThreeBandWaveLow244 thirdFullThreeBandWaveMid244
        thirdFullThreeBandWaveHigh244 thirdFullThreeBandPolarLow244
        thirdFullThreeBandPolarMid244 thirdFullThreeBandPolarHigh244))

/-- Direct verification of the true quadratic Leray symbol at all three
modes. This is stronger than an unprojected trilinear sign check. -/
theorem thirdFullThreeBand_exampleProjectedWork244 :
    thirdFullThreeBandProjectedLow244 = -1 ∧
    thirdFullThreeBandProjectedMid244 = -1 ∧
    thirdFullThreeBandProjectedHigh244 = 2 := by
  constructor
  · norm_num [thirdFullThreeBandProjectedLow244,
      thirdFullThreeBandDot244, thirdFullThreeBandLeray244,
      thirdFullThreeBandSourceLow244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandWaveHigh244, thirdFullThreeBandPolarLow244,
      thirdFullThreeBandPolarMid244, thirdFullThreeBandPolarHigh244,
      thirdFullThreeBandAdd244, PrimeTensor.Bridge.Euclidean.axis_fold_three]
  constructor
  · norm_num [thirdFullThreeBandProjectedMid244,
      thirdFullThreeBandDot244, thirdFullThreeBandLeray244,
      thirdFullThreeBandSourceMid244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandWaveHigh244, thirdFullThreeBandPolarLow244,
      thirdFullThreeBandPolarMid244, thirdFullThreeBandPolarHigh244,
      thirdFullThreeBandAdd244, PrimeTensor.Bridge.Euclidean.axis_fold_three]
  · norm_num [thirdFullThreeBandProjectedHigh244,
      thirdFullThreeBandDot244, thirdFullThreeBandLeray244,
      thirdFullThreeBandSourceHigh244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandWaveHigh244, thirdFullThreeBandPolarLow244,
      thirdFullThreeBandPolarMid244, thirdFullThreeBandPolarHigh244,
      thirdFullThreeBandAdd244, PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- Both consecutive outward kinetic fluxes are strictly positive.
This refutes a universal instantaneous sign-frustration conjecture, not a
possible *temporal* dynamical constraint on unforced solutions. -/
theorem thirdFullThreeBand_bothOutwardFluxesPositive244 :
    0 < -thirdFullThreeBandProjectedLow244 ∧
    0 < thirdFullThreeBandProjectedHigh244 := by
  obtain ⟨hLow, _, hHigh⟩ :=
    thirdFullThreeBand_exampleProjectedWork244
  rw [hLow, hHigh]
  norm_num

end
end PrimeTensor.FirstMonomialTriad
