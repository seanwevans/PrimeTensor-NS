# Exact real-solenoidal kinetic exclusion of global anti-heat alignment

Pinned HEAD: `23b953ac6bb0ae2d06641814354a3e4087ecd518`.

## Structural finding

The accepted scalar Young-gap saturation is `f=-2q z`. The actual physical
Navier--Stokes Fourier equation is `R=-q z-f`; hence such saturation *across
all frequencies* would align the momentum derivative with `+q z`. This is
anti-diffusive and differs fundamentally from a generic complex Fourier
coordinate, where the sharp constant 2 is attainable.

Instead of assuming an unproved global Fourier orthogonality lemma, reuse
the accepted **actual physical Hilbert kinetic identity**:

    inner_R(U,R) = -D0,     norm(U)^2 = E0.

For any nonnegative scalar lambda at any strict physical time, the real
Hilbert norm expansion yields an **exact** identity:

    norm(R-lambda U)^2 = norm(R)^2 + lambda^2 E0 + 2 lambda D0.

It follows that

    lambda^2 E0 + 2 lambda D0 <= norm(R-lambda U)^2.

On an H3 physical path with terminal kinetic energy infimum L, the
already-proved monotonicity of E0 gives the uniform-in-time lower bound

    lambda^2 L <= norm(R-lambda U)^2.

In the positive-terminal-kinetic branch, any fixed `lambda>0` excludes
`R=lambda U` at every strict tail time. This is an actual non-conditional
kinetic PDE restriction, unlike the arbitrary complex-mode sharpness test.

## What remains unproved

The Fourier Young-gap saturation condition involves **frequency-dependent**
`q(xi)` and may occur only on a moving highpass annulus. The global Hilbert
anti-heat theorem tests only a *fixed scalar* lambda and the **whole** old
physical source. Kinetic cancellations may be transferred between low and
high frequencies, so the theorem must not be used to assert a highpass gap
or terminal H3 regularity.

The additional two-error theorem shows for ANY physical Hilbert vector A:

    lambda^2 E0 + 2 lambda D0
      <= [ norm(A-R) + norm(A-lambda U) ]^2.

For a future choice A=qU on a shell, the first term would become the
anti-heat/Young-gap mismatch, while the second would measure the multiplier
variation across the shell. There is **no** currently proved identification
of either of these terms with a frequency-restricted physical Hilbert state.

The next hard mathematical step is a frequency-localized comparison between
`R` and the positive multiplier `q U`, tracking both cutoff transition and
signed low-frequency kinetic pairing. Without such an estimate, the positive
terminal kinetic floor does not prohibit highpass near-saturation.

## Kernel-audited declarations

- `thirdFullKinetic_antiHeatResidual_exactSquare244`
- `thirdFullKinetic_antiHeatResidual_lowerSquare244`
- `thirdFullPhysical_antiHeatKinetic_exactSquare244`
- `thirdFullPhysical_antiHeatKinetic_coercivity244`
- `thirdFullPhysical_antiHeatKinetic_terminalFloor244`
- `thirdFullPhysical_antiHeatKinetic_noAlignment244`
- `thirdFullPhysical_antiHeatKinetic_twoErrorGate244`

No `sorry`, `admit`, axioms, or extra physical regularity assumptions are
introduced. Actual Lean elaboration must be checked in the pinned toolchain.
