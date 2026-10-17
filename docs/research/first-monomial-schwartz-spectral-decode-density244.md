# Spectral Schwartz density through the genuine inverse Fourier L² decoder

Baseline: `dabaa5a4` (2026-10-17).

The previous three-component spectral density result constructed Schwartz
representatives in the *weighted spectral* Hilbert space. This patch
transports the **same representatives** through PrimeTensor's actual
weight-stripping operator and the unitary complex inverse Fourier transform.

The exact componentwise estimate is

    ‖decode(F) − decode(G)‖_{L²} ≤ ‖F − G‖_{weighted H³}.

Consequently an arbitrary weighted H³ spectral velocity `U` admits a
Schwartz-vector sequence `Φₙ` for which its weighted spectral realization,
raw Fourier L² deweighting, and decoded complex physical L² velocity all
converge to their respective interpretations of `U`. The physical L²
velocity sequence is Cauchy, too.

This is a stronger approximation bridge, but *not* physical H³ Schwartz
density. The weighted spectral Schwartz representatives have not been
shown to correspond to real-valued, divergence-free **physical** Schwartz
velocity functions. The derivative energy E₂/E₃ transfer, preservation of
reality/solenoidality, and the signed first-monomial identification remain.
