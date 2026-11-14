# Selected outer sharp highpass: automatic real-linear projector and signed Leray alignment

Base: `0f5da4a06`. New module: `FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierSharpHighpassCLM`.

## Mathematical contribution

The physical sharp Fourier cutoff was known to be a norm contraction and orthogonal to its complementary band. The previous cutoff-uniform temporal Laplacian commutator theorem still took an explicit continuous real-linear realization certificate. This module constructs that map from existing scalar Fourier Plancherel injectivity, Fourier multiplier linearity, and the componentwise `PiLp` realization.

For every real cutoff `rho`, the actual map

\[
Q_\rho V=V-P_{<\rho}V
\]

is a real continuous-linear map of norm at most one on the three-component physical `L²` Hilbert space. The statement is genuine, not an abstract proxy, and removes the remaining interface hypothesis in the previous theorem.

At each fixed `x in (0,T)` and for each `eta>0`, there is a `delta>0` independent of **rho** such that for `x<=s`, `s-x<delta`, `s<T`,

\[
\left\|Q_\rho \int_x^s \Delta u(t)\,dt-(s-x)Q_\rho\Delta u(x)\right\|_2\le (s-x)\eta.
\]

The exact signed energy ledger with both quadratic increments now therefore gives, for the selected positive highpass mass-loss forcing `epsilon<K(M_x-M_s)`,

\[
\epsilon -K[2\tau d_\rho(x)+2\|H\|\tau\eta]
+K(\|A\|^2+\|B\|^2)<2K\langle H+A,B\rangle.
\]

A further geometric deduction is available when the frozen diffusion and commutator are insufficient to pay `epsilon`:

\[
\|A-B\|^2<2\langle H,B\rangle.
\]

Thus the nonlinear Leray forcing must align **positively with the original selected highpass carrier**, not merely the intermediate viscous state. Its signed pairing must exceed half the square of the full net highpass displacement. This uses the exact Hilbert identity `||A-B||² = ||A||²+||B||²-2<A,B>` and does not discard either negative quadratic term.

## Scope

The cutoff-independent `delta` is local at one fixed positive time `x`. Nothing here bounds `delta` from below uniformly as `x` approaches the terminal time; such uniformity cannot be inferred from interior continuity. No new PDE axioms, compactness hypotheses, or continuation claims are introduced. Lean compilation must be checked with the user's project toolchain.
