# Actual highpass frozen diffusion is dissipative

Base commit: `98c6d6c10` (`isolate frozen selected outer diffusion work and temporal commutator`).

## New analytic result

The previous actual two-stage source ledger is

\[
M_x-M_s=2\tau d_\rho(x)-2\langle H_x,C_\rho\rangle-\|A_D\|_2^2
   +2\langle H_x+A_D,A_N\rangle-\|A_N\|_2^2,
\]
where \(H_x=P_{\ge\rho}u(x)\), \(d_\rho(x)=-\langle H_x,P_{\ge\rho}\Delta u(x)\rangle\), \(A_D=P_{\ge\rho}\int_x^s\Delta u\), \(A_N=P_{\ge\rho}\int_x^s\mathcal N(u)\), \(\tau=s-x\) and \(C_\rho=A_D-\tau P_{\ge\rho}\Delta u(x)\).

The new proof establishes, for every positive physical time and every real cutoff:

\[
\langle P_{\ge\rho}u(x),P_{\ge\rho}\Delta u(x)\rangle_{L^2}
= -\sum_{j=1}^{3}\int_{|\xi|\ge\rho}
  (2\pi)^2|\xi|^2\,|\widehat{u_j}(x,\xi)|^2\,d\xi\le 0.
\]

The equality is the underlying Plancherel computation; the Lean module proves its inequality consequence. No heat-flow identity is asserted for the time-integrated Laplacian.

## Proof chain

1. The actual sharp highpass is exactly the complementary radial indicator on the complex Fourier `L²` carrier.
2. The quotient-safe raw Fourier Laplacian has representative \(-q(\xi)\widehat u(\xi)\), with \(q=(2\pi)^2|\xi|^2\ge0\). The localized complex inner product therefore has nonpositive real part.
3. Scalar physical Plancherel converts the localized Fourier inequality into a physical real `L²` pairing bound.
4. The actual positive-time velocity is the real decoder of the actual spectral snapshot. Raw Hermitian symmetry implies its precise Fourier realizability. The actual physical Laplacian decoder has the corresponding Fourier Laplacian representative.
5. Coordinatewise nonpositivity yields the three-component actual physical highpass sign; the frozen source-work scalar \(d_\rho(x)\) is nonnegative.
6. The previously established exact physical three-way forced-drain alternative is re-exported with that genuine sign included.

## What remains open

This is an analytic improvement over the formerly *signed* frozen-diffusion term. It does **not** control the temporal commutator \(C_\rho\), produce cutoff-uniform bounds for the Leray transfer, or force terminal continuation. In particular, \(A_D\) is not the autonomous heat evolution of \(H_x\). A genuinely new temporal spectral estimate or triad cancellation is still required.

## Audit

The registration script adds only the new module import and `#check` / `#print axioms` declarations. There are no new `axiom`, `sorry`, or `admit` declarations. The module requires local Lean 4/mathlib compilation; archive and structural checks are not a substitute.
