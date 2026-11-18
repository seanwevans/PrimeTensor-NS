# Exact Z³ longitudinal heat rigidity

**Commit parent:** `5d24a94410448965ade57e07c31680494d897552`
**Module:** `FullThirdSolenoidalKineticThreeBandZ3LongitudinalHeatRigidity`

## Mathematical content

The constructed infinite Z³ Fourier flow has a source represented by the absolutely
convergent ordered Leray convolution, and that source is transverse to its output
frequency (proved in the parent commit). The physical remaining issue is
propagation of the zero-divergence constraint through the flow.

Set \(\xi_n=\mathrm{frequency}(n)\) and \(w_n(t)=\langle\xi_n,g_n(t)\rangle_\mathbb C\).
Whenever the coefficientwise projected equation has a real-time derivative,

\[
\frac{d}{dt}g_n(t)=-\mu\|\xi_n\|^2g_n(t)+\mathcal{B}(g(t),g(t))_n,
\quad \langle\xi_n,\mathcal{B}(g,g)_n\rangle=0,
\]

applying the (real-restricted) complex-linear pairing gives the **exact scalar
longitudinal heat ODE**

\[
  w_n'(t)=-\mu\|\xi_n\|^2w_n(t).
\]

The generic scalar Grönwall lemma proves that if \(w_n(a)=0\), then \(w_n(t)=0\)
for every \(t\in[a,b]\), including the closed endpoints. The proof works for
\(\mu\ge0\), including zero viscosity, and requires no frequency-mode count
or constants depending on the Galerkin cutoff. The nonlinear term vanishes
identically in the longitudinal sector.

## What is proved

1. `scalarRigidity244`: zero-data homogeneous scalar heat uniqueness via mathlib Grönwall.
2. `scalarDerivative244`: exact inner-product chain rule for the infinite vector NS derivative.
3. `projectedDerivative244`: analytic mass bounds supply transverse nonlinear source and the heat derivative.
4. `solenoidalRigidity244`: any coefficientwise differentiable full Fourier NS path with the stated
   analytic bound preserves zero divergence from transverse initial coefficients.

## Remaining bridge, not smuggled into a hypothesis

`thirdFullThreeBand_z3PrescribedFourier_localExistence244` currently returns an
**integral** Fourier evolution, not an explicit `HasDerivAt` at every interior time.
The present theorem requires that coefficientwise derivative; it does not
claim the derivative was established in this package. The next proof step is
continuity of the independently identified infinite Leray source along the
constructed path, permitting fundamental-theorem-of-calculus differentiation
of its already-proved time integral. This would make the solenoidal conclusion
unconditional for the constructed projected-data solution.

Hermitian reality and physical-space transfer are separate obligations. Nothing
here proves global H³ continuation on ℝ³.
