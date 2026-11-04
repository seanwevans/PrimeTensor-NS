# Exact weighted Fourier bridge for the regularized real solenoidal Schwartz family

**Base HEAD:** `48311aa1` — prove regularized solenoidal Hermitian H3 diagonal density and real decoder convergence.

## Mathematical assertion

The earlier `FullThirdRegularizedHermitianTransverseRecovery` construction returns a genuine **real**, physically divergence-free Schwartz field `u_n` whose complex Fourier transform is exactly

\[
  \widehat{u_{n,j}}(\xi)
   = \chi(\xi)\frac{|\xi|^2}{|\xi|^2+\delta_n}U_j(\xi),
  \qquad \delta_n=(n+1)^{-1},
\]

when the smooth input `U` is pointwise Hermitian and transverse and the real cutoff `χ` is even. The new file promotes this to the **correct weighted H³ identity**

\[
 W_3(\xi)\widehat{u_{n,j}}(\xi)
 = \frac{|\xi|^2}{|\xi|^2+\delta_n}
       \bigl(W_3(\xi)U_j(\xi)\bigr)
\]

under the explicit support-flatness requirement `χ(ξ)=1` whenever `U_j(ξ)≠0`. In particular, for any **bundled** weighted spectral input `F_j` with representative `F_j(ξ)=W₃(ξ)U_j(ξ)` almost everywhere, it proves that the bundled `R_n F_j` has as its representative the exact weighted Fourier transform of the constructed real spatial Schwartz function.

The finite-coordinate theorem handles the native `Fin 3` spectral ordering via `h3AxisOfFin3`; no real-space/complex-space or axis/Fin indexing identification is postulated. For the very same real Schwartz fields it also retains exact pointwise physical divergence freedom and vanishing longitudinal six-symbol defect. A separate moving-family assembly theorem packages the already-proved uniform radial contraction with the new representative equality: provided each smooth compact input and cutoff has the stated properties, the resulting weighted spectral states converge strongly and Cauchy to the target and their real physical L² decoders converge as well.

## Explicit limitations

This patch **does not yet** show that an arbitrary weighted `L²` Leray-projected state is represented by a smooth compact `U`. This would be false before origin regularization. It also does not yet choose a compact even smooth cutoff equal to one on the support of a given smooth compact input. Those are obligations for the next density theorem.

The result is an exact bridge for inputs meeting those stated, checkable conditions. It deliberately avoids identifying an arbitrary `L²` equivalence class with a pointwise function or declaring a physical Schwartz field from an abstract Leray projection.

## Proof/validation

New module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdRegularizedPhysicalWeightedFourierBridge.lean`.

Register and audit all new definitions/theorems through `tools/audit/register_h3_full_third_regularized_physical_weighted_fourier_bridge.py`; rebuild the generated module index and compile the targeted module and full project. The package is structurally checked but not locally Lean-compiled.
