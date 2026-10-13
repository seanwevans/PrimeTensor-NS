# Exact cyclic reindexing of the first-monomial integral

Base checkpoint: `dbe534c7` — physical Fourier sign and cyclic triad shell identity.

The repository already has an exact real-Schwartz physical aggregate-to-shell
identity, the seven-derivative Fourier multiplier, and the measurable
involution on pairs of frequencies

    F(p,r) = (p,-p-r).

This patch constructs the conjugate cyclic change

    G(p,r) = (-p-r,r),

and proves both preserve volume on the two-frequency product carrier. The
existing `h3TriadMiddleEquiv` is reused, rather than reproving its Haar/volume
properties. Consequently, for an incompressible Schwartz Fourier field `U`,

    ∫ [ S(p,r) + S(p,-p-r) + S(-p-r,r) ] dp dr
       = 3 ∫ S(p,r) dp dr,

where `S` is the already established signed complex shell kernel. The proof
provides absolute integrability of each transformed term.

The algebraic cyclic identity is generalized from `Fin 3` to an arbitrary finite
index type. This allows direct instantiation on `Axis Depth.three` without an
implicit coordinate-identification assumption. At each `(p,r)` the cyclic sum
is exactly the full six-permutation Fourier coefficient evaluated on the SAME
Schwartz polarization field at `p`, `q=-p-r`, and `r`.

Thus the six-order integral is **three times** the existing shell integral.
For a logged velocity having an actual real Schwartz realization at the time
of interest and satisfying the stated physical divergence identity, the
physical first-monomial aggregate obeys

    3 * firstMonomialAggregate = (2π)^7 * Im(∫ sixOrderKernel).

This is an exact signed equality. It does not prove that the sharp pointwise
low-normal example can be embedded into a real divergence-free Schwartz field
with an integrated lower bound; localization and cross-triad interactions
remain open. It does not establish a continuation theorem or a global
Navier–Stokes regularity claim.

## Local validation

The patch is authored against Lean 4.34.0-rc1 and the current mathlib API
already used in `FirstMonomialTriadIntegralBound.lean`. Compilation must be
performed on the project's pinned local toolchain; it was not available in
the artifact authoring container. The run script builds the new `.olean`
before the audit and runs the complete project build before pushing.
