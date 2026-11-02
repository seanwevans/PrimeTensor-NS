# Active finite-band endpoint Fourier cutoff escape

**Baseline**: `8326955e` — exclude persistent adaptive H³ endpoint scales with divergent cost.

This theorem advances beyond real-integral bookkeeping. The existing actual
low-band physical H³ dissipation estimate states that for any **fixed**
finite radius `ρ`, for all `t ∈ (b,T)`:

    lowRadialD3(ρ,t) ≤ ρ² * RadialWeightCeiling(ρ) * velocityH3Energy0At(u,b).

For the SAME original cofinal fivefold witnesses, each nonzero internal
endpoint interval has a positive finite-band capture at radius `N(k)+1`:

    R(k)² ε(k)² / 8 < lowRadialD3(N(k)+1, p(k)).

If the selected positive threshold `R(k)² ε(k)² / 8` tends to `+∞`, then:

    For each fixed M, eventually η(k)=0 OR M < N(k).

Thus an eventually bounded finite-band cutoff forces the endpoint
persistence branch to vanish eventually; if it remains active on a cofinal
subsequence, its selected finite-band cutoffs must leave every fixed band.

The proof crucially invokes **actual kinetic-energy anchored bounds** and
monotonicity of the physical low-radial dissipation across Fourier cutoffs.
It does not assume the full H³ dissipation is continuous, nor that its
terminal real integral is finite. The non-spectral, finite-band PDE-clock,
and anchor physical viscosity alternatives remain unchanged.

### Registered Lean declarations

- `h3Critical_scalar_activeCutoff_escape_of_divergingHeight`
- `h3Critical_physicalActiveFiniteBandCutoff_escape`
- `h3Critical_scalar_activeCutoff_eventuallyZero_of_boundedCutoffs`
- `h3Critical_noL2Trace_cofinalFivefold_activeEndpointCutoffEscape`

The new module imports the original synchronized endpoint gate as well as
the actual fixed-radius monotonicity and kinetic-anchor ceiling modules.
Compilation must be verified with the repository's pinned Lean 4 toolchain.
