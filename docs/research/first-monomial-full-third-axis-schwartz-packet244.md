# Full-third actual Hermitian Schwartz Fourier packet on the positive-depth axis carrier

Base commit: `d3dca3fd` — prove strict full third windowed Hermitian local integral.

The preceding theorem proves a negative six-dimensional integral of ONE selected
labelled three-window coefficient. It does not define a global Fourier field,
so the natural next step is a fully assembled three-mode packet and its
conjugate-reflected counterpart.

`FirstMonomialTriadLowQuarterPoint3FullThirdAxisSchwartzPacket244.lean`
constructs this field on the **actual** `Axis Depth.three → ℝ` carrier.
It uses the smooth compact window at each of centers 0, 1, 2, multiplies by
its corresponding normalized polynomial transverse germ, and gives the three
complex polarization factors phases `1`, `1`, `Complex.I`. The product of
these phases at the positive sharp triad is therefore `Complex.I`, the phase
required for the previously audited signed Hermitian orbit. Conjugate
reflection supplies the opposite-frequency packets.

The main proof obligations and deliverables are:

- Exact pointwise complex divergence of each localized packet and their sum.
- Smoothness of the quadratic polynomial transverse germ on the physical axis carrier.
- Compact support and infinite smoothness of each complex vector packet.
- Conjugate-reflection reality and preservation of pointwise complex divergence.
- Packaging the entire six-packet field as a vector-valued `SchwartzMap`.
- Exact pointwise divergence and Hermitian reality of the packaged Schwartz map.

**Not yet proved:** the Fourier transform/inverse Fourier transform bridge from
this axis-carrier Schwartz map to the project's `H3FourierPoint3` real physical
velocity; the identification of its full third-order gradient/interpolation
integral with the labelled Hermitian polynomial; the sign of the SUM over all
coherent sectors. In particular, this patch does not infer nonzero full
transport, failure of an a priori estimate, or Navier–Stokes continuation.

## Verification

Run the included idempotent registration script; regenerate `proof/order.txt`
with `python3 proof/generate_index.py`, check freshness with `--check`, validate
prose fragments, compile the new module, inspect the axiom audit, and perform a
full `lake build` before committing. The preparation container does not
provide the repository's pinned Lean toolchain/mathlib; this code needs the
checkout's Lean compilation as its proof-verification gate.
