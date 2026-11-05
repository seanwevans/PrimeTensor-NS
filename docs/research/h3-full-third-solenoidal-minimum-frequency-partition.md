# Solenoidal H³: complete minimum-frequency partition

Parent commit: `b00871e6698940ddeeb7350c6817f13a02fc459b`.

The project now has three distinct solenoidal estimates for the genuine
complex Fourier sixth-power flux. The first/middle/last minima are selected
with a deterministic lexicographic tie rule. On the Fourier pair
`z=(p,r)` with `q=-(p+r)`:

1. `Sₚ = { |p| ≤ |q| and |p| ≤ |r| }`
2. `S_q = { |q| < |p| and |q| ≤ |r| }`
3. `Sᵣ = { |r| < |p| and |r| < |q| }`

All are measurable. The sets are mutually disjoint, including on frequency
ties, and their union is the complete Fourier pair space. The full flux
integral is exactly the sum over these regions, using the set-integral union
theorem twice and Schwartz flux integrability; no null-set boundary shortcut.

On each sector, the smallest frequency pays the first radial moment, while
the other two pay three derivatives each. Each contribution is bounded by
`72 M₆ M₁`, with `M₆ = ∫ |ξ|⁶ F(ξ)²` and `M₁ = ∫ |ξ| F(ξ)`. The exact sum gives

    ‖∫ F₆‖ ≤ 216 M₆ M₁.

For a real solenoidal Schwartz recovery represented by actual weighted H³
states with coordinate norm ceiling `K`, use `M₆ ≤ 3K²` and
`M₁ ≤ 3 C₁ K` to obtain

    ‖∫ F₆‖ ≤ 1944 C₁ K³.

The same physical recovery sequence used for the signed third-order
transport limit supports this bound at fixed interior physical time.

## Scope and next mathematical question

This is a useful **frequency-resolved decomposition**, not a sharper global
scalar estimate. The earlier global raw Fourier mass estimate `27 C₁ K³`
is numerically stronger when one merely asks for an unsigned global ceiling.
The partition is valuable because it assigns *which* frequency is low,
allowing future refinements by low-frequency concentration, spectral transfer,
and temporal profiles without mixing orientations.

A fixed-snapshot cubic ceiling is not a dissipative absorption or a
uniform-in-time continuation estimate. The next nontrivial gate is a
frequency-weighted smallness, sign, or disjoint temporal charge mechanism
that survives approach to the terminal time. Do not claim this partition
closes that gate.

## Verification

The ZIP registrar inserts exactly one import in `PrimeTensor.lean` and the
audit module, plus 18 `#check` and 18 `#print axioms` entries. Run
`proof/generate_index.py` before the Lean/build checks. No `.sh` file is
included. Local static validation is not equivalent to Lean compilation.
