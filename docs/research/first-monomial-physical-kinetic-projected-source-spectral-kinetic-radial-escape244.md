# Exact physical kinetic anchor controls fixed radial weighted H³ mass

**Base:** `2270b6c7` — bound fixed radial spectral mass and isolate high radial escape.

The previous radial estimate isolated the polynomial Sobolev carrier ceiling
but retained a separately supplied raw-Fourier square mass ceiling. This
module proves that ceiling from the physical old velocity and kinetic balance.

## Plancherel and the actual Fourier encoder

At any strict physical time t∈(0,T), the actual weighted spectral state G(t)
may be deweighted coordinatewise. The raw Fourier coordinate equals the scalar
Plancherel transform of the actual old physical L² zero-order jet. Therefore

    h3TerminalRawVelocityFourierTotalSquareDefect G(t) 0 = E₀(t).

This uses the existing exact identification and PiLp norm-square formula.
The right-hand side is genuine kinetic energy, not a surrogate H³ norm.

## One fixed kinetic anchor

The closed kinetic energy derivative identities make E₀ antitone on each
strict energy-class interval (a,T). Choose any b∈(a,T). Then for t∈(b,T),

    RawSquare(G(t),0) = E₀(t) ≤ E₀(b).

By the fixed radial Sobolev-weight ceiling, for any ρ≥0,

    LowSquare_ρ(G(t)) ≤ (1+ρ²+ρ⁴+ρ⁶)E₀(b).

Thus no free raw-Fourier ceiling remains in the high-radial obstruction.

## Endpoint alternative and limitations

For positive terminal kinetic mass, failure of a strong physical terminal
L² trace supplies a fixed cofinally escaping spectral coordinate. The kinetic
anchor bounds every fixed radial carrier; the complementary algebraic squared
mass therefore grows without bound on each strict terminal subtail. To obtain
the claim for an arbitrary subtail (c,T), take an anchor b∈(a,c).

Together with the previously proved zero-terminal-mass trace, the theorem
states an **exact-mass L² trace or high-radial spectral remainder escape**
alternative, for all nonnegative fixed radial cutoffs.

The high-radial remainder is still defined as the total weighted spectral
square energy **minus** the radial low square integral. Proving it equals
an actual integral over the complementary Fourier set is a separate and next
measure-theoretic step. In particular, this package does not prove that
hypothetical smooth nonextension causes failure of the kinetic L² trace.
