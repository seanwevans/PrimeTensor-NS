# Canonical exact H³ anchor through disjoint quadratic-sharp clocks

**Base:** `b102dde4` — exact anchor at one canonical physical annulus.

The old disjoint canonical construction exported a nonnegative spectral
coefficient `K(n)`, but not the identity that the constructor actually chose,
`K(n)=‖U₃(τ(n))‖`. A separate copy of that existential sequence must not be
retroactively relabeled as the norm without a proof. This patch therefore
**reconstructs** the cofinal selection from the exact-anchor pointwise clock.

The existing source theorem is strengthened only to export facts it had already
proved internally: the quarter-cubic gap at the minimal outer cutoff, and
its below-cutoff minimality. Its name and original hypotheses are unchanged;
new trailing conclusions are added. The new cofinal constructor carries the
same first-crossing choice, exact quadratic-sharp PDE window, persistence
floor, pairwise disjointness, finite sum of physical H³-dissipation costs,
original three-scale alternative, and attained canonical projected-source
maximum, now with **exact** K at every cofinal witness.

At every anchor `τ(v(k))`, the new theorem yields

    K(v k) = ‖U₃(τ(v k))‖
    K(v k)^2 ≤ E₃(τ(v k))
    (K(v k)*C(v k))^2 ≤ E₃(τ(v k))*C(v k)^2.

The critical eighth-power annulus estimate can consequently be written
without an independent K:

    U^8 R^3 < 48^8 E₃(τ(v k))^4 C(v k)^8 D^5

**provided at the same index** that `(Q+1)^8 ≤ D R^9` and
`U R^6 < Λ(R,Q,K,C)`. Neither rate escape nor width cap has been inferred
unconditionally for the new extracted witness sequence. The old sequence's
conditional extension theorem remains distinct until its critical-regime
argument is rebuilt for this exact-anchor selection.

No terminal regularity or unsupported identification of the two selections
is claimed. Lean compilation must be executed with the repository toolchain.

## Build dependency ordering

`lake env lean` checks a source file but does not update the compiled `.olean`
for imports. The exact-anchor **source** theorem in this package now exports
the previously internal quarter-cubic gap and minimality. Build its module
with `lake build ...CanonicalExactAnchorSource244` **before** checking the
dependent `...CanonicalExactAnchorCofinal244.lean`, or the cofinal compiler
may still read the older existential statement and report a mismatch at
`hRaw`. The mathematical statements are unchanged by this fix.
