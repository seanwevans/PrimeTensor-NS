# Cofinal physical escape on noncompressed disjoint H³ annuli

Baseline commit: `a8681c18`.

This module takes the **no-L²-terminal-trace** disjoint annulus witnesses from the
committed relative-outer-frequency/compression theorem. No integrability of
full terminal H³ dissipation is assumed.

Let `Rₖ = v(k)+1`, `Qₖ = N(v(k))+1`, `Cₖ` be the actual attained
projected-source envelope on the relevant half-terminal interval, and
`Eₖ = E₃(t(v(k)))`. Define the geometric cubic clock

    Gₖ = Rₖ³ (T - t(v(k))) / 4.

Either the certified annular charge partial sums `Σₖ δ(v(k)) Rₖ³/2` are
unbounded; **or**, for every `η>0` such that `Gₖ>η` arbitrarily far out,
for every `B≥0` and `D≥1` and every initial index `n`, there is `k≥n` with

    Eₖ Cₖ² > B    or    Cₖ² > B    or    Qₖ+1 > D Rₖ.

This is an aggregate cofinal disjunction: it does not assert any one of its
three arms must consistently occur. The companion scalar lemma shows that
if the two source burdens are *both eventually bounded*, the relative outer
radius must escape every fixed multiple of the inner radius along arbitrarily
late windows, provided geometric noncompression recurs cofinally.

The proof is a contrapositive of the existing conditional clock-compression
theorem, not an assumption that finite physical source/energy/radius bounds
hold in general. The persistent finite-band windows remain exact and disjoint.

Theorems:

- `h3Critical_scalar_cofinalNoncompression_forces_jointPhysicalEscape`
- `h3Critical_scalar_boundedSource_noncompression_forces_outerEscape`
- `h3Critical_noL2Trace_disjointAnnuli_noncompression_forces_cofinalSourceOuterEscape`

**Limitation:** No Navier–Stokes regularity conclusion follows; the
noncompressed branch, bounded-charge branch and source bounds have not been
ruled out.
