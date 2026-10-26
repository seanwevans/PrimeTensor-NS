# Finite terminal dissipation forces cubic window-clock collapse

**Parent:** `73c913ee` (`bound disjoint cubic H3 annulus costs by terminal full dissipation`).

The previous module extracted a pairwise separated cofinal subsequence of cubic H3 annular windows and proved that, **assuming interval integrability of the full physical H3 dissipation up to T**, their partial positive costs are uniformly bounded by

\[
 M=\int_a^T D_3(t)\,dt.
\]

This module promotes bounded positive partial sums to `Summable` using mathlib's `summable_of_sum_range_le`, then applies `Summable.tendsto_atTop_zero`:

\[
 \sum_{k\ge0}\frac{\delta_{v(k)}(v(k)+1)^3}{2}<\infty,
 \qquad \delta_{v(k)}(v(k)+1)^3\to0.
\]

Thus a hypothetical integrable-dissipation terminal branch **necessarily has cubic-normalized persistence clocks vanishing**, even though the absolute selected window widths are positive. This does not yet contradict preterminal H3 admissibility or the no-L2-trace branch.

## Necessary PDE rate concentration in the explicit-width geometry

The earlier anchored PDE construction chooses a positive window by

\[
 \delta=\min\bigl\{b/2,1,\;g/[2(\Lambda+\Xi+1)]\bigr\},
 \qquad g=B_{R,Q}(t)-A>0.
\]

The pure algebraic lemma proves: if `A*delta ≤ M`, `2*M < A*b`, and `M < A`, then

\[
 A g\le 2M(\Lambda+\Xi+1).
\]

**Interpretation:** when terminal-time slack `b` and the unit cap cannot account for the small width, the PDE variation-rate coefficient must. The new module does not yet replace the existential selector in the cofinal-window theorem with a canonical explicit `min` value; that further connection is needed before this alternative can be applied unconditionally to actual selected terminal witnesses.

The results remain conditional on the actual terminal `IntervalIntegrable (velocityH3DissipationAt u) volume a T` assumption. No global Navier–Stokes regularity conclusion follows.

## Auditing

The registrar is idempotent, adds the exact `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean` import, and registers `#check` and `#print axioms` for all four new theorems. Run `proof/generate_index.py` after registration, then `lake build` and the baseline audit.
