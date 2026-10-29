# Canonical higher-radial temporal budget: conditional compression

Base commit: `8974277b` — extend canonical inner-cutoff higher radial escape across full PDE windows.

## Exact conclusion

The existing physical theorem gives, on the *original* disjoint windows
`[τ(v k), τ(v k)+δ(v k)]`, at every interior time and every natural radial
shift `m`, the extended physical top-order `q^(4+m)` moment lower bound

    ENNReal.ofReal(((R_k²)^m) * R_k³/8) ≤ M_top,4+m(s),
    R_k = v(k)+1.

Suppose, **as an additional analytic hypothesis for one fixed m**, there
exists a nonnegative, real-valued `F_m` on the whole strict-time interval,
`IntervalIntegrable F_m volume a T`, such that at every strict time

    M_top,4+m(s) ≤ ENNReal.ofReal(F_m(s)).

By the `ENNReal.ofReal_le_ofReal_iff` lemma, the lower bound transfers to the
real pointwise inequality `((R_k²)^m) R_k³/8 ≤ F_m(s)`. The already-proved
`h3Path_disjointNonnegativeWindows_finiteHeightCost_le244` and bounded
partial-sum theorem imply

    ∑_k δ_k * ((R_k²)^m * R_k³/8) < ∞.

Consequently, since `R_k^(2m+3) = (R_k²)^m R_k³`, the original canonical
clock obeys the necessary higher-moment compression

    δ_k R_k^(2m+3) → 0.

The whole original existential canonical witness `τ,N,K,C,δ,v` is retained
and the conclusion is quantified for *every* fixed natural `m` and every
eligible real-valued integrable majorant `F_m`.

## Boundary of the result

The H³ finite dissipation budget in the source hypotheses controls `m=0`
(and its related cubic window charge) but does **not** supply higher-moment
time integrability for `m>0`. The additional majorant premise is never
constructed or derived here; it is a genuine conditional assumption.
Without it, unbounded moment height on shrinking windows is compatible
with finite accumulated H³ dissipation. This file does not prove a
singularity contradiction, smooth continuation, or the missing upper envelope.

## New formal declarations

- `h3Path_scalar_disjointWindows_integrableMajorant_weightedCharge244`
- `h3Path_physicalTopHigherMoment_upperEnvelope_forces_realFloor244`
- `h3Path_scalar_summable_higherCubicCharge_forces_widthCompression244`
- `h3Path_noL2Trace_exactAnchor_integrableTopHigherEnvelope_forces_widthCompression244`

The Lean code must be compiled with the pinned Lake toolchain; only ZIP,
registration and static source audits have been run in the packaging environment.
