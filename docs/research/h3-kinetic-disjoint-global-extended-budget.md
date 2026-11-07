# Global extended physical H3 cost of disjoint kinetic annular clocks

Base commit: `25aef04de911c21f5aa91b6f526639fa992cbfaf`.

The preceding module selected cofinal windows with exact kinetic-only
Navier--Stokes time widths and pairwise separated closed intervals. It proved
each annular physical viscous floor and a finite sum of extended full-H3 costs,
but did **not** charge that sum to the single full-dissipation integral.

## New hard analysis: global packing without terminal L1

For strictly separated half-open temporal windows

    W(k) = (p(k),p(k)+w(k)],  a < p(k) < p(k)+w(k) < T,

and arbitrary real dissipation density f with `H(k) <= f(r)` on each closed
window, prove for **every finite prefix m**

    sum_{k<m} ofReal(H(k)) * ofReal(w(k))
      <= lintegral_{(a,T)} ofReal(f(r)) dr.

The proof uses the Mathlib equality `lintegral_biUnion_finset` on the
measurable, pairwise disjoint `W(k)` and set-inclusion monotonicity. Unlike
an attempted linearity argument in a nonmeasurable density, this theorem
requires **no** measurable/continuous full-H3 dissipation and makes **no**
terminal L1 hypothesis. The relevant Mathlib equality directly covers an
arbitrary ENNReal integrand.

## Transfer to the true physical PDE

Use the existing same-witness kinetic cofinal theorem and its original
frequency cutoffs `N(v(k))`, physical sample times `tau(v(k))`, positive widths
`delta(v(k))`, and lower heights `M(v(k))/4`. Each window's floor is below
`velocityH3DissipationAt u r`. The global bound becomes

    sum_{k<m} ofReal(M(v(k))/4)*ofReal(delta(v(k)))
      <= lintegral_{(a,T)} ofReal(velocityH3DissipationAt u r) dr.

The same chosen windows also obey the previous ordinary finite-annulus
integral charges and kinetic clock/rate alternatives. No re-selection,
interval shortening, or resummation over overlapping intervals occurs.

## Honest terminal-divergence criterion

If

    sup_m sum_{k<m} ofReal(M(v(k))/4)*ofReal(delta(v(k))) = top,

then the single physical full-H3 extended dissipation over `(a,T)` equals
top. This is a **conditional** frequency-versus-time obstruction: the outer
cutoff chosen by fixed-time Fourier tail decay may increase so rapidly that
its kinetic time width is too short to force divergence. The theorem does not
assert unconditionally that the sum diverges or that Navier--Stokes continues.

The three registered Lean theorems are:

- `thirdFull_scalar_disjointWindows_le_globalExtendedBudget244`
- `thirdFull_scalar_disjointWindows_divergence_forces_infinite244`
- `thirdFullPhysical_noH3Trace_kineticDisjointGlobalExtendedBudget244`

Lean compilation must be run against the repository's pinned Lean/mathlib.
