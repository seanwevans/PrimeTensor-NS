# Fixed physical spectral PDE component escape

**Baseline:** `1f89bf8b` — transfer terminal angular escape to projected physical PDE source.

Let `A(t)` be the actual physical spectral Laplacian total and `B(t)` the actual physical Leray total. The committed physical projected momentum source is `R(t)=A(t)-B(t)`.

The new Lean module proves the pointwise estimate

`‖R(t)‖ ≤ ‖A(t)‖ + ‖B(t)‖`,

and a quantitative pointwise dichotomy: `M<‖R(t)‖` implies `M/2<‖A(t)‖` or `M/2<‖B(t)‖`.

More importantly, a finite two-source **cofinal pigeonhole** shows that if `R` is unbounded on every terminal subtail, then there exists a **fixed** component, `A` or `B`, which is unbounded on *every* terminal subtail. If neither component escaped, both would have finite ceilings after (possibly different) cutoff times. Taking the maximum cutoff would bound `R`, contradicting the source escape.

The preceding `ProjectedSourceEscape244` theorem derives cofinal unboundedness of `R` from failure of a strong physical L² terminal trace and positive terminal kinetic mass. Composing the arguments yields the fixed PDE component alternative. The module also proves that individual tail ceilings for both components imply an exact-mass strong terminal L² trace. If one component is eventually bounded while the L² trace fails, the other component necessarily escapes cofinally.

## Important boundaries

* This is a necessary obstruction to **failure** of a terminal physical L² trace, not to H³ nonextension by itself.
* It does not prove unboundedness of either component for every admissible solution.
* Fixed-channel cofinal escape does not imply an asymptotic sign, sharp rate, or direct lower bound in a signed H³ cubic transport channel.
* No new smooth continuation or Navier–Stokes global regularity result is asserted.

All statements use the already formalized physical Hilbert source and kinetic-limit hypotheses.
