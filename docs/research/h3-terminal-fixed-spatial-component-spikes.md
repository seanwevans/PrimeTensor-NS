# Fixed spatial physical-source component terminal spikes

Base: `000bb63c707d4dcac886e78475935c91e6ab2016`.

## Proven in the proposed module (subject to local Lean verification)

1. The actual finite Hilbert product has the identity
   `‖V‖² = ∑ j : Fin 3, ‖V.ofLp j‖²` (Mathlib `PiLp.norm_sq_eq_of_L2`).
   If each component has norm `≤ B` with `B≥0`, then `‖V‖ ≤ 3B`.
2. For any physical Hilbert path cofinally unbounded on each terminal tail,
   a single fixed coordinate `j : Fin 3` is cofinally unbounded on every tail.
   Otherwise each coordinate would have a bounded later tail, and a common
   later tail would bound the full Hilbert norm, contradiction.
3. Applied to the actual projected source, failure of the strong terminal
   physical `L²` velocity trace selects a fixed projected source coordinate.
4. Applied to the prior fixed Laplacian/Leray source alternative, failure of
   the same trace selects ONE fixed pair (physical source, spatial coordinate)
   of six possibilities, with cofinal norm spikes independent of cutoff and
   threshold.

## Scope and next genuinely analytic obstacle

This proves a fixed spatial-coordinate **spike** obstruction, not a fixed
coordinate **time-nonintegrability** obstruction. Unbounded continuous functions
can still be integrable on a finite time interval by concentrating on narrowing
spikes. A finite-product Bochner integrability theorem should yield the
nonintegrability statement, but needs its own audited Lean proof.

The assumption is absence of an actual physical terminal L² velocity trace.
It does not prove this absence, prove smooth continuation, or prove the
unconditional Navier–Stokes regularity problem.
