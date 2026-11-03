# Minimal H³ first crossings: exact carrier mass or physical PDE-component excursion

**Base:** `6355d643` — force occupied minimal H³ kinetic carrier or actual physical source peak.

The previous same-selector theorem says that, in the bounded-cubic-charge / quantified-pressure branch, for each fixed nonnegative `D,L` and at each sufficiently late Riccati-heavy minimal window, either:

1. `R² < 4(4K_Ric²+1) E₃(t)`, or
2. the *last occupied shell* `[m+1,m+2]` lies above frequency `D R`, or
3. the physical projected source has a strict norm peak above `L` on the canonical half-terminal interval `[t,t+(T-t)/2]`.

Here `R=v(k)+1`, `N=m+1`, and the selected `t,N,m,C,δ,v` remain unchanged.

## Exact kinetic mass cost

Define the **literal first-crossing overshoot**

`ω = (LowDissipation(N+1)-LowDissipation(R)) - 3 R³/4 > 0`

and the last-shell raw kinetic Fourier mass

`μ = RawKineticMass(m+1,N+1)>0`.

The already proved physical shell inequality `ω ≤ 4 (N+2)^8 μ` gives

`ω / (4 (N+2)^8) ≤ μ`.

This is a quantitative mass floor at the actual carrier, but it depends on the **actual overshoot**, which is merely positive and may be arbitrarily small relative to `R³`. Neither minimality nor the PDE provides a uniform positive normalized overshoot fraction. No false uniform mass lower bound is inferred.

## Actual projected-source peak splitting

The projected momentum source is *definitionally* the difference between the inverse-Fourier physical Laplacian `D(t)` and Leray transport `L(t)`:

`P(t)=D(t)-L(t)`.

The existing proved Hilbert-triangle estimate gives, for any fixed strict times `t,s`,

`||P(s)|| ≤ ||P(t)|| + ||D(s)-D(t)|| + ||L(s)-L(t)||`.

Test the previous actual source-peak result at `3L`, not `L`. A strict peak `3L < ||P(s)||` forces at least one of the **three genuine physical channels** to be greater than `L`:

- the source norm at the original minimal-window anchor `||P(t)||`;
- the temporal increment of the physical Fourier Laplacian `||D(s)-D(t)||`;
- the temporal increment of physical Leray transport `||L(s)-L(t)||`.

The same attained `s` is retained and belongs to the canonical **half-terminal** source interval, *not necessarily* the shorter disjoint dissipation window `[t,t+δ]`. No time-integrated cost follows from a pointwise peak without further persistence bounds.

The new cofinal theorem retains the unbounded-cubic-charge branch as an alternative. It does not assert recurrence unconditionally, because the signed-gap-budget hypothesis has not been established. The new source splitting does not bound the jump terms, and does not prove Navier–Stokes continuation.

## Next hard analytic gap

The source branch is now pinned to actual time observations of physical PDE components. Proving a **uniform source temporal modulus**, a bound on either the diffusion or Leray jump, or a coercive relation from `ω` to `R³` would remove a real obstruction. These cannot be inferred from mere strict-time continuity or `μ>0`.
