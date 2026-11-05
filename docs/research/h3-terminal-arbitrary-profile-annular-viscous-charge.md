# Terminal H³ escape: arbitrary-profile annular viscous charges

**Baseline:** `1d6e1e86af2874180de8ee76dcff759256c1e53c`
(`derive arbitrary terminal viscous heights and disjoint cubic H3 charges`).

## New mathematics

The existing no-strong-H³-terminal-trace theorem already provides, for
**every** prescribed sequence of real heights `M(n)`, a genuine cofinal time
sequence with physical H³ high-radial dissipation strictly greater than
`M(n)` at the natural radius `n+1`. The previous finite-annulus persistence
and disjoint-cost proof specialized to `M(n)=(n+1)^3`. There is no analytical
reason to fix that exponent.

### 1. Finite annular persistence for arbitrary positive height

Fix a strict physical time `t` and `n : ℕ`, and let `A>0`. If

```
A < HighDissipation_(n+1)(U(t)),
```

then the exact radial dissipation partition and the fixed-time decay of the
high tail yield a finite outer radius `N≥n` with

```
3*A/4 < LowDissipation_(N+1)(t) - LowDissipation_(n+1)(t).
```

This is an actual physical Fourier annulus, not a formal subtraction.
Its time functional is continuous because it is the difference of the
already verified low-pass physical dissipation functionals. Hence a positive
`δ` exists with `t+δ<T` such that **throughout** `[t,t+δ]`

```
A/2 < finite-annulus H³ dissipation(s)
A/2 < high-radial H³ dissipation_(n+1)(s),
```

and the exact finite-annulus integral is at least `δ*A/2`. No uniform
continuity of the unbounded full H³ dissipation is invoked.

### 2. Arbitrary-profile cofinal terminal windows

Assume the original `LoggedPreterminalH3PathAdmissible` and
`PreterminalH3EnergyClass`, but **not** a physical kinetic L² nontrace
hypothesis. If the actual H³ spectral state has no strong terminal trace,
then for every positive sequence `M : ℕ → ℝ`, one obtains cofinal times,
finite outer radii, and positive widths at each `M(n)` half-height.

### 3. Disjoint physical charges and necessary width compression

Apply the existing geometric extraction theorem to obtain disjoint windows
along a strictly increasing `v : ℕ → ℕ`. Under the **additional hypothesis**

```
IntervalIntegrable (velocityH3DissipationAt u) volume a T,
```

the genuine physical dissipation integral bounds every finite partial sum:

```
∑_{k<m} δ(v(k)) * M(v(k))/2 ≤ ∫_a^T D_H³(s) ds.
```

The terms are nonnegative; `summable_of_sum_range_le` therefore proves
summability and the exact vanishing normalized width law

```
δ(v(k)) * M(v(k)) → 0.
```

The height profile may be any prescribed positive function of `n`,
including superpolynomial growth. **Quantifier order matters**: the time
sequence, annular outer radii and widths may depend on `M`. This result
does not establish a lower bound for any of these widths, hence does not
rule out the no-H³-trace branch or settle Navier–Stokes regularity.

## Remaining hard PDE problem

It is necessary to compare these forced width-compression clocks with the
already formalized finite-annulus PDE variation coefficients, actual source
budgets and spatial first-moment estimates. A contradiction would require a
profile-independent lower persistence price or a proven restriction on the
variation coefficient that survives the outer-radius and source amplitude
choices. Merely making peak heights arbitrarily large is insufficient.

## Audit

- `FullThirdSolenoidalTerminalProfileAnnularPersistence.lean` (2 theorems)
- `FullThirdSolenoidalTerminalProfileDisjointViscousCharge.lean` (2 theorems)
- `tools/audit/register_h3_full_third_solenoidal_terminal_profile_viscous_windows.py`
- 4 declarations, 8 `#check`/`#print axioms` audit lines

No `sorry`, `admit`, or new axioms are introduced. The user's Lean build is
the authoritative compilation check.
