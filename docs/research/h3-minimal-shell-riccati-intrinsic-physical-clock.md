# Minimal first-crossing Riccati peaks: intrinsic PDE duration and terminal-frequency gate

**Base:** `f2561958` (`charge minimal H3 Riccati energy to anchor or actual intra-window transport`).

## New hard mathematical step

Let `R=v(k)+1`, `K=h3PathSqrtEnergyRiccatiCoefficient` and `B=4 K²+1`.
The earlier actual Riccati window has a physical time `s` in its original
PDE interval `[t_k,t_k+δ_k]` where `R² < B E₃(s)`.

The already established exact physical H³ Riccati estimate makes
`1/sqrt(E₃(t)) + (K/2)t` monotone on the strict energy-class interval.
Consequently

    1/sqrt(E₃(t_k)) <= 1/sqrt(E₃(s)) + (K/2)(s-t_k).

If `4 B E₃(t_k) <= R²`, the Riccati peak forces `E₃(s) > 4 E₃(t_k)`.
Taking square roots and reciprocals, this implies

    1 < K (s-t_k) sqrt(E₃(t_k)).

Since `4 K² <= B` and `4 B E₃(t_k) <= R²`, one also has
`4 K sqrt(E₃(t_k)) <= R`. Hence `4 < (s-t_k)R <= δ_k R`.

Most importantly, this is the **literal quadratic-sharp PDE selector**,
not an arbitrary interval: its first `min` branch imposes

    δ_k <= ((T-t_k)/2)/2 = (T-t_k)/4.

Therefore **each actual Riccati-heavy window** obeys

    R² < 4 (4 K²+1) E₃(t_k)  OR  16 < (T-t_k) R.

This avoids an assumed bound on the integral of signed within-window
transport. It uses only the proven inverse-root Riccati derivative control
and the literal PDE window width. In particular a small original anchor
cannot grow to the quadratic Riccati amplitude unless the inner frequency
is already at least inverse-linear in remaining physical time.

## Formal deliverables

- `h3Critical_scalar_inverseRootPeak_anchorOrLinearClock` (pure scalar lemma)
- `h3Critical_scalar_quadraticSharpWidth_le_halfBudget` (literal selector cap)
- `h3Critical_minimalShellQuadraticPeak_anchorOrTerminalClock` (physical PDE bridge)
- `h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt` (window property)
- `h3Critical_noL2Trace_minimalShell_cofinalRiccatiAnchorOrTerminalClock` (same selected witnesses, eventual implication and conditional cofinal consequence)

The physical bridge is unconditional **given an actual quadratic Riccati
witness**. No terminal H³ dissipation or transport integrability is used.
The no-L²-terminal-trace cofinal recurrence still explicitly needs both
unbounded selected cubic charges and bounded selected positive signed-gap
replenishment. Neither premise is established here, and global smooth
Navier–Stokes regularity is not claimed.

## Verification

The registrar is idempotent and adds the theorem/definition import and
`#check` / `#print axioms` entries to both audit roots. The pinned Lean
and full Lake build must be run in the user's repository environment.
