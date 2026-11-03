# Minimal-shell Riccati peaks: arbitrary normalized physical source pressure

**Committed base:** `6dd8dba0` — minimal Riccati H³ anchor or actual twelfth/ninth physical source rates.

The original sixth/ninth physical-source gate gives, in its bounded-charge
branch, an alternative for **each** `ε > 0`, eventually in the selected
minimal-shell index. The previous Riccati gate used only `ε = 1`.

The physical inverse-root clock for a Riccati-heavy window supplies
`R² < 4(4K²+1) E_anchor` or `16 < (T-t) R`, where `R = v(k)+1` and
`K = h3PathSqrtEnergyRiccatiCoefficient`. If the quadratic anchor branch
fails, `R ≥ 1` implies

    R³ (T-t)/4 > 4 R² ≥ 4.

Thus the *same* compressed-time cap is impossible for **every**
`0 < ε ≤ 1`, not just ε=1. At any sufficiently late Riccati-heavy
window the remaining source-rate alternatives therefore are

    R² < 4(4K²+1) E_anchor,
    R¹² ≤ 512 ε² (2304 E_anchor C² (N+2)¹⁰ + 1),
    R⁹ ≤ 16 ε² (36 C² ((N+2)⁸ + (R+1)⁸) + 1).

The eventually quantifier is inside the epsilon quantifier: a distinct
terminal threshold is permitted for each ε. The proof does **not** claim
that all ε alternatives hold simultaneously at any fixed window.

For any fixed `M ≥ 0`, take an explicit positive `ε ≤ 1` with
`512 M ε² ≤ 1` and `16 M ε² ≤ 1`. The two physical factors are
nonnegative, so the previous alternative strengthens to

    R² < 4(4K²+1) E_anchor,
    M R¹² ≤ 2304 E_anchor C² (N+2)¹⁰ + 1,
    M R⁹ ≤ 36 C² ((N+2)⁸+(R+1)⁸) + 1.

This is arbitrary normalized source pressure at late Riccati peaks,
**not** an unqualified source-divergence theorem. All original physical
first-crossing, last-shell kinetic, exact PDE-window, and signed-gap
witnesses remain the same.

A conditional contradiction criterion follows: if eventually the
quadratic anchor alternative fails and both normalized source terms
are at most `L` times their respective `R¹²`/`R⁹` scales, then applying
the arbitrary-multiplier bound at `M=L+1` excludes all sufficiently late
Riccati-heavy windows.

The theorem keeps the complementary branch of **unbounded actual cubic
window charges**, already known to imply every-tail charge divergence.
The previously proved bounded-positive-gap implication to recurrent
Riccati windows remains available on that branch.

**Open:** Neither an eventual quadratic-anchor exclusion nor a finite
normalized source-rate ceiling is derived unconditionally from the physical
PDE. Nothing here proves global smooth continuation, rules out blow-up,
or assumes full-terminal H³ dissipation integrability.
