# Minimal-shell Riccati peaks: outer-frequency or actual source-envelope escape

**Baseline:** `e2d0faa6` — force arbitrary normalized physical source pressure at minimal H3 Riccati peaks.

## Exact boundedness calculation

Write `R = v(k)+1 >= 1`, `Q = N(v(k))+2 >= 0`, `E = E3(t(v(k)))`,
`C = C(v(k)) >= 0`. For any fixed nonnegative outer-radius multiplier `D`
and nonnegative source-envelope bound `L`, assume at one index

    E <= R^2,      Q <= D R,      C <= L.

The original normalized physical PDE-rate factors have explicit ceilings:

    2304 E C^2 Q^10 + 1 <= (2304 L^2 D^10 + 1) R^12,
    36 C^2 (Q^8 + (R+1)^8) + 1
       <= (36 L^2 (D^8 + 256) + 1) R^9.

The constants are literal: `(R+1)^8 <= (2R)^8 = 256 R^8`, and
`R^8 <= R^9`. Neither Fourier shell mass nor source coefficient is replaced.

The accepted normalized-source theorem supplies, for each fixed nonnegative
multiplier `M`, an eventual implication from any Riccati-heavy window to
one of three branches:

    R^2 < 4(4 K_Ric^2 + 1) E,
    M R^12 <= 2304 E C^2 Q^10 + 1,
    M R^9 <= 36 C^2 (Q^8+(R+1)^8) + 1.

Set

    M(D,L) = 2304 L^2 D^10 + 36 L^2 (D^8+256) + 3.

If the quadratic anchor branch is false, `E <= R^2` follows from
`4(4 K_Ric^2+1) E <= R^2`, since `E >= 0`. Both rate alternatives
contradict the corresponding explicit ceilings if `Q <= D R` and `C <= L`.
Therefore, for **each fixed** nonnegative `D,L`, eventually every
Riccati-heavy window satisfies the three-way physical obstruction

    R^2 < 4(4 K_Ric^2+1) E  OR  Q > D R  OR  C > L.

This is the primary result, requiring no anchor bound. Under the additional
eventual hypothesis that the quadratic anchor inequality always fails, the
alternative improves to `Q > D R OR C > L` at each late Riccati window.
If *both* `Q/R` and `C` are eventually bounded, that extra anchor hypothesis
therefore excludes late Riccati peaks outright.

## Preservation and limitations

The exported no-terminal-L2-trace witness theorem carries this result on the
**same** strictly increasing and physically disjoint minimal first-crossing
selector, including the literal last kinetic shell, quadratic-sharp PDE
width, physical sixth/ninth-rate branch and exact signed-gap accounting.
The complementary unbounded-cubic-charge branch is preserved unchanged.

Quantifiers matter: the late-tail threshold depends on `(D,L)` and cannot
be interchanged with the `∀ D L`. Moreover the triple alternative is
proved only in the *source-pressure* branch of the original global
dichotomy; the complementary cubic-charge branch is still possible.
No uniform bound on the actual projected source envelope `C`, no outer
cutoff cap, no subquadratic H3 anchor, and no terminal H3 integrability are
claimed unconditionally. No Navier--Stokes regularity is proved.
