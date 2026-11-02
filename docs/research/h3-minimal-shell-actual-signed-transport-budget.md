# Exact signed H³ transport on the minimal first-crossing annular PDE windows

Baseline: `a934eeca`, "quantify unconditional physical H3 energy versus minimal annular width".

## Same-witness advance

The actual minimal first-crossing witness supplies at every s in its PDE
persistence window [t, t+delta]:

    (n+1)^3/2 < D_annulus(s) <= D_H3(s).

The exact physical Navier--Stokes H3 energy identity is already formalized:

    E3'(s) + 2 D_H3(s) = - T_H3(s).

Consequently, with R=n+1, on every such strict physical slice:

    E3'(s) + R^3 < -T_H3(s),

and, using the committed H3 dissipative Riccati inequality:

    E3'(s) <= -R^3/2
       OR
    R^3/2 < K_Ric sqrt(E3(s)) E3(s).

In particular, on any nondecreasing-energy slice E3'(s)>=0,

    R^6 <= K_Ric^2 E3(s)^3.

The main theorem synchronizes these signed physical statements with the
previously committed unconditional energy-width inequality, exact source
and PDE clock, last-shell and energetic-width-shell kinetic certificates,
and sixth/ninth-rate alternative on the identical disjoint cofinal windows.

## Limitations

The proof needs only eventually strict physical anchor times, obtained from
the selected cofinal sequence. It does NOT assert that the physical energy is
nondecreasing on those windows. It neither assumes nor proves full terminal
H3 dissipation integrability or global H3 regularity. The dynamic signed
transport sign and size remain to be controlled; the exact identity alone
cannot provide absorption.

Verification in the assistant environment includes ZIP archive integrity,
placeholder-free audit checks, and idempotent registration. Lean compilation
and full repository builds must run on the user's Lean installation.
