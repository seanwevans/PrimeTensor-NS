# Sublinear physical H3 anchor energy forces minimal annular width escape

Base commit: `62a79e6b` — width-averaged energetic shell synchronized with
minimal physical PDE sixth/ninth rate barriers.

## The sharper energy threshold

Write `R_k=v(k)+1`, `Q_k=N(v(k))+1`, and `L_k=N(v(k))-v(k)`.
The same quarter-cubic first crossing gives the **strict**, actual-energy inequality

    R_k^3 < 4 (Q_k+1)^2 E3(t_{v(k)}).

If the physical energy grows *sublinearly relative to the inner radius*,

    E3(t_{v(k)}) / R_k -> 0,

then the selected actual minimal outer cutoff and literal annular width obey

    (Q_k+1)/R_k -> +infinity,
    L_k/R_k -> +infinity.

Proof: for any fixed D, a hypothetical `Q_k+1 <= D R_k` would imply
`R_k < 4 D^2 E3(t_k)`, contradicting `4 D^2 E3(t_k)/R_k -> 0`.
The exact integer identity `Q_k+1 = R_k+L_k+1` transfers the divergence
to width. Neither source control nor terminal clock noncompression is used.

This improves an earlier result requiring E3 to be eventually bounded:
`E3=o(R)` permits unbounded energy, as long as its growth is sublinear.
Sublinearity remains an explicit condition and is not shown to follow from
Navier–Stokes or no-terminal-strong-L2-trace.

## Same physical witnesses

The newly exported existential witnesses preserve, on one sequence:
- minimal first-crossing and positive last-shell raw Fourier kinetic mass;
- width-averaged positive-kinetic energetic shell;
- exact quadratic-sharp projected PDE source clock and disjoint physical windows;
- certified annular cost and the full sixth/ninth source-rate dichotomy.

No terminal H3-dissipation integrability, artificial outer cutoff, or new
kinetic mass floor is inserted. No regularity conclusion follows.

## Verification

The archive and registrar can be checked independently. Full Lean elaboration,
module build, root/audit compilation, fragment checks and baseline audit must
pass on the local PrimeTensor-NS Lean environment before committing.
