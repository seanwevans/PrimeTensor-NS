# Constructive late-viscous reciprocal-square-root tail threshold

**Base:** `01b88fb5c253bc06fd4982f17ec98869f452fefa` — accepted secondary physical PDE persistence.

## Main implication

Let `A>0` be the normalized prescribed-gauge fourth-power H3 spike, `B>0`
the actual remaining terminal H3 dissipation, `E>=0` the fixed kinetic
anchor, and `R>0` the actual PDE quintic frequency coefficient. The existing
late two-slice rate branch is

    A² <= R B (E + 3 D(sState)) (E + 3 D(sSource)).

Under the explicit non-kinetic gap

    4 R B E² < A²,

select the **canonical, not arbitrarily postulated**, threshold

    h := A / (12 sqrt(R B)) > 0.

Then `R B (E+3h)² < A²`, so one of the two actual selected times satisfies
`D(s)>h`. The preexisting finite-band capture and explicit projected-
Navier–Stokes persistence theorem give a secondary interval with

    η₂ = min ((T-s)/4) ((h/2)/(2(Λ₂+1))) > 0,
    h/2 < D_low,J₂(q) <= D_H3(q)  (s <= q <= s+η₂),
    η₂ (h/2) <= integral_m^T D_H3(q) dq.

The kinetic-anchor low-radial dissipation bound, with the independently
verified eighth-order cutoff polynomial, moreover forces

    h/2 < 4 E0(b) (J₂+1)^8.

The cofinal theorem attaches the **same canonical threshold** and the
secondary cutoff cost to the unchanged prescribed-gauge minimal crossing
witnesses, retaining the other Fourier/source/kinetic alternatives,
frequency escape, disjoint original viscous sum and terminal tail limit.

## Scope and remaining gap

This forces large physical dissipation observations and escaping capture
frequency *conditional on the non-kinetic gap*. Neither `R B` nor `A` is
uniformly controlled along the cofinal sequence. The first and second late
PDE windows need not be disjoint; their individual costs cannot be added
without overlap control. Thus no continuation theorem is claimed.

The patch contains no `sorry`/`admit`. The registrar checks every declared
theorem and its axioms. Full elaboration and build must run against the
project's pinned Lean/mathlib toolchain in the user's local repository.
