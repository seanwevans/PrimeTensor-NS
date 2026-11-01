# Physical PDE factor escape on the original cofinal quintic source windows

**Base:** `2c8ff160` (accepted cutoff-or-positive-quadratic-PDE-cost gate).

Let the actual cofinal source-window parameters be

    S_k = max(1, sigma(v k)) + 1,
    P_k = 4 q(v k) > 0,
    H_k = M(v k) + q(v k)/[3(3+C_L)] > 0,
    J_k = E(t(v k))-1,
    K_k = A_k^2 B_k.

The accepted theorem supplies on each selected window either (a) an actual
Riccati-energy observation, (b) `w_k <= J_k/H_k`, (c) `H_k <= 16 J_k S_k^4`,
or (d) **both**

    S_k^2 P_k^2 < K_k,
    H_k P_k^4 <= 16 J_k K_k^2.

## First physical factor split

Because `A^2>=0`, the strict positivity of `A^2 B` implies `B>0`. If
`|A|<=S` and `B<=P^2`, multiplication gives `A^2 B<=S^2 P^2`, contradicting
(d). Thus (d) alone implies

    S_k < |A_k|  OR  P_k^2 < B_k.

No sign assumption on B is introduced. The exact witnesses, including the
actual selected PDE factors, remain unchanged. It is important that the
previously accepted cofinal theorem supplies named A/B witnesses, but not
their original explicit state/source formulae in its *result type*. This
patch does not falsely claim that those formulae have been re-exposed.

## Arbitrary quantitative factor-ceiling test

For arbitrary nonnegative proposed local factor ceilings `L,Q` with

    16 J_k (L^2 Q)^2 < H_k P_k^4,

on the positive PDE-cost branch it is impossible that `|A_k|<=L` and
`B_k<=Q`, because the latter would imply

    H_k P_k^4 <= 16 J_k (A_k^2 B_k)^2
              <= 16 J_k (L^2 Q)^2.

Consequently the following implication holds on each unchanged window:

    if J_k < H_k w_k                  (geometric compression excluded),
       16 J_k S_k^4 < H_k            (cutoff branch excluded),
       16 J_k (L^2 Q)^2 < H_k P_k^4 (local factor ceilings insufficient),
    then either an actual Riccati-energy observation occurs,
         or L < |A_k| or Q < B_k.

The three antecedents are **explicit conditional assumptions**, not derived
terminal hypotheses. This is an escape frontier, not a source-window charge
divergence theorem or an unconditional Navier-Stokes regularity result.

## Formalization

- `h3Critical_scalar_positiveQuarticPDECost_forces_factorEscape`
- `h3Critical_scalar_quadraticQuarticPDECost_forces_factorEscape`
- `h3Critical_noL2Trace_cofinalQuintic_quarticPDEFactorEscape`

Use `lake env lean` with the pinned Lean/mathlib build and inspect axiom
prints. Static packaging is not a substitute for Lean elaboration.
