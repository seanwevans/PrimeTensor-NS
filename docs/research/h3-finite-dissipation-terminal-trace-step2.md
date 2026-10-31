# Finite full H³ dissipation and the physical L² terminal trace — Step 2

Base commit: `f82c08a6`. Requires the separately compiled Step 1 module
`Critical/Energy/FiniteDissipationPointwise.lean`.

## Mathematical result

Let `U` be the actual three-component physical velocity Hilbert state, `G` the
previously identified projected Laplacian-minus-Leray source, `E₀` kinetic
energy, and `D` full H³ dissipation. On any strict anchored terminal tail
`b < t < T` we already have

    ‖G(t)‖ ≤ (3 + C_Leray) [1 + 6 E₀(b) + 3 D(t)].

If `D` is interval-integrable on `[a,T]`, the RHS is integrable on `[b,T]`.
Positive-time source continuity supplies a.e.-strong measurability, so `G`
is Bochner-integrable. The existing genuine Hilbert FTC gives

    U(t) = U(b) + ∫_b^t G(r) dr.

The integral primitive extends continuously from the left to `T`, yielding

    U(t) → U(b) + ∫_b^T G(r) dr    in L² as t ↑ T.

Consequently the finite-full-dissipation and no-strong-L²-trace hypotheses
cannot hold simultaneously within the stated preterminal path/energy class.
No positive terminal kinetic mass assumption is needed.

## Scope

This rules out the *no physical L² trace* branch under a **strong** finite
H³-dissipation assumption. It neither proves finite H³ dissipation for all
Navier--Stokes solutions nor supplies an H³ endpoint or smooth extension.

## Verification

This patch is a proof candidate. The pinned Lean/mathlib toolchain is not
available in the packaging environment; run the supplied local Lake test.
Do not register, commit, or use the new theorem in other results until it
compiles locally.
