# Exact physical H³ signed Fourier excess: diffusion/Hilbert versus transport

Base checkpoint `d2b24060` — the PDE signed-excess terminal-width secant theorem.

## What is now closed

The preceding code identified the actual normalized Fourier radial variance

    R(t) = 1 - E2(t)^2 / (E0(t) D3(t))

and its signed physical derivative `R' = -X/(E0 D3)^2`, with `X` initially described through `E0'`, `E2'`, and the proven physical Hilbert representation of `D3'`. It then substituted the actual Navier–Stokes right-hand side for the order-zero and order-two energy derivatives.

This patch splits the PDE sources using the **existing** `velocityH3PDEDerivative0At_eq_split` and `velocityH3PDEDerivative2At_eq_split`, with the required momentum splittings and pairing integrability supplied by the admissible physical H³ class. Existing physical pressure cancellations remove both order-zero and order-two pressure contributions. Existing flux cancellation removes order-zero transport.

Write `A = E0 D3`, `L_j = velocityH3DiffusionDerivativejAt`, `T_j = velocityH3TransportDerivativejAt`, and `H = D3'` for the actual fourth-radial Hilbert pairing. The newly named background and transport excess are

    B = 2 E2 L2 A - E2^2 (L0 D3 + E0 H),
    N = -2 E2 T2 A + E2^2 T0 D3
      = -2 E2 T2 A        (on physical H3 slices).

The Lean theorems identify, **unconditionally on each strict energy-class slice**,

    X = B + N,             R' = -(B + N) / A^2.

`B` deliberately retains `H = D3'` with its full physical forcing: it is a *diffusion/Hilbert background*, not pure linear heat dissipation. To split its forcing into linear diffusion and nonlinear Leray product requires the separate fourth-radial PDE closure and is the next substantive task. We do not claim a sign for B or N.

## Forced nonlinear transport burden

The exact mean-value/secant theorem and near-Young estimate yield an interior witness `r` with

    [R(s) - 256 δ/(27 K^4 E0(t))] / (t-s)
      <= [B(r)+N(r)] / (E0(r)D3(r))^2.

If a **separately proved or explicitly hypothesized** upper bound `B(r)/(E0(r)D3(r))^2 <= M` holds on the whole interval, the actual order-two transport must satisfy somewhere inside `(s,t)`:

    - 2 E2(r) T2(r) / [E0(r)D3(r)]
      >= [R(s)-256 δ/(27 K^4 E0(t))]/(t-s) - M.

No terminal regularity or transport-rate ceiling is inferred from the sign algebra. The analytic frontier is bounding the actual Hilbert fourth-radial forcing component of B and determining whether the order-two nonlinear transport can compensate it near the hypothetical terminal sequence.

## Audit and build

The registrar adds the module import to `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`, with `#check` and `#print axioms` for two definitions and six theorems. Regenerate `proof/order.txt`, run fragment verification, compile the module and central audit, build the library, and run baseline audit before push. No `sorry`/`admit`, new axioms, or new class hypotheses are introduced for the physical identity.
