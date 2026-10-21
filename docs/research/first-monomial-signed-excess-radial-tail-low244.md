# Actual signed H³ spectral production: radial heat, Leray, and low complement

Base commit: `bec218fc` — split the physical H³ Fourier signed excess into diffusion/Hilbert background and nonlinear transport.

## Analytic input and exact identity

Earlier the full top dissipation is differentiable on every strict class interval, with a physical fourth-radial Hilbert derivative `D3_prime`. Independently, `h3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint_closed` proves an exact evolution for every natural high-radial tail `Tail_n`, with cutoff `n+1`:

    Tail_n' = Heat_n + Leray_n,
    Heat_n = -2 ∫_{|frequency| >= n+1} q^5 S <= 0.

Introduce the **actual low-frequency complement** `Low_n = D3 - Tail_n`. Its derivative is closed without any new temporal hypothesis:

    Low_n' = D3_prime - Heat_n - Leray_n,
    D3_prime = Heat_n + Leray_n + Low_n'.

Combine with the already proved order-zero transport cancellation and order-zero/order-two diffusion–transport–pressure split. Set `A=E0*D3`, `L_j` the actual lower diffusion pairing and `T2` the order-two transport pairing. The exact physical signed excess becomes

    X = H_n + N_n + Z_n,
    H_n = 2 E2 L2 A - E2^2 (L0 D3 + E0 Heat_n),
    N_n = -2 E2 T2 A - E2^2 E0 Leray_n,
    Z_n = -E2^2 E0 Low_n'.

Every one of these terms is constructed from the already closed physical PDE quantities and differentiated spectral paths. There are no new assumed estimates or axioms. In particular this is **not** a claim that `Low_n'` is negligible, or that the global `D3'` is pure heat + Leray at fixed positive cutoff. Removing / controlling the low-complement term is the next genuine analytic seam.

## Near-Young secant

The existing exact signed secant, together with `R(t) <= 256 δ/(27 K^4 E0(t))` when the physical Young gap is at most δ, produces an interior `r` with

    [R(s)-256 δ/(27K^4 E0(t))]/(t-s)
       <= [H_n(r)+N_n(r)+Z_n(r)]/[E0(r)D3(r)]^2.

The result holds at every **fixed** natural radial cutoff n, including the strict-time low complement, under the usual positive-mass and dissipation hypotheses. No global regularity conclusion or transport majorant is asserted.

## Audit and compilation

Run the registrar; regenerate the proof index, check fragments, compile the module, compile the central FirstMonomialTriad audit, run a complete build and the baseline. `#check` and `#print axioms` are generated for all four definitions and five theorems.
