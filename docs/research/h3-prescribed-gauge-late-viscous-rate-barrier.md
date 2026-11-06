# Prescribed-gauge late H³ viscous source: terminal-time compression or physical PDE rate

**Base commit:** `6ae9011a94990973f434e0e46cdd705f7f7038cd`.

## New quantitative consequence of the exact Navier–Stokes clock

The established prescribed-gauge construction produces an actual late physical
H³ dissipation spike at `r_k` after the midpoint
`m_k=(tau(v k)+T)/2`. The prior module selected a finite low-radial cutoff
`J_k`, attained strict-time physical source/state maxima, and an exact PDE
persistence width

    A_k      = H(v k)^4 / (2 P_k) > 0,
    P_k      = 168 Q_k^4 ||F|| (3+C_L) (T-m_k) > 0,
    Q_k      = N(v k)+2,
    Lambda_k = 6 (J_k+2)^2 K_k sqrt(3 W_3(J_k+1)) C_k >= 0,
    eta_k    = min ((T-r_k)/4) (A_k / (2 (Lambda_k+1))),
    B_k      = integral_(m_k)^T D_H3(s) ds,
    eta_k A_k <= B_k.

The new algebraic `thirdFull_scalar_minPDEClock_timeOrRate244` eliminates the
auxiliary clock and proves the alternative

    (T-r_k) A_k <= 4 B_k
       or
    A_k^2 <= 2 (Lambda_k + 1) B_k.

The first arm is a **terminal-time compression charge**. The second arm is a
**physical projected-PDE rate barrier**. In the second arm a vanishing terminal
viscous tail can support a fixed positive normalized spike only when the
actual cutoff-sensitive physical PDE variation rate grows.

## Lean witness transfer

`thirdFullPhysical_noH3Trace_prescribedGauge_lateRateOrCompression244`
retains the existing witnesses `U, tau, N, K, C, delta, v`, the exact original
minimal first-crossing windows, finite disjoint viscous charge sum and outer
gauge-frequency escape. The first three Fourier/source/kinetic alternatives
are untouched. The fourth is strengthened by the displayed rate-or-compression
alternative at the same actual late peak with attained maxima.

The previous terminal dissipation tail tends to zero. Nothing here bounds
`J_k`, `K_k`, `C_k`, or `Lambda_k` uniformly, bounds `(T-r_k)` below, or
forces an inadmissible terminal trace. A global continuation conclusion is
not claimed.

## Verification

Run the registrar `--apply`, `--check`, generate the proof index, check the
fragment, compile the new Lean module, build the root, and run the baseline
audit in the pinned local Lean/mathlib environment. The bundled proofs have
not been compiled in the packaging environment.
