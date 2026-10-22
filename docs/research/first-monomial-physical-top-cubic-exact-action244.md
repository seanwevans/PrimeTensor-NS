# Actual physical cubic-forcing action and dissipative fifth/phase balance

Base checkpoint: `cee866a0` — bound physical top replenishment by signed cubic forcing action.

## Exact signed PDE budget

Write `D3` for the genuine fourth-radial top Hilbert dissipation, `M5` for the fifth velocity Fourier square mass, `M3` for the third-radial nonlinear Leray forcing square mass, and `P` for the exact, nonnegative Fourier phase defect.

The committed physical PDE identity reads

    D3'(r) + M5(r) + P(r) = M3(r).

For `D3(r)>0` this becomes

    M3/D3 = (d/dr) log D3 + M5/D3 + P/D3.

Integrating on a compact strict energy-class interval produces the **exact** identity

    integral_s^t M3/D3
      = log D3(t) - log D3(s) + integral_s^t M5/D3 + integral_s^t P/D3.

Both `M5/D3` and `P/D3` are nonnegative; the signs are not discarded. The cubic forcing ratio is also identified with the third-radial physical Leray Fourier L2 norm-square realization already established by the terminal forcing program.

## Automatic compact-time normalized forcing integrability

The existing `h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn` establishes continuity of the full cubic forcing mass on every strict energy-class interval. The physical top-dissipation mass path is differentiable, hence continuous, on the same interval. On `[s,t]` with `D3>0` this supplies continuity and **automatic interval-integrability** of `M3/D3`. No independent normalized cubic integrability hypothesis is needed in the new near-Young theorem.

Separate integrability assumptions for the signed logarithmic rate, normalized fifth and phase losses, and the other physical FTC source channels are retained. The proof does not assert terminal-time L1 integrability of the cubic forcing or those sources.

## Near-Young normalization cancels the endpoint top logarithm

The previous near-Young forcing obstruction was

    R(s) - 256 δ/(27 K^4 E0(t))
      - [log E0(s)-log E0(t)]
      - 36 integral_s^t C1 sqrt(E_H3)
      - [log D3(s)-log D3(t)]
      <= integral_s^t M3/D3.

Substituting the exact cubic action identity cancels the `D3` endpoint logarithms **exactly**, leaving

    R(s) - 256 δ/(27 K^4 E0(t))
      - [log E0(s)-log E0(t)]
      - 36 integral_s^t C1 sqrt(E_H3)
      <= integral_s^t M5/D3 + integral_s^t P/D3.

Thus the purely necessary concentration mechanism involves finite-time expenditure in the normalized fifth velocity and nonnegative phase-defect channels. Crucially, this is a **lower** bound on the cost, not an upper bound that could exclude a singularity.

## Next analytic problem

An actual continuation argument would require an upper bound or suitable absorption mechanism for the normalized fifth-plus-phase action, while also proving time integrability of the remaining physical derivative profiles. Presently neither is claimed. The two-band heat construction explains why an instantaneous concentration rate is insufficient by itself.
