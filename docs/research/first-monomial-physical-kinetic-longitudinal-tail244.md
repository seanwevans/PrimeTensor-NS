# Physical kinetic longitudinal/transverse terminal-tail action

Baseline: `34be75bf`, module: `FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticLongitudinalTail244`.

From the exact source split `R = P + Q` with `P=-(D0/E0) U` and
`<U,Q>=0`, the strictly positive terminal kinetic mass `L` supplies

`||P(t)|| = D0(t)/sqrt(E0(t)) <= D0(t)/sqrt(L)`.

All of `U`, `R`, `E0`, and `D0` are continuous on strict positive times.
Consequently both `P` and `Q` are strongly continuous on `(a,T)` whenever
`L>0`; their norms are integrable on every closed strict subinterval.

The new source action bound is

`integral_s^t ||R|| <= integral_s^t ||Q|| + (E0(s)-L)/(2 sqrt(L))`.

By the already closed positive-time physical Hilbert FTC,

`||U(t)-U(s)|| <= integral_s^t ||Q|| + (E0(s)-L)/(2 sqrt(L))`.

Thus the longitudinal component becomes uniformly negligible in the terminal
tail as `s -> T-`, while a transverse time-action criterion would suffice
for terminal physical L2 Cauchy convergence. This patch does *not* assert
such a criterion; it does not bound `D3` or prove NS continuation.

The original physical source/kinetic identities inherit selected physical
evolution from the earlier curl weak-FTC chain; there is no independence claim.
