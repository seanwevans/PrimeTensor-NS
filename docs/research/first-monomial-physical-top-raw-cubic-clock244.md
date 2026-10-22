# Raw physical cubic forcing clock: avoid division by top dissipation

Baseline `87ae60f8` — normalized physical top cubic terminal criterion and forcing spikes.

## The stronger unnormalized PDE mechanism

The exact Hilbert/Fourier PDE supplies `D3′ + M5 + P = M3` where `M5 ≥ 0` and the signed phase remainder `P ≥ 0`. Therefore `D3′ ≤ M3` pointwise. Unlike the logarithmic/cubic ratio bound `(log D3)′ ≤ M3/D3`, this statement has **no positivity assumption on D3**.

The actual third-radial Leray forcing mass profile `M3(r)` is continuous on every strict H3 energy-class interval, so it is integrable on compact intervals. By taking a compact forcing ceiling K and applying the one-sided derivative integrability theorem to `K*r-D3(r)`, the derivative `D3′` is itself interval integrable; no continuity of the derivative is presumed. The ordinary FTC proves:

    D3(t) ≤ D3(s) + ∫_s^t M3(r) dr.

The resulting conditional physical top-moment criterion states that a bounded cumulative raw cubic mass action implies a bounded physical top moment, with no requirement that D3 remain positive.

## Terminal consequences

If D3 is unbounded on a finite strict terminal subtail, the *unnormalized* cumulative cubic mass action must be unbounded. Moreover, the pointwise derivative-ceiling/mean-value theorem gives a stronger necessary source condition:

    for every K, there exists r in (s,T) with M3(r) > K.

The forcing profile is exactly `(2*pi)^6 * sum_{j:Fin 3} ||third-radial-Leray-forcing_j||_2^2`, and the patch packages its necessary unboundedness as a separate spectral statement.

This unnormalized forcing escape is stronger in one respect than the earlier ratio escape: a large M3/D3 caused only by D3 being small does not qualify. It is the actual Fourier third-radial Leray forcing norm-square mass that must become unbounded. Both conclusions hold without a lower bound for D3.

These are **necessary conditions**, not an unconditional exclusion of Navier–Stokes singularity. The deeper task is to use the existing nonlinear spectral product, kinetic budget, and moment hierarchy to prevent the required raw forcing mass explosion (or show it is incompatible with a canonical endpoint).
