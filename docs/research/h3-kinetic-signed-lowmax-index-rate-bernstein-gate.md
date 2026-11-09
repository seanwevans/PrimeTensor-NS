# Exact index-rate Bernstein gate for physical signed sixth flux

**Pinned base:** `17877d1b5a153c1ea7de0f68ea79964460285dec` — first excluded adaptive shell.

## Main result

On the original separated kinetic gaps write

- `D(k) = ∫_[x_k,y_k] velocityH3DissipationAt(u,r) dr`, with `x_k = tau(v k)+delta(v k)` and `y_k = tau(v(k+1))`;
- `h = eta / (8 * (thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 E + 1)) > 0`, at fixed actual H3-energy cap E;
- `L_j(E0) = thirdFullPhysicalKineticLowBandDissipationRate244 j E0`, with the genuine earlier kinetic anchor `E0=velocityH3Energy0At u b`;
- `C_k(E0) = 1 + 2*sum_{j=0}^k L_j(E0)`.

The accepted adaptive gauge is

`G(k) = Nat.findGreatest (fun j => 32*C_j(E0)*D(k) < h^2) k`.

If the INDEX itself is affordable, `32*C_k*D(k) < h^2`, the largest affordable gauge equals k. This avoids inferring anything unjustified from convergence of G(k): it is a direct application of the exact maximality selector. Conversely G(k)<k forces `h^2 <= 32*C_k*D(k)`.

Intersecting this scalar gate with the accepted adverse signed-sixth-flux theorem gives, on all sufficiently late ORIGINAL kinetic gaps, every qualifying adverse physical time and inner radius R with the accepted tenth-power residual excluded:

1. `(y_k-x_k)*h <= 16*D(k)` (positive relative physical H3 dissipation);
2. `h^2 <= 32*C_k(E0)*D(k)` (the **index-k kinetic Bernstein/source rate** is paid);
3. `exists Q >= R, k < Q` (a genuine certified finite outer annular cutoff past the kinetic-gap index).

For the second branch the proved positive scalar normalization gives
`D(k) >= h^2/[32*C_k(E0)] > 0`. Thus the obstruction identifies a concrete lower price in real physical H3 dissipation, rather than only an abstract "high rate".

## Exact physical Bernstein/source decomposition

The new lemma checks the existing finite-band physical rate algebraically:

`L_j(E0) = 6*(j+2)^2 * W_j^2 * sqrt(E0) * S_{j+1}(E0)`,

where `W_j=thirdFullFiniteBandH3WeightCeiling244 j`, and
`S_{j+1}=thirdFullPhysicalKineticLowBandSourceCeiling244 (j+1) E0`.

The latter contains the genuine Fourier-ball measure, not a Schwartz approximation or invented volume bound. No monotonicity of `L_j` and no polynomial Fourier-ball-volume estimate is assumed.

## Remaining hard-math obstruction

Convergence `D(k)->0` alone does **not** imply `C_k(E0)*D(k)->0` since the cutoff k grows. The next useful direction is to prove or refute a suitable frequency-dependent envelope for the actual source Bernstein term and compare it with the physical dissipation decay. Nor is the positive relative-density branch excluded. The result is a conditional necessary obstruction, not global H3 Navier–Stokes regularity.

## Verification

The registrar checks seven theorem names and their axioms in the central audit. Use `proof/generate_index.py` and the repository's pinned Lean/Lake toolchain before committing. Static checks on the archive do not establish kernel elaboration.
