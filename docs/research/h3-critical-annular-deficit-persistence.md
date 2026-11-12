# Actual annular deficit: kinetic continuity and one-snapshot physical viscous windows

Base: `8529ac84b69966a2a54a7613cf66c0da0c2ac0bb` — charge annular kinetic deficits to unconditional truncated physical viscous clocks.

## New mathematical bridge

For each **fixed** cutoff radius `rho`, the actual three-component physical sharp highpass `Q_rho=I-P_rho` is 1-Lipschitz on real physical `L²`. The scalar cutoff already satisfies `P_rho(f-g)=P_rho(f)-P_rho(g)` and has norm at most one; the accepted physical three-vector highpass estimate gives `‖Q_rho(V-W)‖≤‖V-W‖`. Since the actual physical Hilbert velocity `U(t)` is norm-continuous for every strict physical time, the actual highpass kinetic mass `M(t,rho)=‖Q_rho U(t)‖²` is continuous without new PDE assumptions, uniform terminal bounds, or a moving-cutoff theorem.

The exact annular deficit has the algebraic decomposition

    Delta(t) = rho^6 * (rate*M(t)-B)^2
               - M(t)*(YoungWidth(t)+rho^6*OuterBase),
    rate = (rho^2+sigma^2)/2,
    B = sqrt(E0(b)) * 3*KineticLowBandSourceCeiling(rho,E0(b)),

where `YoungWidth(t)` is the *actual* annular nonlinear Young-gap and frequency-width integral from the accepted annular dichotomy. Hence **continuity of YoungWidth at x alone** gives continuity of Delta at x; highpass mass continuity is already derived from the physical path.

A strict single-time kinetic excess `B<rate*M(x)` and doubled deficit floor `2 epsilon ≤ Delta(x)` with `epsilon>0` now give a physical right window `[x,x+delta]`, `delta>0`, `x+delta<T`, where both the nonstrict kinetic excess and floor `epsilon≤Delta(t)` persist. The previous PDE result and the canonical cap choice `H=epsilon` force

    epsilon / max(1, E0(b)*rho^6*Slope(b,epsilon)) ≤ D3(t)

at *every time* on that window. Finite physical dissipation gives the real clock

    delta * epsilon / max(1, E0(b)*rho^6*Slope(b,epsilon))
        ≤ integral(a,T,D3).

The same canonical cap choice removes the user-prescribed cap sequence from the countable disjoint summability statement, yielding summability of `delta_k*epsilon_k/C(b,rho_k,epsilon_k)` whenever the selected disjoint windows satisfy the precise kinetic persistence premises.

## Exact open obligation

This patch **does not** prove the physical-time continuity of `thirdFullPhysicalActualAnnularYoungWidthCost244`, i.e. the Fourier nonlinear Young-gap/width integral. That continuity is explicitly assumed at the chosen strict observation time in the one-snapshot theorem; it is *not* replaced by continuity of viscosity, an abstract surrogate, or a continuity assumption on the entire deficit. Establishing nonlinear cost continuity from the actual strongly continuous spectral state and annular weighted Fourier estimates is the next analytic goal. Even after that, local positive widths do not yield a uniform or quantitatively summable cofinal width estimate. There is no Navier–Stokes global regularity or terminal H3 continuation claim.

## Verification

The registrar rejects `sorry`, `admit`, and new axioms and registers kernel axiom audits. Run `lake build` and `lake env lean` on the user's pinned Lean/mathlib environment; source checks are not Lean kernel compilation. No external assumption is silently removed.
