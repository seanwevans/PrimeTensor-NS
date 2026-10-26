# Finite-annulus physical-PDE gradient transfer (244)

Base commit: `a70c4151`.

The actual physical PDE already controls its L² momentum increments. The prior radial Plancherel proof controls the corresponding weighted H³ spectral *square defect* below every fixed radius. This increment introduces the exact bounded Fourier gradient multiplier from the low-radial dissipation proof and obtains the additional `(ρ + 1)^2` factor for the three squared gradient-increment norms.

For source ceiling `C` on `[s,t]`, and nonnegative `ρ`, the bound is

`Σ_j ‖Mρ(G_j(s)-G_j(t))‖² ≤ (ρ+1)² · 3 · (1+ρ²+ρ⁴+ρ⁶) · (C(t-s))²`.

An independent H³ energy ceiling produces `C = (3 + C_Leray) E`. Both cutoff radii can be combined in one finite-annulus estimate. No temporal H³ derivative or uniform terminal rate is asserted.

**Next analytic proof:** polarize these genuine localized Hilbert increments against bounded snapshots to bound changes in the finite-annulus dissipation quadratic. That will make the PDE source control the window persistence budget.
