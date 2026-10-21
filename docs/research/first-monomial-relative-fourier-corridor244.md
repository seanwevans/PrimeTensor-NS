# Intrinsic scale-relative Fourier corridor under sharp Young near-saturation

Base checkpoint: `e00ca2e3` — moving physical Fourier-frequency corridor.

## New normalization

The existing physical Fourier moment definitions give `E0=∫S`, `E2=∫q²S`, `D3=∫q⁴S` where `q(ξ)=(2π)²|ξ|²`, together with first-Cauchy defect `F1=E0 D3-E2²` and exact variance `E0 F1=∫(E0 q²-E2)² S`.

Earlier, an arbitrary unnormalized corridor radius `ρ` yielded

    27 K⁴ ρ² M_far(ρ) ≤ 256 E0 D3 Δ_Y,

where `Δ_Y = D3 + (27/256) K⁴ E0 - K E3` and positive `D3` is assumed.

For positive `E0,D3` and `ε≥0`, choose

    ρ(t,ε) = ε sqrt(E0(t) D3(t)).

This choice makes the actual Fourier event equivalent to the dimensionless deviation

    |q(ξ)² - E2/E0| ≥ ε sqrt(D3/E0).

The product `E0 D3` cancels *exactly*, yielding the division-free budget

    27 K⁴ ε² M_far(t, ε sqrt(E0 D3)) ≤ 256 Δ_Y.

With `K, ε, E0>0`, the **fraction of physical Fourier mass** outside the relative corridor satisfies

    M_far/E0 ≤ 256 Δ_Y / (27 K⁴ ε² E0).

This estimates concentration relative to the actual moment scale, rather than using fixed dimensional frequency windows. The precise Fourier measure and density are inherited from the preceding modules. A Landau-specific theorem instantiates `K=4398 C1 sqrt(E)` using the already established positivity of `C1` and `E≥1`.

## Mathematical frontier

A small *normalized* Young gap `Δ_Y/(K⁴ E0)` is enough to constrain normalized Fourier mass outside every fixed relative corridor. No result here asserts that the Navier--Stokes dynamics make that normalized gap vanish. Even if it does vanish, concentration may occur in a narrowing annulus; excluding the terminal scenario requires PDE information (signed Fourier transport / radial dispersion) unavailable from these algebraic moment bounds alone.

## Audit and build

Use the registrar, regenerate `proof/order.txt`, run fragment checks, compile the new Lean module and central audit, build all targets, and check the baseline before committing. All theorem bodies are explicit; no axioms or placeholders are introduced in the patch.
