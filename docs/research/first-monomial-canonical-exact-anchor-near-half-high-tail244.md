# Exact-anchor half-height persistence charge and near-half high-tail concentration

Base commit: `d9d0106e` — force canonical H3 half-gap PDE budget and high-tail concentration.

## New mathematical step

Use the **same original** canonical first-crossing witnesses `(τ,N,K,C,δ,v)` and their exact quadratic-sharp PDE clocks. Define `D_k=D₃(τ(vk))`, `Q_k=N(vk)+1`, `H_k=H_{Q_k}(U₃(τ(vk)))`, and `I_k=∫_{τ(vk)}^{τ(vk)+δ(vk)}D₃(s) ds`.

The previous checkpoint proved the one-cutoff LOW-Q PDE budget `B_k=Λ_Q δ+Ξ_Q δ² < D_k/2`, with `Λ_Q, Ξ_Q` built from the exact spectral anchor and attained actual projected-source ceiling. The physical one-cutoff radial partition `D=L_Q+H_Q` and the source-driven anchored PDE modulus `|L_Q(τ(vk))-L_Q(s)|≤B_k` imply, for **every** `s` in the same exact original window,

    D₃(s) ≥ D_k-H_k-B_k > D_k/2-H_k.

No continuity or modulus for the untruncated full H3 dissipation is assumed: only the already proved actual low-Q modulus and the nonnegativity of the high-Q tail are used.

Integrating the full *physical* dissipation produces the new quantitative charge:

    δ_k (D_k/2 - H_k) ≤ I_k.

The previously proved disjoint full-dissipation integrals are summable, hence `I_k→0`. Therefore for each fixed real `β<1/2` and each `ε>0`, eventually

    δ_k D_k ≤ ε   OR   β D_k < H_k.

The earlier theorem had a fixed threshold β=1/4. This version permits **every** fixed β strictly below half, with no new source-action or width hypothesis and no re-selection of anchors. If `δ_k D_k≥η>0` eventually, the second arm eventually holds for each β<1/2, implying a physical high-tail fraction with liminf at least one-half (the Lean theorem uses the universally quantified eventual threshold form instead of assuming a uniform ratio limit).

The proof does **not** establish positive lower persistence of `δ_k D_k`; it isolates that remaining branch. It also does not assert the strict endpoint fraction β=1/2 or global Navier–Stokes regularity.

## Declarations

- `h3Path_scalar_lowPDEVariation_forces_fullPlateau244`
- `h3Path_physicalPDE_outerLow_forces_fullPlateau244`
- `h3Path_physicalPDE_halfHeightDeficit_integratedCost244`
- `h3Path_scalar_halfHeightDeficit_chargeOrHighTail244`
- `h3Path_noL2Trace_exactAnchor_halfHeightChargeOrNearHalfHighTail244`

The ZIP and registrar were statically checked. Pinned Lake compilation is not available in the packaging environment.
