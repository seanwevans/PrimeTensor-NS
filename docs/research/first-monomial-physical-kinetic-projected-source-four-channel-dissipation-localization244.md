# Four-channel moving-radial H³ dissipation localization (2026-10-25)

Base: `e201f3b2` (`localize fast physical H3 decay dissipation above moving radial cutoff`).

## What is proved

Under `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, positive canonical terminal kinetic mass, and the explicit failure of a strong physical L² terminal trace, the already-proved fixed cofinal four-channel alternative reduces to **one existential terminal sequence**, with `R_n = n+1`, `τ_n ∈ (a,T)`, `dist(τ_n,T) < 1/R_n`, and `τ_n → T`, satisfying

    R_n D_low(R_n, τ_n) < D_high(R_n, τ_n)
    D_high(R_n, τ_n) / D_total(τ_n) → 1.

The `D_low` and `D_high` functions are actual Fourier integrals of the full physical H³ dissipation density, with `D_total = D_low + D_high` proved exactly. They are NOT weighted H³ mass. The elementary share theorem uses `R_n L_n < H_n` and `L_n ≥ 0`, giving `0 ≤ L_n/(L_n+H_n) < 1/(R_n+1)` and hence the stated limit.

The fast negative-slope branch provides the dissipation dominance directly. The high-energy branch and both negative canonical cubic branches first provide high-radial H³ mass dominance, and its **pointwise** implication yields the same dissipation inequality on the selected sequence. No intersection of distinct cofinal sets is used.

A neutral result, from H³ admissibility and energy class alone, states the disjunction of a strong physical L² terminal trace with its exact canonical kinetic mass, or the localized dissipation sequence.

## Scope

This is a necessary conditional terminal-frequency alternative, **not** unconditional smooth H³ continuation or Navier–Stokes regularity. The no-trace branch is not inferred from nonextension. In particular, fast direct-viscous snapshots are not asserted to have high-radial weighted H³ energy-mass dominance.
