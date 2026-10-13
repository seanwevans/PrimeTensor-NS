# Quantitative physical L² initial trace from scalar Schwartz momentum

Base: `9208a56d` — initial Schwartz weak trace from scalar FTC and physical energy.

For any physical Hilbert vectors `V`, prescribed `U`, and spatial test `ψ`, an **approximate** kinetic ceiling and one physical norm bound imply

    ‖V-U‖² ≤ e + 2(|⟪V,ψ⟫-⟪U,ψ⟫| + (B+‖U‖)‖U-ψ‖)

whenever `‖V‖² ≤ ‖U‖²+e` and `‖V‖≤B`.

For an actual H³-admissible old physical velocity, the previously audited initial integrated kinetic budget gives the time-dependent energy error

    e(t) = ∫₀ᵗ |r(s)| ds

and a finite norm ceiling `B = sqrt(E₀(0)+∫₀ᵇ |r|)`. Each Schwartz test Φ has its own interval-integrable real scalar initial momentum source `gΦ`, so the initial paired difference equals `∫₀ᵗ gΦ(s)ds`. Combining these ingredients gives an explicit **finite-time** physical initial squared L² error bound.

An additional sharper theorem uses the already-proved *exact* kinetic ceiling to remove the kinetic-error primitive and replace `B+‖U‖` with `2‖U‖`. The first estimate itself does **not** depend on positive-time kinetic antitonicity or strong initial time convergence.

No single physical L²-valued time derivative, uniform-in-Schwartz source modulus, spatial Schwartz approximation rate, or subcritical H³ energy majorant is assumed. Initial-anchored L¹ kinetic budget and scalar Schwartz initial equations remain explicit PDE-facing assumptions; this is not a proof of unconditional Navier–Stokes regularity.

## New public declarations

- `h3Audit_initialHilbert_approxProbeSquaredDefect_of_energyError`
- `h3Audit_initialSchwartzScalarFTC_quantitativePhysicalSquaredError`
- `h3Audit_initialSchwartzScalarFTC_quantitativePhysicalSquaredError_exactCeiling`

## Build rule

Run the idempotent registration script, then `python3 proof/generate_index.py` and `python3 proof/generate_index.py --check`, **before any Lean build**. Include the resulting `proof/order.txt` in the commit. Run the root, contracts and full build before pushing.

The patch is not Lean-compiled in the artifact environment; compilation must be verified with Lean 4.34.0-rc1 on Rocky Linux.
