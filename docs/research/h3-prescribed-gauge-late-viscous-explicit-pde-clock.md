# Prescribed-gauge late viscous spikes: an explicit physical-PDE clock

**Base commit:** `b738ec4fe53c19e02228222f99d339664384fe33`.

## Analytic advance

The previous committed terminal alternative promoted an actual late viscous spike to a finite radial capture and an unspecified positive persistence duration. This patch replaces the abstract continuity radius by an explicit duration computed using the established projected-Navier--Stokes finite-cutoff gradient variation estimate.

For a genuine physical late time `r` and finite cutoff `J`, assume `0<V<P D_{<J+1}(r)`, with `m<r<T`. On `[r,r+(T-r)/2]`, the *actual* projected source norm and weighted spectral-state norm attain maxima `C` and `K`. Set

```
A = V/(2P) > 0
Lambda(J,K,C) = 6 (J+2)^2 K sqrt(3 W3(J+1)) C
eta = min ((T-r)/4) (A/(2*(Lambda+1))) > 0
```

The actual physical Fourier-PDE estimate controls low-radial dissipation variation by `Lambda*(s-r)`; the retained margin between the captured height `V/P` and the desired floor `A=V/(2P)` gives

```
A < D_<J+1(s) <= D_full(s)  for all s in [r,r+eta]
eta*A <= integral_m^T D_full(s) ds
```

The same theorem transports this quantitative clause to the *existing* arbitrary-gauge minimal first-crossing witnesses, while retaining their four-way physical alternative, disjoint finite viscous charges, and diverging outer-to-gauge ratio.

## Exact assumptions and limitations

- `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, and interval-integrability of **full** physical H3 dissipation are maintained from the parent theorem.
- `J` is a finite cutoff selected by the previously established radial capture; the new PDE rate depends on `J`, on two attained maxima, and on remaining terminal time.
- No terminal-uniform estimate on `J`, `K`, or `C` is obtained. The rate can diverge, so the new clock can be arbitrarily compressed.
- New late persistence intervals are **not** asserted disjoint and are not identified with the original anchored minimal annulus windows.
- This is a necessary cascade barrier, **not** a Navier--Stokes continuation theorem.

## Verification

Run the registrar with `--apply` then `--check`, regenerate the index with `proof/generate_index.py`, compile the Lean module, build the dependent root and audit, and run the existing baseline. Static ZIP and registrar checks do not replace Lean elaboration.
