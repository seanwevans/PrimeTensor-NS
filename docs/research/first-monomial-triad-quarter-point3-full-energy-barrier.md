# Full H³ quadratic absorption barrier at the real Schwartz witness

Parent: `32820000` (*prove cubic first-monomial scaling against quadratic H3 dissipation and refresh source index*).

The committed 243-slot real `Point3` first-monomial has cubic velocity homogeneity and the committed four-derivative Schwartz dissipation has quadratic homogeneity. This module adds the zeroth-, first-, second- and third-order derivative square integrals that constitute the unnormalized componentwise H³ energy on real Schwartz fields. It proves exact degree-two scaling for every order and their total.

A stronger general lemma applies to *any* degree-two homogeneous functional `Q`, any coefficient `C`, and any additive real constant `K`. At a sufficiently large positive amplitude of the existing positive, solenoidal real quarter packet, the cubic signed first monomial exceeds `C * Q + K`. The constructive amplitude is `(abs (C * Q f) + abs K + 1) / M + 1`, where `M > 0` is the previously proved physical first-monomial value.

The concrete application rules out a universal fixed-coefficient inequality

```
M(v) ≤ ε D4(v) + C (1 + E_H3(v))
```

holding for *all* real divergence-free Schwartz velocity snapshots, where `E_H3` sums all four squared derivative orders and `D4` is the ordered four-derivative square from the previous module. `1` is the normalization already present in PrimeTensor's canonical `velocityH3EnergyAt`. This does **not** prohibit inequalities with coefficients depending on `E_H3` or other nonlinear powers, or inequalities on bounded-energy classes. No Navier–Stokes solution is constructed, and no global regularity or singularity statement follows.

## Verification

Register the new module in `PrimeTensor.lean` and the first-monomial audit. Refresh `proof/order.txt` using `python3 proof/generate_index.py`, run `--check`, validate fragments, then compile the module and root/audit contracts, build the entire project, and commit the refreshed source index. Lean/mathlib are not installed in the patch preparation environment; local compilation is the required verification gate.
