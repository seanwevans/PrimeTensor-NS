# H³-Cauchy Schwartz completion: signed transport invariance (244)

Checkpoint: `9b5c4d47` (`fix H3 energy Cauchy square bound normalization`).

The signed 243-slot Schwartz first monomial has a real limit for every sequence
whose *actual order-two and order-three energy differences* are Cauchy-small.
The present module selects that real limit and proves **stability under a
vanishing cross-family mixed jet graph**. The latter is a sufficient analytic
condition on approximating families, not an assumed equality of nonlinear
observables.

## Quantitative estimate

For actual third-derivative L² and both second-derivative L⁴ roots bounded by
`K`, the real trilinear perturbation inequality implies each spatial slot
error is at most `3 K² G(f,g)`; summing 243 slots and retaining the physical
factor two gives

`|M(f)-M(g)| ≤ 2∑slotError ≤ 6 card(Slots) K² G(f,g)`.

For two E₂/E₃-energy-Cauchy Schwartz families, the earlier automatic root
boundedness theorem supplies one common finite K. If their cross-family mixed
graph tends to zero, the signed monomial values converge to the same real
number. This proves uniqueness of the completed observable with respect to
that explicit strong-graph approximation relation.

## Deliberately remaining

1. Derive cross-family mixed-jet graph convergence from the ordinary Sobolev
   H³-distance between *different* approximating families.
2. Construct Schwartz approximating families for each eligible physical H³
   Sobolev velocity and show that the relevant physical path is included.
3. Identify the extended signed first monomial with the original physical
   trilinear pairing and handle the top-dissipation/E₄ transfer separately.

No density, physical identification, continuation criterion, or regularity
claim is inferred solely from the completion result.
