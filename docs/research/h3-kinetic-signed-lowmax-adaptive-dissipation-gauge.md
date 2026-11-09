# Adaptive unbounded kinetic gauge from actual cofinal H3 dissipation

**Pinned base:** `090e0570c9ae485bd3d7b8c0b93bce7a0f36183e`.

## Hard mathematical distinction: fixed-gauge vs moving-gauge quantifiers

The accepted signed sixth-flux theorem gives for every **fixed** natural
frequency gauge `G` an eventually valid relative-H3-dissipation versus
outer-annulus escape. The index at which it holds may depend on `G`.
It is invalid to substitute an arbitrary growing function `G(k)` into
this `forall G, eventually k` result without a diagonal construction.

The new construction starts with the ACTUAL physical H3 gap dissipation

`D(k) = integral_(tau(v(k))+delta(v(k)))^(tau(v(k+1))) D3(t) dt`,

which tends to zero by the existing cofinal separated-gap theorem. Fix
`eta>0`, an actual physical H3-energy cap `E>=0`, and the positive
linear viscous floor

`h = eta / [8*(A(E)+1)] > 0`, `A(E)=((2*pi)^7/3)*1944*C1*(E+1)`.

With the fixed earlier kinetic anchor `E0 = velocityH3Energy0At(u,b)`, define

`C_G = 2*sum_(j=0)^G L_j(E0) + 1 > 0`,

where `L_j` is the already-established true physical kinetic-only
finite-low-band dissipation Lipschitz coefficient.

**The new adaptive gauge** is the maximal affordable index

`G(k) = max { G in natural numbers : G<=k and 32*C_G*D(k) < h^2 }`,

with fallback zero if there is no such `G`. It is represented by
`Nat.findGreatest` with an explicit bound `k`, not a choice of an unknown
uniform late-gap threshold.

## Three exact mathematical properties

1. `G(k) <= k` by definition, so the gauge cannot anticipate future indices.
2. For each fixed natural `m`, `32*C_m*D(k) -> 0`; hence for all late
   enough `k>=m`, that `m` belongs to the affordable set. As a result,
   `G(k) -> infinity` with **no monotonicity premise** for `C_m` or `G(k)`.
3. In particular, the candidate `m=0` belongs to the affordable set for
   sufficiently late `k`. The greatest-member theorem then proves that
   the **selected** `G(k)` satisfies `32*C_(G(k))*D(k) < h^2`.

The third property is important: the definition does not merely assert
existence of an unknown affordable gauge; it actually selects and verifies
one gauge on the original kinetic gap.

## Physical transport consequence

For any sufficiently late original gap and **every** natural inner radius
`R` and physical observation `t in [x_k,y_k]`, assume the accepted true
high-radial gamma-free carrier and actual energy cap `E3(t)<=E`. Then

`(y_k-x_k)*h <= 16*D(k)` **or** `exists Q>=R, G(k)<Q`.

The same single adaptive gauge works simultaneously for the permitted
observations at that gap. The global `Tendsto G atTop atTop` is proved in
Lean rather than assumed. A separate theorem starts from the original
signed sixth-flux adverse physical sample and excludes the explicitly
retained tenth-power residual; it then supplies the identical alternative.

If a witness sequence `Q(k)` can be selected above the adaptive gauge on
all sufficiently late gaps, another proved lemma shows `Q(k)->infinity`.
The lemma does not assume such adverse samples or a selection exist.

## What's still unresolved

Finite total H3 dissipation alone does **not** imply that the relative
average `D(k)/(y_k-x_k)` tends to zero. Consequently the first branch
may persist despite `D(k)->0`, and the theorem does not establish
unconditional spectral escape or Navier--Stokes continuation. The
remaining hard problem is to control this positive relative-density
mechanism from the genuine signed Navier--Stokes transport and physical
kinetic-window geometry, not to assume a uniform clock width.

## Verification and registration

Run the accompanying idempotent registrar, `proof/generate_index.py`
with `--check`, targeted Lean elaboration and Lake build, full
`PrimeTensor.lean` elaboration and build, and the proof-fragment audit.
No `sorry`, `admit`, or new axioms. Archive static checks are not
Lean kernel verification.
