# Solenoidal H³ flux: complete high-maximum trilinear tail

Baseline: `3bcde9fc5f3cdb7e440b29583b93b34e576ccebe`.

## Geometric input

Let `p+q+r=0`, and assign each pair to its tie-broken *minimum* Euclidean
frequency. With `g(ξ)=2π‖ξ‖`, define

`highMax(R) = { max(g(p),g(q),g(r)) >= 2(R+1) }`.

If `p` is minimal, then `q` and `r` obey `g(q) <= 2g(r)` and
`g(r) <= 2g(q)` by the triangle inequality, and both therefore have
`g >= R+1` on `highMax(R)`. The same conclusion holds for `p,q` when
`r` is minimal; the middle-minimum case was previously proven at
`3bcde9fc5`. These properties hold even at the threshold. This proof
permutates **the geometry**, not the complex trilinear kernel.

## Localized trilinear inequalities

Let `F_6(v,p,r)` be the genuine complex sixth-power solenoidal Fourier
flux symbol and let `A_v(ξ)` be the exact vector Schwartz spectral amplitude.
Set

- `M_6^high(R) = ∫_{g(ξ) >= R+1} ‖ξ‖^6 A_v(ξ)^2 dξ`;
- `M_1 = ∫ ‖ξ‖ A_v(ξ) dξ`.

The old exact low-first / low-last pointwise bounds and the
`outer-L¹` variable changes allow the cubic factors to be truncated by
the **same** high-radial indicator. Consequently each of the outer
high-maximum sector integrals is bounded in norm by `72 M_6^high M_1`.
Together with the compiled middle-sector result and the exact disjoint
partition of `highMax(R)`:

`‖∫_{highMax(R)} F_6‖ <= 216 M_6^high(R) M_1`.

For the existing genuine weighted H³ state `V`, where `K >= ‖V‖` and
its weighted Fourier representative agrees almost everywhere with
`W₃ 𝓕v`, the prior bridges yield

`M_6^high(R) <= 3 ‖P_R V‖²`, `M_1 <= 3 C₁ K`, hence

`‖∫_{highMax(R)} F_6‖ <= 1944 C₁ K ‖P_R V‖²`.

## Physical recovery and limitations

The identical real-solenoidal Schwartz physical recovery of the old
Navier–Stokes snapshot converges strongly in weighted H³; its high
weighted square tails (and thus raw sixth moments) vanish uniformly over
sufficiently late approximation indices. Since the first Fourier moment
has a common snapshot-dependent ceiling, the **complete high-maximum
complex flux integral** becomes uniformly small over those indices,
while the exact full signed physical H³ transport limit is retained.

There is no assertion of uniformity as physical time approaches the
terminal time, a coercive sign, unconditional endpoint control, or a
solution of global Navier–Stokes regularity. The proof is a fixed-snapshot
continuity / compactness result.

## Modules and checks

- `FullThirdSolenoidalOuterHighMaxTail.lean`: common high set, both outer
  sectors, geometry, actual complex trilinear estimates, weighted bounds.
- `FullThirdSolenoidalGlobalHighMaxTail.lean`: exact disjoint full
  high-max partition, sum bound and physical recovery corollary.
- `register_h3_full_third_solenoidal_global_high_max_tail.py`: repeatable
  imports, declaration `#check`, and `#print axioms` registration.

No `sorry`, `admit`, or new `axiom` is introduced. The source archive is
not a substitute for Lean compilation and the project-wide baseline audit.
