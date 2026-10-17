# Physical 12-term gradient block: the genuine cubic shape frontier

Base checkpoint: `5c452454` (fixed kinetic full H3 static absorption obstruction).

The 243-slot signed interpolation monomial has already been shown to grow as
`M(f_t)=t^17 M(f)` along the exactly kinetic-preserving concentration
`f_t(x)=t^3 f(t^2 x)`.

**The principal missing issue was the signed gradient block in the full
third-order transport commutator.** The PDE's third-order `D^3(u·∇u)`
commutator contains four `D^3u·Du` terms and three `D^2u·D^2u` terms per
velocity axis. The global third-order physical energy pairing multiplies
these by `2 D^3u` before integration. The existing cyclic result turns the
three second-derivative products into `3 M(f)`.

This module builds the complete gradient shape `G(f)` on real Schwartz fields:

```
G(f) = 2 ∑_{j,i,k,l,r} ∫ D_{ikl} f_j [
    (D_{ikl} f_r)(D_r f_j)
  + (D_l f_r)(D_{ikr} f_j)
  + (D_k f_r)(D_{irl} f_j)
  + (D_i f_r)(D_{rkl} f_j)] dx.
```

The usual physical energy-pairing factor two, all 3^5 ordered axis slots,
all four gradient terms, the actual Jacobian, and both amplitude and spatial
homogeneities are retained. The new *Schwartz spatial* full-commutator shape is
`T(f) = G(f) + 3 M(f)`.

Theorems establish:

- `G(af)=a^3 G(f)` and `G(f(s·))=s^4 G(f)`;
- `T(af)=a^3 T(f)` and `T(f(s·))=s^4 T(f)`;
- `G(f_t)=t^17 G(f)` and `T(f_t)=t^17 T(f)`;
- if `T(f)≠0`, the orientation `f` or `-f` has `T>0`;
- if a real Schwartz **physically solenoidal** `f` has `T(f)≠0`, every proposed
  pair of static coefficients `C,K` is defeated by a solenoidal concentrated
  velocity with exactly fixed kinetic energy, using `D4` and the full
  normalized physical H3 energy on the right.

## Actual open mathematical obligation

**We have not proved `T(f)≠0` for the constructed quarter packet**. The
known strict positivity `M(f)>0` is insufficient: `G(f)` may equal `-3M(f)`.
The next step must compute the signed 3+3+1 Fourier triad integrals on that
packet, with reality phases and its 12 gradient terms, then determine whether
`G(f)+3M(f)` vanishes. The static Schwartz functional also still needs an
explicit theorem identifying it with the time-slice `thirdOrderGradientTransportSum`
of a physically realized admissible Navier--Stokes path. The present module
makes neither unproved claim.

A nonzero complete commutator would refute a universal pointwise static
absorption estimate; it would **not** settle Navier--Stokes regularity, because
the evolution may supply time-dependent cancellation unavailable to static
inequalities, and no singular solution is constructed here.
