# Uniform H³ spectral and high-maximum flux tails on strict compact time slabs

Base: `eca0ebae7a27f69a50b3a188534d463986f4af50` (complete high-maximum sector tail).

## Hard-math step: compact spectral families have uniformly vanishing high-frequency tails

The native high-radial projection `P_R` is an actual indicator multiplier on
weighted H³ Fourier states. It is a contraction, additive, and strongly tends
to zero on each fixed state, by the prior checkpoint. The new theorem establishes

```
∀ C : Set H3SpectralVelocityState, IsCompact C →
  ∀ ε > 0, ∃ R : ℕ, ∀ U ∈ C, ‖P_R U‖ < ε.
```

This is **not** a consequence of mere boundedness in H³: a bounded family can
translate its spectral mass to arbitrarily large frequencies. The key extra
hypothesis is *compactness*, and the proof uses:

1. `‖P_m U‖ ≤ ‖P_n U‖` whenever `n ≤ m`, via the exact squared-norm set
   integrals and monotonicity of the natural high-radial sets.
2. `P_R` is 1-Lipschitz, using the already-proved additivity and contraction.
3. For each ε>0 the sets `{U | ‖P_R U‖<ε}` form an open **directed cover**
   of a compact C; `IsCompact.elim_directed_cover` yields a single R.

## Unconditional physical strict-slab result

The existing theorem `h3Audit_initialActualSpectralVelocity_continuousOn`
proves strong H³ spectral continuity of the original physical velocity on
`(0,T)`. Therefore the image of every `[a,b]` with `0<a≤b<T` is compact
in the weighted H³ spectral state space. The new
`thirdFullPhysicalStrictSlab_uniformHighRadial244` gives

```
∀ ε>0, ∃ R, ∀ t∈[a,b], ‖P_R U_actual(t)‖ < ε.
```

No uniform-in-time Schwartz density selection, moment bound, or terminal
regularity assumption is used in this theorem.

## Conditional, exact trilinear consequence

For a **given** family `v(t)` of solenoidal Schwartz amplitudes on `[a,b]`
with the exact a.e. weighted Fourier representatives of a continuous spectral
path, compactness supplies a common K and R. The global result of the parent
commit yields

```
‖∫_(highMax(R)) F6(v(t))‖ ≤ 1944 C1 K ‖P_R U(t)‖² < ε
```

for all t in the same compact time slab. The theorem has a specialization to
`h3AuditActualSpectralVelocityTotal hH3`, keeping the matching family of
Schwartz realizations explicit in the hypotheses. The prior fixed-snapshot
density theorem does not automatically provide a jointly selected family
with the requisite exact representatives for all t.

## What remains open

The radius R depends on the strict compact slab. Compactness of `(0,T)` is
false in general, and bounded H³ norms alone do not imply uniform spectral
tightness as t→T. The precise next obstruction is an endpoint-uniform
high-radial compactness modulus, or an alternative PDE estimate which forces
one from viscosity/dissipation. No global Navier–Stokes continuation follows
from this module alone.

## Lean elaboration repair (fix 1)

The Fourier carrier `H3FourierPoint3` is indexed by `PrimeTensor.Axis Depth.three`.
The local finite-axis `Fintype` instance was missing from the compact-time
radial-tightness module, preventing elaboration of its scalar Fourier integrals
and `setIntegral_mono_set`. Add the same local instance as the preceding H³
transport modules. No theorem statement, cutoff bound, or proof premise changes.
