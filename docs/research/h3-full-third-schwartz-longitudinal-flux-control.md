# H³ longitudinal flux control: the actual analytic boundary

**Baseline:** `f3d72583` — exact six-orbit flux plus the three off-solenoidal longitudinal contractions, and its corrected canonical/physical Schwartz limit.

## Exact new estimate

Writing `a=p·q`, `b=p·r`, `c=q·r`, `α=p·A`, `β=q·B`, `γ=r·C`, and `X=A·C`, `Y=A·B`, `Z=B·C` (complex-bilinear dots), the correction is

```
D_long = -Z α b (b²+3bc+3c²)
         -X β c (3b²+3bc+c²)
         -Y γ c (3a²+3ac+c²).
```

The new Lean estimate is the pointwise inequality

```
|D_long| <= |Z||α||b||b²+3bc+3c²|
          + |X||β||c||3b²+3bc+c²|
          + |Y||γ||c||3a²+3ac+c²|.
```

All three terms explicitly retain their Fourier-divergence factor, and no inverse powers of frequencies enter. **This is not** a uniform cubic H³ estimate: a high-high-low configuration can make the factors large, and dropping the correction before controlling its integral can destroy a cancellation essential to the physical commutator.

## Zero-middle-frequency cancellation: a warning about separate limits

For `q=0` and `r=-p`, write `P=p·p`, `Z=B·C` and `α=p·A`.
The three-term radial flux and longitudinal correction have the exact
values

```
F_six(p,0,-p; A,B,C) = -Z α P³,
D_long(p,0,-p; A,B,C) = +Z α P³.
```

The complete six-orbit vanishes identically although neither separated
summand must vanish. This is an algebraic consequence of the prior exact
six-orbit identity (not a newly registered Lean theorem in this patch).
It diagnoses precisely why one cannot commute an arbitrary weighted-H³
limit separately through the two flux pieces without additional control.

## Exact residual identity and limit criterion

For a real Schwartz profile `f`, provided its longitudinal integrand is integrable, the uncorrected flux is integrable and

```
fullSchwartzThirdCommutator(f)
  = ((2π)^7/3) Im ∫ F_six(f)
  + ((2π)^7/3) Im ∫ D_long(f).
```

For a derivative- and decoder-matched H³ Schwartz completion, the previously proved canonical limit therefore transfers to the **uncorrected** flux *if* the signed longitudinal integral tends to zero. The resulting theorem states that condition exactly; it does not falsely infer it from convergence of `F.spectral`.

## Hard analysis still needed

1. Establish an integrable quantitative majorant of the longitudinal term along a chosen completion; then show its integral vanishes, **or**
2. Construct a divergence-free matched Schwartz completion via a Fourier-transverse approximation (with origin excision, Hermitian reality, and preservation of the exact decoder/jet matching used by the canonical limit).

The second route is structurally promising because exact frequency transversality annihilates the defect pointwise, but it requires a genuine density/construction theorem, not an additional assumption inserted into the existing completion.

## Validation

The module contains no `sorry` or new axioms. The algebraic norm estimate and the residual calculation are included as Lean proof terms. They **must be compiled and audited in the project's Lake environment**; this generation environment does not contain Lean/mathlib.
