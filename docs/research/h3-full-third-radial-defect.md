# Hard-math return: radial-defect cancellation of the COMPLETE physical H³ triad

**Pinned base:** `9da439ba` — minimal Riccati windows pay quadratic anchor or cubic charge. This work intentionally does not extend the terminal-escape alternative chain.

## Result

Let `p+q+r=0` be an actual Fourier momentum triad on the `PrimeTensor.Axis Depth.three` carrier, and let `A·p=B·q=C·r=0` be the exact physical polarization conditions. The already-verified *corrected* full-third symbol is the six-permutation sum of

```
O(p,q,r;A,B,C) =
  (A·C)(B·r) [(p·q)^3 + 3(p·q)^2(p·r)]
  + 3(A·B)(C·q) (p·q)^2(p·r).
```

This contains the full third-order gradient contractions **and** the interpolation monomials; the contractions in the two summands differ. It is not the isolated first monomial.

Write `a=p·q`, `b=p·r`, `c=q·r` and ``thirdFullRadialDefectMultiplier244 x y z = x²+xy+y²+3z(x+y)+3z²` (abbreviated `G(x,y;z)` below)`. The new **exact physical symbol identity** is

```
S₆ = (A·C)(B·r)(|r|²-|p|²) G(a,c;b)
   + (A·B)(C·q)(|q|²-|p|²) G(b,c;a)
   + (B·C)(A·r)(|r|²-|q|²) G(a,b;c).
```

Here all squared lengths are literally `thirdTriadAxisDot244 k k`; no inverse frequency or projection with a singular denominator appears. The proof uses momentum/incompressibility to pair the six terms and factor the polynomial differences.

**Balanced-frequency consequence:** if `|p|²=|q|²=|r|²`, the *complete corrected six-orbit* vanishes. The physical Hermitian reflected orbit also vanishes for **every complex phase**. This does not assert that pairwise-equal radii suffice: they do not. It does not assert that Fourier support of a nontrivial `L²(ℝ³)` velocity can lie on one exact sphere.

**Quantitative consequence:** if all three squared-radius differences have absolute value at most `ρ`, then

```
|S₆| ≤ ρ (|(A·C)(B·r)G(a,c;b)|
         + |(A·B)(C·q)G(b,c;a)|
         + |(B·C)(A·r)G(a,b;c)|).
```

This is a true algebraic gain in **radial shell imbalance** for the actual full physical H³ transfer coefficient, rather than another necessary condition for hypothetical nonextension.

## Why this matters, and exactly what remains

The existing adverse full-third Schwartz triad has squared frequency radii `1,2,5` and a nonzero phase-correct six-orbit `-96` (Hermitian `-192`). That is consistent with—and makes concrete—the nonzero radial-defect requirement. The previous static fixed-kinetic absorption counterexample remains valid. This factorization instead reveals which portions of the Fourier interaction cancel **before** taking absolute values.

The decisive next mathematical test is a full physical Fourier-integral inequality retaining this radial-defect multiplier. In particular, one must distinguish near-equal-radius triads (small multiplier) from strongly separated scales (possible large multiplier), then ask whether conservation, dissipation, the true NS transport structure, and dynamic interscale transfer can control the latter without assuming a terminal energy bound. A bound may still fail; it must be tested against the already-constructed adverse Schwartz families.

No global regularity, uniform shell-width bound, terminal integrability, new invariant from the logarithmic bridge, or PDE-time cancellation is claimed. The development is rooted in the exact physical three-axis carrier derived from `PrimeTensor.Depth`; a genuinely new `Depth` invariant would still require an independent proof.

## Validation contract

A new Lean module proves the exact polynomial identity, equal-radius cancellation, Hermitian cancellation, and the near-equal-radius estimate. The registrar adds imports to `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`, and checks axioms. Run the repository Lean toolchain and full audit before committing. The assistant environment does not contain `lean` or `lake`, so successful Lean elaboration is not claimed.
