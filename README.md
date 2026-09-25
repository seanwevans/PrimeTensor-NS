# PrimeTensor-NS

Lean 4 / mathlib formalization of a continuation program for the three-dimensional incompressible Navier–Stokes equations on `ℝ³`.

The current development focuses on extracting **necessary terminal behavior from hypothetical failure of smooth H³ continuation**, together with explicit positive continuation criteria obtained by contraposition.

This repository does **not** currently prove finite-time blowup or unconditional global regularity.

## Main formalized claims

For a preterminal H³ path, write

```text
E(t)    = full H³ energy
E₃(t)   = top-order H³ energy
D(t)    = full H³ dissipation
D₃(t)   = top-order H³ dissipation
T_H3(t) = H³ transport term
```

The exact H³ balance is

```text
E'(t) + 2 D(t) = -T_H3(t).
```

Assuming the path does **not** extend smoothly across terminal time `T`, the formalization proves the following necessary consequences.

### Terminal energy and dissipation cascade

The Riccati lower bound gives

```text
2 ≤ K (T - t) sqrt(E(t)),
```

hence

```text
E(t) → +∞.
```

Using the Fourier interpolation inequality

```text
E₃(t)^4 ≤ E₀(t) D₃(t)^3,
```

the development derives

```text
D₃(t) → +∞,
D(t)  → +∞,
D₃(t) / E₃(t) → +∞,
D(t)  / E₃(t) → +∞.
```

A late comparison between full and top-order energy further gives

```text
D₃(t) / E(t) → +∞,
D(t)  / E(t) → +∞.
```

### Intrinsic H³ frequency cascade

Define

```text
Λ₃(t)^2 = D₃(t) / E₃(t),
ℓ₃(t)   = 1 / Λ₃(t).
```

Hypothetical nonextension forces

```text
Λ₃(t) → +∞,
ℓ₃(t) → 0.
```

More quantitatively, sufficiently late,

```text
1 ≤ 3 K² (E₀(b)+1) (T-t)² Λ₃(t)^6.
```

The critical quantity is nonintegrable on every strict terminal subtail:

```text
Λ₃^3 ∉ L¹((b,T)).
```

Therefore integrability of `Λ₃^3` on one strict terminal subtail implies smooth continuation.

### Full-energy normalized dissipation rate

With

```text
A_b = 3 K² (E₀(b)+1) (4 + 3 E₀(b))³,
```

hypothetical nonextension forces

```text
1 ≤ A_b (T-t)² (D₃(t)/E(t))³,
1 ≤ A_b (T-t)² (D(t) /E(t))³.
```

Thus normalized dissipation cannot remain bounded at terminal scale.

A direct continuation criterion follows: if one fixed finite bound

```text
D(t) ≤ C E(t)
```

recurs arbitrarily late, the path extends smoothly.

### Critical `(D/E)^(3/2)` obstruction

Define

```text
Q(t) =
  (D(t)/E(t)) *
  sqrt(D(t)/E(t)).
```

Since

```text
Q(t)^2 = (D(t)/E(t))^3,
```

the quantitative rate yields a harmonic lower bound on a terminal tail, and therefore

```text
Q ∉ L¹((b,T))
```

for every strict terminal subtail under hypothetical nonextension.

Equivalently, terminal integrability of `(D/E)^(3/2)` is a continuation criterion.

### Exact normalized balance-gap divergence

The exact H³ balance gives

```text
(-T_H3(t) - E'(t)) / E(t)
  = 2 D(t) / E(t).
```

Therefore hypothetical nonextension forces

```text
(-T_H3(t) - E'(t)) / E(t) → +∞.
```

The quantitative version is

```text
8 ≤ A_b (T-t)²
      ((-T_H3(t) - E'(t))/E(t))³.
```

This gives another direct threshold continuation criterion.

### Adverse transport on nonnegative-growth times

The formalization does not assume that adverse transport dominates at every terminal time.

Instead, on sufficiently late times satisfying

```text
E'(t) ≥ 0,
```

hypothetical nonextension forces, for every finite `M`,

```text
M ≤ (-T_H3(t)) / E(t).
```

Thus any sufficiently late nondecreasing-energy time must carry arbitrarily large adverse transport relative to full H³ energy.

A selected terminal sequence also synchronizes

```text
E'(t) → +∞,
D₃(t) → +∞,
D(t) → +∞,
-T_H3(t) → +∞.
```

## Canonical Landau coefficient frontier

The current Landau closure gives

```text
-T_H3(t)
  ≤
D(t) + c_L(t) E(t),
```

with canonical coefficient

```text
c_L(t)
  =
4422 *
  (1 + C₁ * sqrt(E(t))).
```

The generic absorption theorem proves:

```text
c_L ∈ L¹((b,T))
  ->
smooth continuation across T.
```

Consequently, hypothetical nonextension forces

```text
c_L ∉ L¹((b,T))
```

on every strict terminal subtail.

This isolates the present Landau frontier: the pointwise absorption estimate is available, but the current coefficient cannot be integrable on a nonextension branch. Closing the Landau route therefore requires a genuinely smaller temporal coefficient, additional cancellation, or another mechanism that bypasses this integrability obstruction.

## Interpretation

These are **conditional obstruction theorems**.

A statement such as

```text
no smooth continuation
  ->
D(t)/E(t) → +∞
```

does not establish nonextension.

Its value is contrapositive: any independent estimate incompatible with one of the forced terminal behaviors yields a continuation theorem.

## Build

```bash
lake build
```
