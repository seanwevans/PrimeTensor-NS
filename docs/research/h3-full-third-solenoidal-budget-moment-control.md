# Exact L²--L²--L¹ control of unsigned solenoidal H³ Fourier flux budget

Base commit: `365a1e14a` — unconditional L¹ integrability of the three complex contraction budgets.

## New quantitative inequality

On the physical triad `(p,q,r)` with `q=-p-r`, let

- `F(ξ)=sqrt(Σ_j |𝓕(v_j)(ξ)|²)` be the same complex Fourier amplitude defined in `h3TriadSpectralAmplitude`;
- `H(ξ)=|ξ| F(ξ)`;
- `M₀(v)=∫ F(ξ)² dξ`, the unweighted Fourier kinetic mass;
- `M₁(v)=∫ H(ξ) dξ`, the first Fourier `L¹` moment.

The actual **unsigned** budget consists of

    |(A·C)(r·B)| + |(A·B)(q·C)| + |(B·C)(r·A)|.

Bilinear complex Cauchy--Schwarz, applied before absolute integration, gives

    budget(p,q,r) ≤ 2 F(p) F(q) H(r) + F(p) F(r) H(q).

Using `2ab ≤ a²+b²` for the two distinct amplitude products yields

    budget(p,q,r) ≤ (F(p)²+F(q)²)H(r)
                     + (F(p)²+F(r)²)H(q)/2.

Each of the four square-weight products has integral `M₀ M₁`. This is **not**
a formal symbol permutation: the proof invokes the existing product-volume
preserving `h3TriadMiddleEquiv` and `integral_prod_swap` equalities. Hence

    totalUnsignedBudget(v) ≤ 3 M₀(v) M₁(v).

No denominator, zero-frequency excision, arbitrary Schwartz seminorm, and no
premature assumption of spectral incompressibility are involved.

## Moving annuli under uniform moments

For a sequence of Schwartz fields with `M₀(v_n) ≤ E` and `M₁(v_n) ≤ M`,

    totalUnsignedBudget(v_n) ≤ 3 E M.

For solenoidal `v_n`, if a measurable triad sector `S_n` has its three
squared radii in `[lo_n,hi_n]`, `hi_n ≤ H`, and `hi_n-lo_n → 0`, then

    |∫_{S_n} flux₆(v_n)| ≤ 9 H² E M (hi_n-lo_n) → 0.

This is the first controlled **moving-field** thin-shell limit; the older
shrinking-annulus theorem applied only to one fixed field with one fixed
Schwartz budget.

## Remaining physical bridge

A uniformly bounded *weighted H³ spectral recovery sequence* should yield
uniform M₀ and M₁ through the repository's physical Fourier representative,
Plancherel/L² deweighting and the bundled first-moment H³ deweighting estimate
`h3SpectralScalarRawFourier_firstMoment_integral_le`. That identification
is NOT an unproved premise concealed in this file; it is the next theorem.

Even after that bridge, the off-shell complement can still be large. No sign,
coercivity, Navier--Stokes continuation, or Clay conclusion is claimed.

## Verification

- Register the module with `tools/audit/register_h3_full_third_solenoidal_budget_moment_control.py --apply` then `--check`.
- Run `proof/generate_index.py` then `--check`.
- Run the file with `lake env lean`, its target with `lake build`, the full fragment audit and full `lake build`.
- Inspect `#print axioms` for all exported definitions/theorems.
