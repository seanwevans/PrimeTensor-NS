# Physical H³ transport persists off every bounded shrinking common-radius shell

Base: `2b4879f4e` — the exact solenoidal Schwartz Fourier flux has uniform raw
Fourier kinetic mass and first L¹ moment on the *same* weighted H³ physical
recovery sequence. This is fixed-snapshot uniformity, not uniformity as
physical time approaches the terminal endpoint.

## Two independent mathematical inputs already proved

For the exact sixth-power complex triad transfer `T₆(v;z)` and the signed physical
third-order H³ transport `T₃(u,t)`, the physical recovery produces solenoidal
Schwartz fields `vₙ` and strongly converging weighted H³ representatives `Vₙ`:

    c Im ∫ T₆(vₙ;z) dz  →  T₃(u,t),    c = (2π)^7/3.

The recent physical moment bridge proves, for a single constant K at this
snapshot, independent of recovery index n,

    M₀(vₙ) ≤ 3K²,
    M₁(vₙ) ≤ 3C₁K,
    B(vₙ) ≤ 27C₁K³.

The earlier pointwise solenoidal shell gain, integrated over *any* measurable
common-squared-radius annulus Sₙ with `0 ≤ loₙ ≤ hiₙ ≤ H`, gives

    ‖∫_{Sₙ} T₆(vₙ;z) dz‖
        ≤ 3H² (hiₙ-loₙ) B(vₙ)
        ≤ 81H² C₁K³ (hiₙ-loₙ).

Thus when `hiₙ-loₙ → 0`, the complex near-shell integral itself tends to zero;
not only its imaginary part. This conclusion holds with changing vₙ.

## New conclusion

Solenoidal Schwartz flux is integrable on the full triad carrier. The exact
measurable partition identity is

    ∫ T₆(vₙ) = ∫_{Sₙ} T₆(vₙ) + ∫_{Sₙᶜ} T₆(vₙ).

Linearity of the imaginary projection therefore gives

    c Im ∫_{Sₙᶜ} T₆(vₙ;z) dz  →  T₃(u,t).

The code first formalizes the abstract subtraction of a complex norm-null
shell; next invokes the quantitative moving-annulus theorem with uniform
moments; finally applies these facts to the genuine physical recovery witness
without selecting new approximants or inserting an unproved moment premise.

**Interpretation:** If the actual signed transport does not vanish, deleting
an arbitrarily narrow bounded common-radius band from each recovering Fourier
triad does not remove that transport. The off-shell complement necessarily
retains its signed limit. Nothing here supplies a sign, damping estimate,
endpoint-uniform H³ bound, or a Navier–Stokes continuation theorem.

## Verification and workflow

- Install with the idempotent `--apply` registrar.
- Regenerate `proof/generate_index.py` then require `--check`.
- Check all proof fragments, the target Lean file, module build, audit Lean
  entrypoint and full build; no commit or push until they succeed.
- Registrar adds `#check` and `#print axioms` of all three exported theorems.
- Lean/mathlib are not installed in the creation environment. The ZIP is
  **not** claimed to be compiled; the script runs on the checked-in lockfile.
