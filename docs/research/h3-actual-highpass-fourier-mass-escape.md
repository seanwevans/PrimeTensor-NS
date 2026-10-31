# Actual terminal high-frequency Fourier source mass escape

Base: `38dda4d6` — identify actual physical low-pass and prove high-pass source escape.

## New Fourier bridge

Let `R(t)` denote the actual real physical projected momentum source and let
`S_ρ = { ξ : 2π‖ξ‖ < ρ }`. The Fourier frequency carrier is the real
Euclidean `H3FourierPoint3`, and scalar physical fields live in the existing
real `L²(Point3)` Hilbert space.

We prove the radial indicator is invariant under reflection `ξ ↦ -ξ` and
therefore its complex Fourier `L²` multiplier preserves the **Hermitian
reality condition**. Consequently the existing inverse-Fourier decoder gives
an exact round trip even after applying the sharp cutoff. For an arbitrary
real physical scalar `f`:

    h3ScalarFourierL2 (Pρ f)
      = h3CriticalFourierSharpLowCutoffCLM ρ (h3ScalarFourierL2 f).

Thus `Fourier(f - Pρ f) = (I - 1_{Sρ}) Fourier(f)` in actual complex `L²`.
The high-pass state is a.e. identical to the indicator on `Sρᶜ`, with exact
identity

    ‖Fourier(f - Pρ f)‖² = ∫_{Sρᶜ} ‖Fourier(f)(ξ)‖² dξ.

## Genuine PDE Fourier source

The actual Fourier source is defined by Fourier-transforming a coordinate of
the **actual physical projected momentum source**, not by selecting an
unrelated spectral field. At each positive physical time, the already-proved
Hermitian reality of the actual weighted H³ velocity gives the exact identity

    Fourier(R_i(t)) = Δ̂_i(U(t)) - N̂_i(U(t),U(t)).

No artificial timewise H³ or full-dissipation ceiling is assumed.

## Conditional terminal high-frequency escape

Fix a physical H³ energy-class path, kinetic anchor `b`, and suppose the
physical old velocity has **no strong L² terminal trace** at `T`.
Then one coordinate `i : Fin 3`, selected once before radius and time, has:

- for every fixed finite nonnegative `ρ` and every `c ∈ (b,T)`, the exact
  Fourier high-pass projected source is not Bochner-L¹ on `(c,T)`;
- its Fourier `L²` norm is cofinally unbounded;
- for every real threshold `K`, some `t ∈ (c,T)` satisfies

      K < ∫_{Sρᶜ} ‖Fourier(R_i(t))(ξ)‖² dξ.

The final statement is **Fourier-source mass**, not the velocity H³
energy or dissipation. This is a necessary spectral concentration
condition if the terminal physical velocity trace fails; it does **not**
assert terminal trace failure or imply singularity without further work.

## Verification

Run the targeted module first, followed by the registrar, root/audit builds,
full Lake build and the project's baseline suite. No Lean executable was
available during patch construction, so all theorem proofs require local
compilation verification.
