# Kinetic low-radial Laplacian and combined projected RHS, terminal time-L¹

**Pinned base:** `0b249e99` (the actual low-radial physical Leray source is already terminal Bochner-L¹).

## Kinetic symbol argument

Let `U(t) = h3AuditActualSpectralVelocityTotal hH3 t`, and fix an energy
class `(a,T)`, strict kinetic anchor `b ∈ (a,T)`, later time `t ∈ (b,T)`,
coordinate `i : Fin 3` and Fourier-gradient cutoff `ρ ≥ 0`. Put
`Sρ = {ξ | 2π‖ξ‖ < ρ}` and `E₀(b) = velocityH3Energy0At u b`.

The exact deweighted Fourier Laplacian has representative `-q(ξ) û_i`, where
`q(ξ) = (2π‖ξ‖)²`. On `Sρ` its modulus is at most `ρ²‖û_i(ξ)‖`. The sharp
cutoff is the *genuine norm-one continuous L² operator* constructed in the
preceding module, so the `Lp.norm_le_mul_norm_of_ae_le_mul` comparison gives

    ‖1_{Sρ} Δ̂u_i(t)‖₂ ≤ ρ² ‖û_i(t)‖₂ ≤ ρ² √E₀(b).

The second inequality is the already-proved physical kinetic energy
monotonicity on a strict positive-time H³ path. The physical real
inverse-Fourier decoder is contractive, so the same bound holds for the
reconstructed physical L² low-frequency Laplacian coordinate.

## Time and combined-source results

The weighted scalar Fourier Laplacian map is continuous, the sharp-cutoff
L² operator is continuous, and the physical inverse-Fourier decoder is
continuous. Their composition with the **actual** positive-time spectral
velocity path is therefore strongly continuous. The kinetic bound dominates
its norm on every finite terminal interval `(b,T)`, proving
`IntervalIntegrable ... volume b T` directly, without a separate
measurability premise or terminal H³ ceiling.

Subtracting the earlier low-band nonlinear Leray source yields terminal
Bochner-L¹ for the **combined reconstructed projected Fourier RHS**. The
proof uses the existing physical decoder subtraction identity and the
linearity of the sharp cutoff to show that this difference is exactly the
decoder of the sharp-cutoff Fourier Laplacian minus Leray Fourier source.

## Remaining boundary

The established object is the cutoff of the genuine reconstructed Fourier
PDE RHS. To invoke the conditional high-pass theorem in
`TerminalFixedComponentResidualEscape.lean` with an independent **physical**
cutoff `Pρ`, a concrete bounded physical operator must be constructed and
identified with this low-band reconstruction, including commutation with the
physical real-part / inverse Fourier decoder. The current file does **not**
assume or claim that equality without proof. Nothing here establishes a
global Navier–Stokes regularity theorem.
