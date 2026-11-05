# Weighted physical H³ recovery to uniform Fourier solenoidal flux budget

Base checkpoint: `9175fcfbb` — bound the exact unsigned three-channel sixth-power
Fourier contraction budget by `3 M₀ M₁`.

## The missing mathematical bridge

The older theorem's hypotheses concern the *raw* Fourier transform of a
Schwartz vector field, not the weighted spectral Hilbert state stored by the
physical solution's H³ recovery.  For each genuine Schwartz coordinate `f_j`
with weighted representative `G_j = W₃ 𝓕 f_j` almost everywhere, the existing
reciprocal weight identity gives the a.e. identification

    h3SpectralScalarRawFourier G_j = 𝓕 f_j.

The existing L² contraction and first-moment Hölder estimate then give

    ∫ |𝓕 f_j|² <= ‖G_j‖²,
    ∫ |ξ| |𝓕 f_j| <= C₁ ‖G_j‖,

where `C₁ = h3SobolevFirstMomentDeweightingConstant`.  The exact Euclidean
three-coordinate amplitude satisfies

    F(ξ)² = Σ_j |𝓕 f_j(ξ)|²,     F(ξ) <= Σ_j |𝓕 f_j(ξ)|.

By finite Fubini and monotonicity,

    M₀ <= Σ_j ‖G_j‖²,
    M₁ <= C₁ Σ_j ‖G_j‖.

Thus coordinate bounds `‖G_j‖ <= K` imply

    M₀ <= 3 K²,     M₁ <= 3 C₁ K,
    totalUnsignedBudget <= 27 C₁ K³.

No new homogeneous norm, arbitrary Schwartz seminorm, or Fourier moment
hypothesis is introduced.

## The physical witness

`exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244` already
provides one real solenoidal Schwartz recovery `Ψ_n`, its exact weighted
representatives `V_n`, their strong H³ convergence, and convergence of the
pure sixth-power flux to physical H³ transport.  Any convergent sequence of
normed-space vectors is bounded: separate a finite initial prefix and bound
the tail using `dist(V_n,U)<1`.  Hence `‖V_n‖<=K` for one global `K` and
all n.  Each coordinate obeys `‖V_n,j‖<=‖V_n‖`, so the above moment and budget
estimates hold on the **same** physical solenoidal approximants.

The theorem does *not* assert that the whole signed flux has favorable sign,
that the off-shell complement is small, or that the physical H³ norm remains
uniformly bounded as time tends to a possible endpoint.  Its bound is at a
fixed interior snapshot; K can depend on that snapshot.

## Verification scope

The module is supplied for compilation in the user's project with the known
Lean/mathlib lockfile.  The creation environment has no `lake` or Lean,
so this ZIP is **not represented as build-verified**.  The guarded runner
first regenerates/checks the index and executes targeted Lean and audit builds
before the full build and push.  Do not commit if any compilation fails.

## Lean elaboration correction (follow-up to `9175fcfbb`)

The Schwartz first-moment integrability proof binds
`(𝓕 (v j)).integrable_pow_mul volume 1` to a local `h` before
`simp` removes the explicit exponent `^ 1`. This prevents expected-type
propagation from demanding the simplified integrand before the source lemma
has been elaborated. The mathematical statement and all nine declaration
signatures are unchanged.
