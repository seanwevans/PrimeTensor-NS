# Real solenoidal Schwartz density: exact physical H³ derivative jets

**Base HEAD:** `0f61007c` — prove real solenoidal physical Schwartz density in weighted H3.

**Module:** `FullThirdRealSolenoidalSchwartzMatchedH3Jets.lean`

The compiled unconditional solenoidal density result from the base commit
constructs genuine real Schwartz fields `Ψ_n` with exact pointwise physical
divergence zero and weighted L² Fourier states `V_n → target`.

This step connects those **same** approximating fields to the existing
physical jet machinery. We do not replace them by a distinct generic
non-solenoidal Schwartz sequence.

## Mathematical content

For a real Schwartz scalar `ψ` and weighted Fourier state `F` with

`F(ξ) = W₃(ξ) · 𝓕(complexify ψ)(ξ)` almost everywhere,

the existing inverse-weight map and weight cancellation prove the genuine
`Lp ℂ 2 volume` equality

`rawFourierL2(F) = toLp(𝓕(complexify ψ))`.

The Schwartz inversion/real-part composition is literally `ψ`, so the
existing exact second/third derivative lemmas give

- `decodeReal(F) = toLp(ψ)`;
- for every ordered axis pair `(a,b)`, the canonical real physical second
  Fourier jet of `F` equals `toLp(∂ₐ∂ᵦψ)` transported through the native
  `h3FromFourierRealL2` carrier;
- for every ordered axis triple `(a,b,c)`, the canonical third jet of `F`
  equals `toLp(∂ₐ∂ᵦ∂𝚌ψ)` with the same carrier map.

The `2πi` Fourier derivative normalization comes from the previously
established exact matched-derivative theorems. No ad-hoc derivative scaling
is introduced.

## Unconditional assembly

For every target satisfying `H3SpectralFinDivergenceFree` and
`H3SpectralVelocityRawHermitian`, the theorem chooses one sequence of
real solenoidal Schwartz fields and corresponding weighted spectral states
and proves simultaneously:

1. `Vₙ → target` strongly in weighted H³.
2. Exact pointwise physical divergence zero for each `Ψₙ`.
3. Almost-everywhere weighted Fourier equality for each component.
4. Zeroth/second/third real physical L² jet identities for that **same** `Ψₙ`.
5. Strong convergence of the 3 zero-order, 27 second-order, and 81 third-order
   physical L² coordinate families to their canonical targets.
6. The weighted approximating states form a Cauchy sequence.

## Boundaries

The module adds no axioms and no hypotheses beyond Fourier incompressibility
and real Fourier Hermitian symmetry of the target. It is a spatial H³ graph
statement, not a Navier–Stokes continuation proof. It does not establish new
bounds on the nonlinear signed transport functional.

## Local tests

- `lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdRealSolenoidalSchwartzMatchedH3Jets.lean`
- `lake build PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRealSolenoidalSchwartzMatchedH3Jets`
- `python3 proof/generate_index.py --check`
- `python3 proof/check_fragment.py --all`
- `lake build`

**Local Lean compilation is not available in the artifact container.**
