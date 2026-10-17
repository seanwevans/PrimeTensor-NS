# One weighted H³ / physical Schwartz sequence (244)

Baseline: `7df48957`.

## Exact matched representative, not unrelated approximations

For each weighted scalar `G` and `ε > 0`, smooth compact weighted density
produces `F` and a compact smooth representative `g` with `‖G-F‖<ε`.
The canonical deweighted complex Schwartz spectrum
`S := h3SmoothCompactDeweightedSchwartz g ...` has **exact** bundled raw
Fourier value `h3SpectralScalarRawFourierL2 F = S.toLp`.

Define the genuine real physical Schwartz function
`ψ := h3RawSchwartzPhysicalRealInverse244 S`. The Plancherel Schwartz
compatibility and real projection give the exact bundled equality

`h3SpectralScalarDecodeRealL2 F = ψ.toLp`.

Choosing `ε = 1/(n+1)` independently for all three finite velocity components
then yields a synchronized sequence `(Vₙ, Ψₙ)` such that:

1. `Vₙ -> U` strongly in the **native** weighted spectral H³ norm;
2. `(Ψₙ j).toLp = h3SpectralVelocityDecodeRealL2 (Vₙ) j` for **every** n,j;
3. real physical L² approximants converge to `decodeReal(U)`;
4. the entire 81-coordinate cubic physical jet family of `Vₙ` converges
   to the native cubic family of U;
5. for a real Fourier-compatible physical H³ slice, target zero and cubic
   jets are the actual old physical derivative slots, by the previously
   proved compatibility theorem.

The novelty is that the real physical Schwartz maps and the weighted strong
H³ convergence now refer to the **same** approximating data. The older raw
Schwartz density could not provide this because it controlled only raw L².

## Remaining hard math

Identify the Fourier-multiplier real third derivatives of each `Vₙ` with the
literal derivatives of its matched Schwartz map `Ψₙ` (and prove analogous
second-order results). Then transport those to Point3 and identify the actual
27-slot E₂ and 81-slot E₃ integrals. The current theorem does not yet assert
solenoidality or the E₂/E₃ Cauchy condition of the signed nonlinear observable.
