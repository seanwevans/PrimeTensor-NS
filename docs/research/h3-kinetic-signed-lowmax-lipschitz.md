# Signed sixth-flux: exact finite-radius weighted-H³ Lipschitz modulus

Base: `b78c67a4cb5ccb4bdfb52557d4fce1c8e4b403bd` (signed two-snapshot weighted-H3 flux estimate).

## Mathematical improvement

The previous theorem bounds the actual complex, signed LowMax(R) integral
`Φ_R(v)` of two complex three-component Schwartz Fourier velocity fields
represented by actual spectral `H³` states `V,W`. Its right side consists of
three mixed Young costs, with independent positive reciprocal scales.

Set `d=‖V−W‖`, `a=‖V‖`, `b=‖W‖`, `τ=d+ε>0`, `C0=h3SobolevDeweightingConstant`
and `ρ=2(R+1)`. Choose the Young scales

- first term: `s₁=1/√τ`, with difference in the first L² factor;
- middle term: `s₂=1`, with difference in the middle Fourier L¹ factor;
- third term: `s₃=√τ`, with difference in the last L² factor.

After substitution, the scalar costs are proportional to

`[(d²/τ + τa²)a + (a²+b²)d + (τb²+d²/τ)b]`.

Since `d≤τ` and `1≤M=1+a+b`, each bracketed term is at most `2τM³`.
Combining with the exact coefficients in the previously proved mixed estimate
gives, for every ε>0,

`‖Φ_R(v)−Φ_R(w)‖ ≤ 243 ρ⁷ C0 (d+ε) (1+a+b)³`.

An order-theoretic epsilon-elimination lemma then establishes the honest
**linear** modulus, including `d=0`:

`‖Φ_R(v)−Φ_R(w)‖ ≤ 243 [2(R+1)]⁷ C0 ‖V−W‖ (1+‖V‖+‖W‖)³`.

Thus, within a fixed weighted-H³ ball, the native complex signed low-frequency
flux is Lipschitz in the spectral topology. This is an absolute complex norm
bound; no phase or sign information is replaced early by a scalar cubic ansatz.
The proof requires neither solenoidality of the arbitrary Schwartz inputs nor
an independent mixed-integrability hypothesis: the latter was discharged in
`58942f9bd`.

## Still open

The coefficient grows like the seventh power of the *fixed* Fourier cutoff.
This does not justify `R→∞`, terminal-uniform H³ control, or continuity in
physical time by itself. To connect with the kinetic PDE freezing argument,
the next step is to align the weighted-H³ spectral distance **on the exact
finite band** with the available physical low-frequency time increment,
without replacing it by an unsupported full-H³ temporal modulus.

## Verification

The registrar installs the import and audits `#check`/`#print axioms`. Run
`proof/generate_index.py`, targeted Lean elaboration, the module build, and
project-wide verification against the pinned commit. Archive structure and
Python source checks are not substitutes for Lean kernel checking.
