# Native low-maximum sixth-power flux: exact polarization difference

**Baseline:** `b6d1eced7e75ebc92206eb853f6b49ec22e3e2bb` — moving-radial physical H³ PDE cost on the actual kinetic gaps.

## The exact trilinear obstacle

The prior PDE estimate gives a weighted H³ low-band modulus:

    ‖Q_R U(t) − Q_R U(s)‖ ≤ C_R ∫_s^t ‖projected_source(r)‖ dr,

where `C_R ≤ 2 (R+1)^3`. This bounds the variation of the **input** but says nothing alone about the variation of a cubic, signed Fourier flux. In particular, the global absolute-cubic flux estimate is not a Lipschitz estimate, and the physical snapshot recovery at `s` and `t` need not be the same Schwartz sequence.

## Exactly which trilinear map?

The complex solenoidal sixth-order flux is the actual repository symbol

    thirdFullComplexSixthPowerFlux244 p q r A B C,

without conjugating a polarization or changing the six-power radial gap. It is a complex trilinear polynomial in `(A,B,C)`. For two triples of complex polarizations the new theorem proves **exactly**

    F(A,B,C) − F(A',B',C')
      = F(A−A',B,C) + F(A',B−B',C) + F(A',B',C−C').

`thirdFullKineticMixedPolarSixthFlux244` lifts this identity to three independent Fourier polarization profiles on the physical conserving triad `(p,−p−r,r)`. It agrees definitionally with the existing `thirdFullSchwartzComplexSixthPowerFlux244` when all profiles come from the same Schwartz Fourier field.

On the exact low-maximum sector `(thirdFullHighMaxSet244 R)ᶜ`, the integral telescope yields an **unconditional algebraic** identity under explicitly stated mixed-integrand integrability, and the norm bound

    |∫Low F(P,P,P) − ∫Low F(Q,Q,Q)|
      ≤ ∫Low |F(P−Q,P,P)|
      + ∫Low |F(Q,P−Q,P)|
      + ∫Low |F(Q,Q,P−Q)|.

The inputs remain complex and the Fourier signs remain intact until the final norm. The only integrability assumptions are stated in the Lean theorem, not invented consequences of a weak Sobolev limit.

## The real cutoff geometry

`thirdFullHighMaxSet244 R` uses `2*(R+1)` in the **physical gradient-frequency magnitude** `2π‖ξ‖`. Its complement constrains **all three** frequencies of the conserving triad strictly below this same threshold; not merely two outside inputs. Therefore profiles agreeing exactly on that physical ball have **identical signed low-maximum complex flux integrals** at radius R. The new theorem proves this from the actual set definition.

## Remaining hard estimate

To combine this result quantitatively with the previous **actual PDE freezing**, one must establish a finite-band mixed L²-L²-L² trilinear kernel estimate with the correct `2*(R+1)` cutoff:

    ∫Low |F(P−Q,P,P)| + |F(Q,P−Q,P)| + |F(Q,Q,P−Q)|
      ≤ K_R (‖P‖ + ‖Q‖)² ‖Q_(2R+1)(P−Q)‖,

after reconstructing the correct weighted H³ spectral inputs and handling a.e. representatives. Here `K_R` must be proved finite and explicit; this patch does not claim it. In particular, equality of pointwise Fourier profiles is stronger than their L² equality a.e., and terminal low-band freezing does not by itself imply signed low-maximum flux freezing.

The present patch establishes the **exact nonlinear polarization difference** needed to make that analytic step well-posed. No new axiom, `sorry`, fictitious terminal H³ ceiling, or Clay continuation claim is introduced. Pinned Lean/mathlib elaboration has not been run in the authoring environment.

## New declarations

- `thirdFullComplexSixthPowerFlux_firstSub244`
- `thirdFullComplexSixthPowerFlux_middleSub244`
- `thirdFullComplexSixthPowerFlux_lastSub244`
- `thirdFullComplexSixthPowerFlux_subTelescope244`
- `thirdFullKineticMixedPolarSixthFlux244`
- `thirdFullKineticMixedPolarSixthFlux_schwartz244`
- `thirdFullKineticMixedPolarSixthFlux_telescope244`
- `thirdFullKinetic_lowMax_allFrequenciesBelow244`
- `thirdFullKinetic_lowMax_polarKernel_congr244`
- `thirdFullKinetic_lowMax_polarIntegral_congr244`
- `thirdFullKinetic_lowMax_integralTelescope244`
- `thirdFullKinetic_lowMax_integralDifferenceBudget244`
