# Native low-maximum sixth Fourier flux: the exact mixed radial coefficient

**Base:** `edb0317f328a2585721177116c4194410197cdea` — committed exact
three-slot polarization difference for the genuine signed sixth-order flux.

## The hard analytic step

Let `p + q + r = 0` be the three real Fourier frequencies of a complex
polarization triad, and `P,Q,W` be *distinct* complex polarization fields.
Write `F₆(P,Q,W)` for the native three-channel sixth-power flux, with the
same physical cubic squared-radius gaps as the original H³ transport.
The new `thirdFullKineticMixedPolarSixthBudget244` is exactly

    ‖dot(P(p),W(r)) mixedDot(r,Q(q))‖
  + ‖dot(P(p),Q(q)) mixedDot(q,W(r))‖
  + ‖dot(Q(q),W(r)) mixedDot(r,P(p))‖.

This retains complex phases **within** each contracted factor. It is not
an invented unsigned cubic transport functional.

The project's `thirdFullHighMaxSet244 R` uses the physical gradient magnitude
`2π|ξ|` and the threshold `2*(R+1)`. On its complement, all three raw
Euclidean radii are at most `ρ = 2*(R+1)` because `1 ≤ 2π`.
Consequently

    S = max(|p|², |q|², |r|²) ≤ ρ²,
    0 ≤ Δ = S - min(|p|², |q|², |r|²) ≤ ρ².

Applying the existing proven *unrestricted complex* radial-spread inequality,
not a fictitious solenoidal mixed-argument theorem, yields

    |F₆(P,Q,W)| ≤ 3 S² Δ B₆(P,Q,W)
                 ≤ 3 [2(R+1)]⁶ B₆(P,Q,W).

The proof does not need to infer pointwise solenoidality of any mixed input.

## Integrated consequence

On the exact low-maximum sector, provided the actual mixed flux and its
mixed contraction budget are integrable, we obtain the **explicit** bound

    ∫_LowMax(R) |F₆(P,Q,W)|
       ≤ 3[2(R+1)]⁶ ∫_LowMax(R) B₆(P,Q,W).

Combining this for the three genuine mixed kernels with the committed
polarization telescope gives

    |∫_LowMax F₆(P,P,P) - ∫_LowMax F₆(Q,Q,Q)|
       ≤ 3[2(R+1)]⁶ * [
           ∫_LowMax B₆(P-Q,P,P)
         + ∫_LowMax B₆(Q,P-Q,P)
         + ∫_LowMax B₆(Q,Q,P-Q) ].

This is a **real finite-radius coefficient gain** for the signed flux, not a
formal substitution of low-band PDE freezing into a cubic.

## Remaining analytic frontier

To turn the result into a Lipschitz/Hölder modulus in the native weighted-H³
Fourier Hilbert norm, prove an independently justified mixed
`L² × L² × L¹` convolution estimate on the conserving frequency plane and
then control the low-ball `L¹` factor by its finite volume. The unweighted
three-`L²` product on six-dimensional triads is not integrable by ordinary
pointwise Hölder without that convolution step. Also identify the true sharp
low-maximum radius with the H³ low-radial projection cutoff used in the PDE
modulus, retaining the `2π` normalization and factor two. No strong terminal
H³ trace or uniform-in-terminal-time cutoff is asserted here.
