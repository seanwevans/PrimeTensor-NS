# Independent matched H³ Schwartz choices define the same signed completion

**Base:** `4204d175`, *close matched Schwartz E2 E3 energy Cauchy proof*.

An existence theorem for an H³ Schwartz Cauchy family and its completed signed
243-slot scalar does not by itself give a canonical scalar of the weighted H³
velocity: a different smooth compact-frequency approximation could in principle
produce another scalar.

The new theorem `completedSchwartzH3FirstMonomial_eq_of_sameWeightedLimit244`
removes this ambiguity for **any two derivative-matched families**. Its input is
an arbitrary pair of genuine H³-energy-Cauchy Schwartz families, their weighted
spectral sequences V and W converging to a common U, and the exact 27/81
Fourier–Schwartz derivative matching equalities. These equalities are already
available for the specific density construction from the preceding modules.

We first prove the continuity of the full 27- and 81-coordinate physical
Fourier-L² jet reconstructions as maps of weighted spectral H³ velocity. If
V_n and W_n both converge to U, every coordinate difference tends to zero.
Finite sums of square norms converge to zero. Exact Plancherel and Schwartz
line-derivative subtraction identify these sums with the actual E₂ and E₃
cross-family energies. The established signed transport invariance theorem
`completedSchwartzH3FirstMonomial_eq_of_crossEnergy244` finishes the result.

This is a theorem of **reference independence on the matched approximation
class**. The module does not prove that a general non-solenoidal compact
weighted approximant can be made exactly divergence-free; nor does it identify
the completed scalar with the original physical PDE trilinear integral.

Build verification must be performed in the actual Lean project. The provided
patch introduces no `sorry`, `admit`, or new axioms.
