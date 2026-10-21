# Exact sharp Young deficit and top-frequency rigidity

Base: `ded66ed4` — sharpen kinetic H³ top Fourier Young absorption to optimal constant.

## The new mathematical content

Let `x = K E₃`, `d = D₃` and `b = K⁴ E₀`, with `K ≥ 0`. The actual
path Fourier moment inequality implies `x⁴ ≤ b d³`. The previous sharp
Young theorem states `x - d ≤ (27/256)b`. We now retain its **complete
nonnegative defect**:

\[
256d^3\left[d+\frac{27}{256}b-x\right]
=27(bd^3-x^4)
 +(3x-4d)^2(3x^2+8xd+16d^2).
\]

The first right-hand term is exactly the fourth-moment interpolation
defect. The second measures the scale mismatch `3 K E₃ - 4 D₃`.
Both are nonnegative for physical `K,E₃,D₃` (with positive dissipation
for the strict rigidity theorem). Hence the sharp Young error bounds the
square mismatch rather than merely controlling the total energy growth.

For `δ ≥ 0`, if `d + (27/256)b - x ≤ δ`, then

\[
(3x-4d)^2(3x^2+8xd+16d^2)\le256\delta d^3.
\]

For `d>0`, equality in sharp Young **forces simultaneously**

\[
x^4=bd^3,\qquad 3x=4d.
\]

The second condition is `D₃/E₃ = 3K/4` whenever `E₃>0`. These are
rigidity *necessary conditions*, not a claim that a nonzero physical
Fourier state realizes equality.

## Formal development

New module:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdSharpTopFourierYoungRigidity244.lean`.

Seven theorems cover the exact polynomial identity, abstract mismatch bound,
near-saturation quantitative bound, equality rigidity, physical defect
identity, physical Fourier moment mismatch estimate and physical equality
rigidity. No new assumptions are added to the actual PDE moment inequality.

## Remaining frontier

The bound still allows quadratic H³ energy growth, so it is not global
regularity. A truly dynamical improvement needs a strict or quantitative
Fourier moment-defect estimate, or a signed-transport cancellation estimate
that prevents near-saturation over sufficient physical times. In ℝ³ the
Fourier moment equality's geometric concentration question is especially
important; strictness alone without uniform separation may not suffice.

## Verification workflow

Register the module with
`python3 -B tools/audit/register_first_monomial_sharp_top_fourier_young_rigidity244.py`;
regenerate and check `proof/generate_index.py`; run the fragment checker,
module and full Lean builds, and `tools/audit/baseline.sh --reuse-build`.
No root-level `.sh` files are committed.
