# Ordered Fourier derivative symbol of the complete third-order commutator

**Base commit:** `a26556f5` — isolate full third order Schwartz gradient concentration and cancellation.

## The exact seven contractions

Write the ordered frequency triad as `(p,q,r)`, with `(p,q,r)` respectively the Fourier wave of the energy-tested velocity, advecting velocity, and transported velocity. Let `A,B,C` be their three real polarization vectors. Before introducing the Fourier differentiation factor `(2πi)^7`, let `a = p·q`, `b = p·r`.

The actual four differentiated gradient products `D³u·(D³u Du)` have derivative-index contraction

    a^3 + 3 a b^2.

The three interpolating `D³u·(D²u D²u)` contractions give

    3 a^2 b.

Combining all seven gives the exact ordered symbol

    (A·C)(B·r) a (a^2 + 3ab + 3b^2).

The proof uses the finite axis-index sums directly (`PrimeTensor.Axis Depth.three`) and factors tensor-product sums; it does not posit a signed symbolic cancellation. The quadratic factor is positive semidefinite since

    4(a²+3ab+3b²) = (2a+3b)² + 3b².

## Explicit divergence-free ordered triad

Use actual three-coordinate vectors:

    p=(1,0,0), q=(1,1,0), r=(-2,-1,0)
    A=(0,1,0), B=(1,-1,0), C=(1,-2,0).

Then `p+q+r=0`, `A·p=B·q=C·r=0`, `p·q=1`, `p·r=-2`, `A·C=-2`, `B·r=-1`. The contracted ordered real polynomial is **14**, with gradient-index subtotal 13 and interpolation-index subtotal -6, hence total 7, times amplitude contraction 2.

## The non-negotiable open task

**An ordered derivative symbol is not the real signed physical integral.** The actual Fourier expansion attaches `(2πi)^7`, integrates over the momentum plane, and sums mode assignments plus Hermitian reflections. An individual nonzero ordered triad cannot prove that the fully permuted Fourier polynomial or the full physical `G₃+3M` is nonzero on the quarter packet. No PDE path or full-transport absorption claim follows here.

Next: obtain an exact Fourier representation for `fullSchwartzGradientTransport244` and its order-seven phase, combine it with the already compiled `M` Fourier-shell representation, symmetrize all mode placements respecting `p+q+r=0` and `B·q=0`, then test the actual real even-windowed quarter packet. That is the hard mathematical sign computation.
