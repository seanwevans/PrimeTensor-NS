# Open strict-sign neighborhood of the sharp Schwartz triad

**Checkpoint:** `ccfa8274` — sharp six-order symbol recovered on a concrete
vector-valued Schwartz field.

Fix the actual divergence-free, Hermitian Fourier Schwartz field `U` at
`t = 1/4`, with `p=(1,0,0)`, `q=(1/4,1/4,0)`, `r=(-5/4,-1/4,0)`.
On the two-independent-frequency momentum plane, set

\[
F(p',r')=\operatorname{Re}\{i C_6(p',-p'-r',r';
   U(p'),U(-p'-r'),U(r'))\}.
\]

`FirstMonomialTriadLowQuarterLocalSign` proves:

1. `F` is continuous as a polynomial expression evaluated on the fixed
   Schwartz field.
2. `F(p,r)=9/64>0`, by the prior exact sharp-center recovery.
3. Consequently `F` is positive on an open neighborhood of `(p,r)`, in the
   topology of the six real independent frequency coordinates.

This proves **local sign persistence**, but **not** a nonzero full-space
integral. To derive a global noncancellation statement, one still needs to
integrate over a positive-measure resonant neighborhood and bound or
classify every other resonant sector and its signed contribution. The
physical seven-derivative Fourier phase is `-(2π)^7 i`; the `i` used in this
module isolates the sign of the imaginary six-order coefficient only.
