# Infinite ordered Z³ Leray convolution identification

Base commit: `db1d0146200d1a4e9a84c97f275b273d2b10bebd`.

## Mathematical frontier

The earlier source completion theorem constructs an infinite Fourier source
`Q(t,n)` with a uniform full-output `W_(log(5/4)) <= 50000` bound. However,
that statement by itself does not identify Q with the Navier–Stokes quadratic
nonlinearity. This module closes the **spatial** identification, under the
necessary cutoff-exhaustivity assumption. It does not assert a time-integrated
PDE, a globally existing solution, or the Clay continuation endpoint.

## Absolute convergence of the physical ordered sum

For an infinite high-radius Fourier field u with all finite partial
`W_(log(9/5))` sums bounded by 100, and any output `n in Z³`, define

`B(u,u)_n = sum' (p in Z³), (-i) P_n [( (n-p) · u_p ) u_(n-p)]`.

Every ordered pair `(p,n-p)` is included once, and P_n is the genuine complex
Leray projector at the output frequency. The existing norm estimate, Euclidean
frequency-to-l1-degree comparison, three-radius derivative reserve, and
single-mode high-radius bound imply

`||Bterm(n,p)|| <= ||freq(n-p)|| ||u_p|| ||u_(n-p)|| <= 500 ||u_p||`.

The same high Wiener bound makes `sum_p ||u_p||` finite. Hence the physical
ordered Fourier convolution is **absolutely summable at every n**. No
cardinality factor or frequency enumeration is used.

## Exact finite partner reduction and exhaustion

The complete finite Galerkin quadratic term can be rewritten exactly as

`Q_s(u)_n = sum_(p in s, n-p in s) Bterm(n,p)`.

If `∀p, eventually p ∈ s_k`, then `s_k ∩ (n-s_k)` is eventually cofinal in
every finite subset of Z³. Summability thus gives convergence of the actual
finite **full-output** quadratic sums evaluated at u to B(u,u)_n.
This is valid for any nonnested, eventually exhausting sequence of cutoffs.

## Identification of completed source

The earlier exact `1000` source-difference theorem gives, at each output n,

`weight_(5/4)(n) * ||Q_s(u_k)_n - Q_s(g)_n||
 <= 1000 * W_(3/2,infinite)(u_k - g)`.

The proof formally shows the finite W_(3/2) sum is dominated by the infinite
one, using high-radius summability rather than assuming this inequality.
Uniform strong Wiener convergence makes the RHS vanish. Exhaustion gives
`Q_s(g)_n -> B(g,g)_n`. Uniqueness of coefficient limits now identifies the
previously completed Q with the absolutely convergent physical convolution.

The last theorem constructs an identified infinite source using the preceding
`uniformSourceCompletion244` theorem when the source Cauchy bound, high-radius
bound, strong convergence, and eventual exhaustion are available. These are
observable prior theorem interfaces, not hidden assumptions about the PDE.

## Outstanding PDE work

The remaining task is to pass actual **time integrals or derivatives** of the
Galerkin ODEs to the limit, while asserting compatible initial projections and
cutoff exhaustion. In particular, source identification alone does **not**
show that the infinite Fourier field satisfies the Navier–Stokes equation or
that it admits a global regular continuation.

## Verification

Source has 9 theorem declarations and 2 definitions with no `sorry`, `admit`,
`axiom`, `unsafe`, or `native_decide`. The included static audit checks the
critical symbolic links and output set/limit conditions. The target Lean
compiler and full Lake build must still elaborate the module and audit probes.
