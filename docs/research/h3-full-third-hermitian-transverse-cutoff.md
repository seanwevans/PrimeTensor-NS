# H³ complex Hermitian transverse cutoff, and real-solenoidal spectral bridge

**Baseline:** `12d95129` (`prove solenoidal weighted H3 spectral density through bounded Leray projection`).

## Algebraic checkpoint

For real frequency ξ and complex polarization A, the previously proven
polynomial numerator is

    N_ξ(A) = (ξ·ξ) A - (ξ·A) ξ.

The new Lemma `thirdFullComplexTransverseNumerator_reality244` establishes

    N_{-ξ}(conj A) = conj(N_ξ(A))

for the actual complex-bilinear pairing, without assuming that A is real or
transverse. In particular, any complex profile U satisfying
`U(-ξ)=conj(U(ξ))` remains Hermitian after this transverse projection.

For an arbitrary **real even** scalar localization χ, set

    V(ξ) = χ(ξ) N_ξ(U(ξ)).

Then the patch proves all of the following exact identities:

    ξ·V(ξ) = 0
    V(-ξ) = conj(V(ξ))  [if U is Hermitian and χ is even]
    χ(ξ) = 0 => V(ξ) = 0
    V(0) = 0
    D_long(p,q,r; V(p),V(q),V(r)) = 0
    S_six(p,q,r;V(p),V(q),V(r)) = F_six(p,q,r;V(p),V(q),V(r))
       whenever p+q+r=0.

Crucially the support property is exact and needs no estimate, while the
Hermitian property uses no Fourier-amplitude conjugation error. This is the
pointwise algebra required for a smooth compact annular Fourier construction.

## Actual weighted H³ spectral bridge

The repository already has a bounded Leray operator with

    ||P G||_H³ <= 6 ||G||_H³,

and proves that it fixes solenoidal targets, maps all spectral states to
solenoidal states, and preserves raw Hermitian reality. The preexisting
`h3SpectralVelocityRawHermitian_realizable` theorem then gives the precise
*real* inverse-Fourier L² decoder, not merely a formally real-valued symbol.

The new `h3SchwartzSpectralLerayState_realSolenoidal244` and related theorems
combine these certificates. Given a Hermitian weighted-Schwartz input Phi,
its Leray projected spectral L² state is simultaneously divergence-free,
raw-Hermitian, and realizable, and for a solenoidal target U its approximation
error is bounded by six times the original strong H³ spectral error. A
conditioned sequence theorem retains Cauchy convergence and all certificates.

## Remaining hard analysis: no density leap

The theorem does **not** assert that all real solenoidal states already have
Hermitian Schwartz spectral approximations, nor that projected L² states
possess genuine Schwartz representatives. The high-frequency polynomial
numerator N_ξ is not the normalized Leray projector, and its quadratic
factor cannot be dropped when approximating arbitrary low-frequency data.

The next constructive analysis must: (1) prove smooth compact **annular**
frequency density with origin excision in weighted L²; (2) perform Hermitian
symmetrization without losing approximation; (3) use the true Leray
multiplier on annular inputs and show that its rational coefficient retains
smooth compact support; (4) deweight, inverse-Fourier transform, and match the
actual E₂/E₃ decoder jets. These are distinct from this algebraic checkpoint.

## Validation

Registrar apply/check and Python syntax/ZIP integrity are checked locally.
No Lean toolchain is present here, so none of the theorem proofs is claimed
to have compiled; `lake env lean` and the full audit remain the acceptance test.
