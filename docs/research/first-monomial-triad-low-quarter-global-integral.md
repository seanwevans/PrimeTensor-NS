# Full six-order signed Fourier noncancellation, quarter scale

**Checkpoint:** `57de4bbf` (`construct even Schwartz window and preserve coherent triad sign`).

The even smooth window `Wρ` built from the six sharp center bumps yields an
actual Hermitian, divergence-free, compactly supported vector-valued Schwartz
Fourier field `Vρ(ξ)=Wρ(ξ)U(ξ)`.

The six-order signed momentum kernel satisfies **exactly**

`F_{Vρ}(p,r)=Wρ(p)·Wρ(-p-r)·Wρ(r)·F_U(p,r)`.

For the small width obtained from the uniform positive twelve-center tube,
nonzero window factors imply that `(p,r)` lies in the original Schwartz
kernel's positive tube. The window is nonnegative, so the modified kernel is
positive at those points and zero wherever any of its three window factors
vanishes. In particular it is **globally nonnegative**.

Continuity of the window and of the fixed Schwartz kernel makes the weighted
kernel continuous. Its support lies in `tsupport Wρ × tsupport Wρ`, a compact
subset of the six-dimensional independent-frequency space. Therefore it is
integrable against `volume.prod volume`.

At the sharp center pair `(P,R)`, all three scalar weights and the fixed
signed kernel are strictly positive, so the weighted kernel is strictly
positive. By continuity, its open support has positive product Lebesgue
measure. Combining global nonnegativity, integrability and positive support
measure proves:

`0 < ∫ (p,r), F_{Vρ}(p,r) d(volume × volume)`.

The result proves a *nonzero integral for this particular six-order signed
symbol*. It does not prove any blowup, regularity, or continuation result for
Navier--Stokes; those implications require separate mathematical bridges.
