# Physical width-averaged shell and ninth/eighth PDE cutoffs on one terminal selector

Base commit: `e762f638` (“force width averaged kinetic Fourier shell inside minimal crossing”).

## Retained physical clocks and kinetic shell

The previous shell pigeonhole construction gives, at each strictly physical
snapshot, an index `n <= m < N` satisfying

    3 (n+1)^3 / 4 < (N-n) [D_low(m+2) - D_low(m+1)]
    3 (n+1)^3 / 4 < (N-n) * 4 (m+3)^8 K_band(m+1,m+2).

The original minimal-annulus ninth/eighth theorem constructed and exported
cofinal witnesses, but it omitted explicit strict-time membership of those
snapshots. Merely using two existential witness sequences would therefore
fail to identify their times, cutoffs, or physical Fourier states.

The first new theorem reconstructs the actual initial quadratic-sharp
selector `τ,N,K,C,δ`, preserves `τ n ∈ (a,T)` for every index and extracts
a strictly monotone cofinal selector `v` with pairwise-separated windows.
Under terminal full-H3-dissipation interval integrability, the identical
nonnegative cost series `Σ δ(vk) (vk+1)^3/2` is summable. The established
exact quadratic-sharp clock lemma supplies the three-scale PDE alternative.
The shell pigeonhole is then applied **at `τ(vk)`**, not at any independently
chosen snapshot. The strict physical membership passed to that theorem is
`hTime (v k)` from the original selector.

The second new theorem takes a dependent selection `m(k)` of those shell
indices and adds the conditional superlinear outer first crossing

    M (v(k)+1)^9 < (N(v(k))+2)^8,

for every fixed `M >= 0`, whenever the same geometric noncompression,
sixth-order linear-rate bound, and projected-source ceiling hold. It also
retains the existing quarter-cubic high H3 dissipation floor at lower
sub-ninth/eighth cutoffs. On precisely the same physical snapshots it
retains strict positivity of the last shell's raw kinetic mass and the
bound for its first-crossing overshoot.

## Limitations: necessary, not sufficient, localization

The selected pigeonhole shell may lie anywhere in the annulus. Its kinetic
lower bound contains the actual shell width factor `N(vk)-vk`, which is not
controlled above by the ninth/eighth barrier: the latter gives a **lower**
bound on N, not an upper bound. No uniform kinetic mass in one shell and
no contradiction with finite global kinetic energy follow without an
additional physical width, source, or temporal persistence estimate.

## Validation

The package is checked for source placeholders, Python syntax, registrar
idempotence and ZIP integrity. Lean cannot be run in the packaging runtime;
use `lake env lean` and the full project build in the user's repository.
