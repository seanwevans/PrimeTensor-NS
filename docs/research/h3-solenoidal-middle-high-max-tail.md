# Genuine trilinear high-maximum tail: middle-minimum sector

Base HEAD: `d1addae8622670ddcfdd86e5130dc8223345105e`.

## Distinct analytic results

**Uniform raw sixth Fourier moment.** The existing strong convergence of the physical weighted H³ recovery `Vₙ → U`, combined with the established exact tail identity, gives for every ε>0 a common radius `R` and recovery index `N` such that

    ∀ n≥N, ∫_{high(R)} |ξ|⁶ |ûₙ(ξ)|² dξ < ε.

All three genuine Fourier components are controlled by the same high-radial state. This is not merely a uniform bound on the weighted H³ norm.

**Geometry of the low-middle sector.** Let `p+q+r=0`, `|q|≤min(|p|,|r|)`. The triangle inequality gives `|p|≤2|r|` and `|r|≤2|p|`. Hence if

    max(D(p), D(q), D(r)) ≥ 2(R+1),    D(ξ)=2π|ξ|,

then both `p` and `r` belong to the existing natural high-radial tail (`D≥R+1`). The real-valued threshold is never divided by frequency or by a possibly zero component.

**Genuine high-maximum trilinear bound.** Restrict the actual complex sixth-power flux to the measurable tie-broken low-middle sector and the large-maximum set above. Both cubic outer inputs are then high-radial, and the original symmetric `L²-L²-L¹` Fourier convolution lemma can be applied directly to a high-radial *square-integrable* outer profile. It gives the genuine signed complex integral bound

    |∫_{middle-min, max≥2(R+1)} F₆(v)|
       ≤ 72 M₆,high(R)(v) M₁(v)
       ≤ 648 C₁ K ||P_high(R) V||²,

where `M₆,high(R)=∫_{D≥R+1}|ξ|⁶ |û(ξ)|² dξ`. The existing weighted H³ physical recovery supplies a finite common `K` and its `M₁` ceiling. Consequently this trilinear *sector* high-max tail vanishes uniformly for all sufficiently late recovery indices at every fixed interior physical time, along the same approximants used to recover physical signed H³ transport.

## Scope and remaining hard obligations

The result covers one of the three disjoint minimum-frequency sectors: the middle-minimum sector. The low-first and low-last sector high-max analogues require the same high-outer argument after permuting the exact solenoidal six-order symbol. They are NOT claimed by these theorems. No terminal-time uniformity, good sign, absorption, global Navier–Stokes regularity, or Clay theorem is inferred.

The source and audit are designed for Lean 4.34.0-rc1 with the repository's mathlib. The ZIP was statically checked and the registrar exercised; Lean/lake are unavailable in the packaging runtime, so the user's guarded script must typecheck the modules before committing.
