# Exact-anchor physical H³ higher radial dissipation moments

Base: `3db23574` — prove canonical H3 low-frequency persistence and near-total high-tail alternative.

Define a genuinely extended moment of the *full* physical H³ Fourier dissipation density D₃(ξ):

    M_m^full(t) = ∫⁻ |D(ξ)|^(2m) D₃(t,ξ) dξ ∈ ℝ≥0∞.

The extended nonnegative integral prevents silently treating a nonintegrable higher derivative as a zero real-valued integral. For every outer cutoff Q≥0 at a physical strict time,

    ENNReal.ofReal( (Q²)^m H_Q(t) ) ≤ M_m^full(t).

The inequality uses exactly the original spectral dissipation density and the already-proved Fourier radial cutoff; no assumed higher Sobolev integrability. On the **same** original canonical disjoint anchors τ(v k) and moving outer cutoffs Q_k=N(v k)+1, the preexisting theorem implies, for all m and β<1 and ε>0, eventually

    δ_k D_k ≤ ε OR
    ENNReal.ofReal( (Q_k²)^m β D_k ) ≤ M_m^full(τ_k).

Under the still-conditional eventual positive lower bound δ_k D_k≥η>0, the second branch holds eventually for every fixed m and β<1. This is a polynomial **frequency-amplified** mass lower bound. It is not an exclusion of the first branch or a proof of blowup.

This full weighted dissipation moment is distinct from the separately defined physical *top-order* higher radial moment ∫⁻ q^(4+m)|û|². A later bridge must compare their densities (with lower-order H³ weights) before treating them as interchangeable.

Declarations:
- `h3PathActualExtendedFullDissipationMoment244`
- `h3Path_extendedFullDissipationMoment_ge_highTailPower244`
- `h3Path_actualPhysicalExtendedFullMoment_ge_highTailPower244`
- `h3Path_exactAnchor_highTail_forces_extendedMoment244`
- `h3Path_noL2Trace_exactAnchor_chargeOrHigherRadialMoment244`

The source is syntax/audit checked but not locally elaborated with the project Lean toolchain.
