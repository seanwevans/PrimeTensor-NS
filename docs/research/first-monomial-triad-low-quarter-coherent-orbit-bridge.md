# Exact coherent orbit and support-tube bridge

Checkpoint: `67ce3914` (`parameterize quarter Schwartz width and classify coherent support`).

The proof formalizes the 12 coherent ordered first/third center labels as a finite Boolean-by-Fin6 index set, and shows that this is exactly the geometric center orbit from `FirstMonomialTriadLowQuarterUniformTube.lean`. In particular, the labeled center set introduced for the adjustable Schwartz packet field is not a larger or distinct collection of resonances.

For any target tube width `δ > 0`, set `σ = min(1,1/4)/4 = 1/16` and choose `ρ = min(δ,σ)/2`. Then `ρ > 0`, `ρ ≤ σ`, and `ρ ≤ δ`. The existing support geometry gives

```
Uρ(p) != 0 and Uρ(-p-r) != 0 and Uρ(r) != 0
  => (p,r) in thickening(ρ, coherent-centers)
  => (p,r) in cthickening(δ, coherent-centers).
```

This is a **geometric** statement about the narrow field's support; it is not the missing sign estimate for its nonlinear kernel. The fixed-width signed kernel's positivity cannot be transferred by replacing its cutoff parameter. The next task is to analyze an amplitude-independent polynomial germ symbol, and exploit nonnegative scalar packet weights to establish sign persistence for the width-dependent kernel.

The source uses finite decidable classification for all possible labels, with `decide`; there are no new mathematical axioms.

The final corollary combines this width selection with the existing positive tube of the **original** fixed-width signed kernel. It is a comparison about where new packet interactions occur in frequency space; it explicitly does not substitute the original kernel for the new one.
