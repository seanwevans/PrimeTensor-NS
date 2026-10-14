#!/usr/bin/env python3
"""Finite-permutation simplification for the orphan SixIntegral source.

Replace only the exact previous `simp only`/`hswap` proof, and leave theorem
statement, kernel definitions and all other code untouched. Fails closed.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
path = ROOT / (
    "PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/"
    "FirstMonomialTriadSixIntegral.lean"
)
old = """  -- The six coefficients are equal once product swaps and the four
  -- linear frequency identities have been reduced.  Avoid global AC simp.
  have hswap (w : V3 × V3) :
      (MeasurableEquiv.prodComm : V3 × V3 ≃ᵐ V3 × V3) w =
        (w.2, w.1) := rfl
  simp only [h3SchwartzTriadSixKernel,
    FirstMonomialTriad.sixOrderTriadCoefficient,
    h3TriadSixOrbit, Fin.sum_univ_succ, h3TriadPermutation,
    h3TriadMiddleEquiv, h3TriadSwapEquiv,
    h3SchwartzTriadKernel_eq_ordered, hswap,
    Prod.fst, Prod.snd, h1, h2, h3, h4]
  ac_rfl"""
new = """  -- Ordinary `simp` evaluates the fixed Fin-6 permutation vector and
  -- the measurable-equivalence compositions. Unfold the product swap, but
  -- do NOT install global add_comm / add_left_comm / add_assoc simp rules.
  simp [h3SchwartzTriadSixKernel,
    FirstMonomialTriad.sixOrderTriadCoefficient,
    h3TriadSixOrbit, Fin.sum_univ_succ, h3TriadPermutation,
    h3TriadMiddleEquiv, h3TriadSwapEquiv,
    h3SchwartzTriadKernel_eq_ordered,
    MeasurableEquiv.prodComm, h1, h2, h3, h4] <;>
    ac_rfl"""
if not path.is_file():
    raise SystemExit(f"Missing local source: {path}")
text = path.read_text()
if new in text:
    print(f"Already patched: {path.relative_to(ROOT)}")
elif text.count(old) != 1:
    raise SystemExit(
        f"Expected exactly one prior `simp only` proof; found {text.count(old)}. "
        "Inspect lines 95-115. No changes were made."
    )
else:
    path.write_text(text.replace(old, new, 1))
    print(f"Patched: {path.relative_to(ROOT)}")
