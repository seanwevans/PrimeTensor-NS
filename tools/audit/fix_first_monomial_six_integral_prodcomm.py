#!/usr/bin/env python3
"""Repair the SixIntegral six-orbit identity without global AC simplification.

Matches the tactic from the prior AC timeout repair, leaves statements and
all six orbit terms untouched, and fails closed on other source variants.
"""
from pathlib import Path

root = Path(__file__).resolve().parents[2]
source = root / (
    "PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/"
    "FirstMonomialTriadSixIntegral.lean"
)
old = """  -- Expand the six fixed permutations without installing AC rewrites in simp.
  -- Then compare the six resulting terms modulo associativity/commutativity.
  simp [h3SchwartzTriadSixKernel, FirstMonomialTriad.sixOrderTriadCoefficient,
    h3TriadSixOrbit, Fin.sum_univ_succ, h3TriadPermutation, h3TriadMiddleEquiv,
    h3TriadSwapEquiv, h3SchwartzTriadKernel_eq_ordered, h1, h2, h3, h4] <;>
    ac_rfl"""
new = """  -- The six coefficients are equal once product swaps and the four
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
if not source.is_file():
    raise SystemExit(f"Missing local source: {source}")
text = source.read_text()
if new in text:
    print(f"Already patched: {source.relative_to(root)}")
elif text.count(old) != 1:
    raise SystemExit(
        f"Expected one prior AC tactic; found {text.count(old)}. "
        "Inspect the source; no changes were made."
    )
else:
    source.write_text(text.replace(old, new, 1))
    print(f"Patched: {source.relative_to(root)}")
