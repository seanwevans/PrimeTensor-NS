#!/usr/bin/env python3
"""Narrow repair for the six-orbit identity's nonterminating AC `simp`.

Edits only the exact offending tactic; keeps the theorem statement and
all six permutations intact. Fails closed if the source has changed.
"""
from pathlib import Path

root = Path(__file__).resolve().parents[2]
path = root / (
    "PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/"
    "FirstMonomialTriadSixIntegral.lean"
)
old = """  simp [h3SchwartzTriadSixKernel, FirstMonomialTriad.sixOrderTriadCoefficient,
    h3TriadSixOrbit, Fin.sum_univ_succ, h3TriadPermutation, h3TriadMiddleEquiv,
    h3TriadSwapEquiv, h3SchwartzTriadKernel_eq_ordered, h1, h2, h3, h4,
    add_comm, add_left_comm, add_assoc]"""
new = """  -- Expand the six fixed permutations without installing AC rewrites in simp.
  -- Then compare the six resulting terms modulo associativity/commutativity.
  simp [h3SchwartzTriadSixKernel, FirstMonomialTriad.sixOrderTriadCoefficient,
    h3TriadSixOrbit, Fin.sum_univ_succ, h3TriadPermutation, h3TriadMiddleEquiv,
    h3TriadSwapEquiv, h3SchwartzTriadKernel_eq_ordered, h1, h2, h3, h4] <;>
    ac_rfl"""
if not path.is_file():
    raise SystemExit(f"Missing local source: {path}")
s = path.read_text()
if new in s:
    print(f"Already patched: {path.relative_to(root)}")
elif s.count(old) != 1:
    raise SystemExit(
        f"Expected precisely one original proof tactic, found {s.count(old)}. "
        "Source was changed; inspect lines 95-105 rather than applying a blind edit."
    )
else:
    path.write_text(s.replace(old, new, 1))
    print(f"Patched: {path.relative_to(root)}")
