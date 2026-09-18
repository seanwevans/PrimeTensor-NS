from pathlib import Path

p = Path("PrimeTensor/Fluid/Vorticity/H3/Energy/Transport/Order/Three/Flux/DivergenceIntegrability.lean")
s = p.read_text(encoding="utf-8")

anchor = """noncomputable section

noncomputable local instance axisFintypeH3TopFluxDivergenceIntegrability
"""

replacement = """noncomputable section

attribute [local instance]
  point3MeasureSpaceH3OrderThreePairingClosure

noncomputable local instance axisFintypeH3TopFluxDivergenceIntegrability
"""

if anchor not in s:
    raise SystemExit("noncomputable-section anchor not found")

s = s.replace(anchor, replacement, 1)

p.write_text(s, encoding="utf-8")
print(f"patched {p}")
