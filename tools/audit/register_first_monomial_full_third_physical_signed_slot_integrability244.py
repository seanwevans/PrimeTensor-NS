#!/usr/bin/env python3
"""Register physical signed H3 2-4-4 slot integrability (idempotently)."""
from pathlib import Path
import re

MODULE = (
    "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control."
    "FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedSlotIntegrability244"
)
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DEFINITIONS = (
    "h3ActualSecondJetOnFourierCarrier244",
    "h3ActualThirdJetOnFourierCarrier244",
    "h3ActualSignedFirstMonomialSlotIntegral244",
    "h3CanonicalSignedFirstMonomialSlotIntegral244",
    "h3ActualSignedFirstMonomialAggregate244",
    "h3CanonicalSignedFirstMonomialAggregate244",
)
THEOREMS = (
    "h3ActualSecondJet_memLp_four244",
    "h3ActualSignedFirstMonomialSlot_integrable244",
    "h3ActualSignedFirstMonomialSlotIntegral_eq_canonical244",
    "h3ActualSignedFirstMonomialAggregate_eq_canonical244",
)

def main():
    for p in (SOURCE, ROOT, AUDIT):
        if not p.is_file():
            raise SystemExit(f"Missing file: {p}")
    src = SOURCE.read_text()
    if re.search(r"\b(?:sorry|admit|axiom)\b", src):
        raise SystemExit("Proof placeholder or new axiom in Lean source")
    for name in DEFINITIONS:
        if not re.search(r"^noncomputable def\s+" + re.escape(name) + r"\b", src, re.M):
            raise SystemExit(f"Missing definition: {name}")
    for name in THEOREMS:
        if not re.search(r"^theorem\s+" + re.escape(name) + r"\b", src, re.M):
            raise SystemExit(f"Missing theorem: {name}")
    imp = f"import {MODULE}"
    root_old = ROOT.read_text()
    root_lines = root_old.splitlines()
    if imp not in root_lines:
        # PrimeTensor.lean is an import aggregation file: append while keeping
        # its existing ordering and line endings intact.
        ROOT.write_text(root_old.rstrip() + "\n" + imp + "\n")
    old = AUDIT.read_text()
    old_lines = old.splitlines()
    # Move *all* import commands to the top. In particular, recover from an
    # older registrar that appended an import below #check / #print commands.
    imports = list(dict.fromkeys([s for s in old_lines if s.startswith("import ")] + [imp]))
    body = [s for s in old_lines if not s.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    for name in (*DEFINITIONS, *THEOREMS):
        qualified = f"PrimeTensor.FirstMonomialTriad.{name}"
        for cmd in (f"#check {qualified}", f"#print axioms {qualified}"):
            if cmd not in body:
                body.append(cmd)
    updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    if updated != old:
        AUDIT.write_text(updated)
    # Fail fast if a future edit inadvertently places an import below a check.
    seen_nonimport = False
    for line in updated.splitlines():
        if line.startswith("import ") and seen_nonimport:
            raise SystemExit("Late import in audit source")
        if line.strip() and not line.startswith("import "):
            seen_nonimport = True
    print("Registered physical H3 2-4-4 integrability and all 243 signed slots")

if __name__ == "__main__":
    main()
