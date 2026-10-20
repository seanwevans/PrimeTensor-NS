#!/usr/bin/env python3
"""Register a lean-verified (on user's machine) physical L⁴ second trace bridge."""
from pathlib import Path
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSecondL4Identification244"
SOURCE = Path(MODULE.replace(".", "/") + ".lean")
ROOT = Path("PrimeTensor.lean")
AUDIT = Path("tools/audit/FirstMonomialTriad.lean")
DECLS = ('h3SecondJet_dualLp_limits_ae_eq244', 'h3MatchedSchwartz_secondL4_ae_eq_spectralSecondL2244', 'weightedH3CanonicalSecondJetL4Trace_ae_eq_spectralL2244', 'weightedH3CanonicalSecondJetL4Trace_ae_eq_actualPhysical244', 'exists_actualPhysicalSecondJet_canonicalL4Representative244')


def add_import(path):
    """Keep Lean imports in the prelude; repair an already-appended audit import.

    Existing #check / #print axioms commands are retained in their original order,
    and running the registrar more than once leaves the file unchanged.
    """
    line = "import " + MODULE
    original = path.read_text()
    lines = original.splitlines()
    if path == AUDIT:
        # The old registrar appended this import after the audit's #checks.
        # Move *all* top-level imports (not just our own) ahead of commands.
        imports = []
        body = []
        for raw in lines:
            if raw.startswith("import "):
                if raw not in imports:
                    imports.append(raw)
            else:
                body.append(raw)
        if line not in imports:
            imports.append(line)
        while body and not body[0].strip():
            body.pop(0)
        updated = "\n".join(imports + [""] + body).rstrip() + "\n"
    else:
        # PrimeTensor.lean is a root import manifest, not a theorem audit.
        # Only append if necessary, preserving its original order.
        updated = original if line in lines else original.rstrip() + "\n" + line + "\n"
    if updated != original:
        path.write_text(updated)


def add_audit():
    data = AUDIT.read_text()
    lines = []
    for name in DECLS:
        needle = "#check PrimeTensor.FirstMonomialTriad." + name
        if needle not in data:
            lines.append(needle)
            lines.append("#print axioms PrimeTensor.FirstMonomialTriad." + name)
    if lines:
        AUDIT.write_text(data.rstrip() + "\n" + "\n".join(lines) + "\n")


def main():
    assert SOURCE.is_file(), SOURCE
    src = SOURCE.read_text()
    for name in DECLS:
        assert "theorem " + name in src, name
    add_import(ROOT)
    add_import(AUDIT)
    add_audit()
    audit_lines = AUDIT.read_text().splitlines()
    seen_command = False
    for audit_line in audit_lines:
        if audit_line.startswith("import "):
            if seen_command:
                raise RuntimeError("Lean audit import appears after a command")
        elif audit_line.startswith(("#check ", "#print ", "#eval ", "set_option ")):
            seen_command = True


if __name__ == "__main__":
    main()
