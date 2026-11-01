#!/usr/bin/env python3
"""Register source-excess signed H3 energy/viscous/transport competition."""
from pathlib import Path
import argparse, re, sys
sys.dont_write_bytecode=True
ROOT = Path(__file__).resolve().parents[2]
MODULE = "PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessSignedEnergyCompetition"
SOURCE = ROOT / (MODULE.replace(".", "/") + ".lean")
ROOT_LEAN = ROOT / "PrimeTensor.lean"
AUDIT = ROOT / "tools/audit/FirstMonomialTriad.lean"
THEOREMS = (
    "h3Critical_fullDissipationFloor_forces_signedH3Transport",
    "h3Critical_fullDissipationFloor_forces_signedH3Riccati",
    "h3Critical_fullDissipationFloor_signedDrainOrRiccati",
    "h3Critical_fullDissipationFloor_nondecreasing_forces_cubicH3Energy",
    "h3Critical_actualSourceExcess_forces_signedH3Competition",
    "h3Critical_noL2Trace_cofinalQuintic_signedH3EnergyCompetition",
)
IMPORT = "import " + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    "#check PrimeTensor.Bridge.Euclidean." + name,
    "#print axioms PrimeTensor.Bridge.Euclidean." + name,
))
def install(path, entries, prepend=False):
    content = path.read_text(encoding="utf-8")
    missing = [e for e in entries if e not in set(content.splitlines())]
    if missing:
        block = "\n".join(missing) + "\n"
        path.write_text(block + content if prepend else content.rstrip("\n") + "\n" + block, encoding="utf-8")
def main():
    ap=argparse.ArgumentParser()
    mode=ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--apply", action="store_true")
    mode.add_argument("--check", action="store_true")
    args=ap.parse_args()
    for path in (SOURCE,ROOT_LEAN,AUDIT):
        if not path.is_file(): ap.error("missing: "+str(path))
    if args.apply:
        install(ROOT_LEAN,(IMPORT,))
        install(AUDIT,(IMPORT,),prepend=True)
        install(AUDIT,CHECKS)
    for path, entries in ((ROOT_LEAN,(IMPORT,)),(AUDIT,(IMPORT,)+CHECKS)):
        lines=path.read_text(encoding="utf-8").splitlines()
        for e in entries:
            if lines.count(e)!=1: ap.error("expected one "+repr(e)+" in "+str(path))
    source=SOURCE.read_text(encoding="utf-8")
    for name in THEOREMS:
        if len(re.findall(r"(?m)^theorem\s+"+re.escape(name)+r"\b",source))!=1:
            ap.error("missing/duplicate "+name)
    for forbidden in (r"\bsorry\b",r"\badmit\b",r"\bunsafe\s+axiom\b"):
        if re.search(forbidden,source): ap.error("forbidden "+forbidden)
    print("PASS",len(THEOREMS),"theorems and",len(CHECKS),"axiom audits")
if __name__ == "__main__": main()
