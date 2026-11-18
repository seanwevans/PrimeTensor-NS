#!/usr/bin/env python3
"""Static proof and registration audit for exact finite Galerkin unrestricted overlap."""
from pathlib import Path
import re, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalKineticThreeBandZ3GalerkinUnrestrictedOverlap.lean'
DOC=ROOT/'docs/research/z3-galerkin-unrestricted-overlap-2026-11-17.md'
IMPORT='import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinUnrestrictedOverlap'
NAMES=(
    'thirdFullThreeBand_z3GalerkinFiniteODE_compactPaths_commonBall244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedUniqueOnIcc244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedOverlapUnique244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_differentEndsAgree244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_longerSegment_extends244',
)
src=SOURCE.read_text(encoding='utf-8')
text=re.sub(r'/-.*?-/', '', src, flags=re.S)
text=re.sub(r'--[^\n]*','',text)
if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',text):
    raise SystemExit('Forbidden assertion in source')
if any(src.count('theorem '+name+'\n')+src.count('theorem '+name+' ')!=1 for name in NAMES):
    raise SystemExit('Missing/duplicate theorem')
if not DOC.is_file(): raise SystemExit('Missing research note')
if 'Lean compilation remains' not in DOC.read_text(): raise SystemExit('Missing compiler caveat')
for path,required in ((ROOT/'PrimeTensor.lean',[IMPORT]),(ROOT/'tools/audit/FirstMonomialTriad.lean',[IMPORT]+[p+'PrimeTensor.FirstMonomialTriad.'+n for n in NAMES for p in ('#check ','#print axioms ')])):
    ls=path.read_text().splitlines()
    for r in required:
        if ls.count(r)!=1:raise SystemExit('Registration missing: '+r)
print('PASS: unrestricted real-Leray initial-segment uniqueness audit')
