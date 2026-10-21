#!/usr/bin/env python3
"""Register old Point3 physical gradient triple and matched Schwartz limit."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientPoint3TripleBridge244'
THEOREMS = ['h3ActualPhysicalFirstJetLinf_ae_eq_oldField244', 'h3ActualGradientTripleDensity_ae_eq_oldPhysical244', 'h3ActualGradientLpTriple_eq_oldPhysicalIntegral244', 'h3SchwartzGradientLpTriple_eq_integral244', 'h3MatchedSchwartz_gradientTripleIntegral_tendsto_oldPhysical244', 'h3MatchedSchwartz_fullGradientTriple_tendsto_oldPhysical244']
DEFS = ['h3OldPhysicalGradientTripleDensity244']
SOURCE=Path(MODULE.replace('.', '/')+'.lean')
ROOT=Path('PrimeTensor.lean')
AUDIT=Path('tools/audit/FirstMonomialTriad.lean')

def main():
    for p in (SOURCE,ROOT,AUDIT):
        if not p.exists(): raise SystemExit(f'Missing {p}')
    src=SOURCE.read_text()
    if re.search(r'\b(?:sorry|admit)\b',src): raise SystemExit('Lean proof placeholders found')
    for k,items in [('theorem',THEOREMS),('noncomputable def',DEFS)]:
        for item in items:
            if not re.search(r'^'+k+r'\s+'+re.escape(item)+r'\b',src,re.M):
                raise SystemExit(f'Missing {k} {item}')
    imp='import '+MODULE
    old=ROOT.read_text(); lines=old.splitlines()
    if imp not in lines: ROOT.write_text(old.rstrip()+'\n'+imp+'\n')
    old=AUDIT.read_text(); lines=old.splitlines()
    imports=list(dict.fromkeys([x for x in lines if x.startswith('import ')]+[imp]))
    body=[x for x in lines if not x.startswith('import ')]
    while body and not body[0].strip(): body.pop(0)
    for d in [*THEOREMS,*DEFS]:
        qual='PrimeTensor.FirstMonomialTriad.'+d
        for s in ('#check '+qual,'#print axioms '+qual):
            if s not in body: body.append(s)
    new='\n'.join(imports+['']+body).rstrip()+'\n'
    if new!=old: AUDIT.write_text(new)
    print('Registered physical H3 gradient Point3 triple bridge')

if __name__=='__main__': main()
