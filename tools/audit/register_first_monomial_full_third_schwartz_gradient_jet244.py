#!/usr/bin/env python3
"""Register the full-third 3-3-1 gradient mixed-root continuity module."""
from pathlib import Path
import re

MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientJetContinuity244'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
ROOT = Path('PrimeTensor.lean')
AUDIT = Path('tools/audit/FirstMonomialTriad.lean')
NAMES = ('SchwartzGradientTripleDifferenceJets244', 'SchwartzFullGradientDifferenceJets244', 'H3FullThirdSchwartzGradientJetApproximation244', 'H3FullThirdSchwartzGradientJetApproximable244', 'fullGradientTriple_tendsto_of_threeDifferenceJets244', 'fullSchwartzGradientTransport_tendsto_of_differenceJets244', 'H3FullThirdSchwartzGradientJetApproximation244', 'H3FullThirdSchwartzGradientJetApproximation244', 'h3Path_gradientJets_implies_fullThirdObservableApproximable244', 'h3Path_noExtension_gradientJetSignedWitness244', 'h3Path_extension_of_gradientJetSignedEnvelope244', 'h3Path_extension_of_gradientJetTopSpectralDominance244', 'H3FullThirdSchwartzGradientJetApproximation244.toSplitJet', 'H3FullThirdSchwartzGradientJetApproximation244.toObservable')

def main():
    for p in (SOURCE,ROOT,AUDIT):
        if not p.is_file():
            raise SystemExit(f'Missing file: {p}')
    source=SOURCE.read_text()
    if re.search(r'\b(sorry|admit)\b',source):
        raise SystemExit('Forbidden proof placeholder')
    for name in NAMES:
        if name.split('.')[-1] not in source:
            raise SystemExit(f'Missing declaration: {name}')
    imp='import '+MODULE
    lines=ROOT.read_text().splitlines()
    if imp not in lines:
        ROOT.write_text('\n'.join(lines+[imp])+'\n')
    old=AUDIT.read_text()
    lines=old.splitlines()
    imports=list(dict.fromkeys([l for l in lines if l.startswith('import ')]+[imp]))
    body=[l for l in lines if not l.startswith('import ')]
    while body and not body[0].strip():
        body.pop(0)
    for name in NAMES:
        full='PrimeTensor.FirstMonomialTriad.'+name
        for op in ('#check ','#print axioms '):
            cmd=op+full
            if cmd not in body:
                body.append(cmd)
    new='\n'.join(imports+['']+body).rstrip()+'\n'
    if new != old:
        AUDIT.write_text(new)
    print(f'Registered {len(NAMES)} gradient-jet declarations')

if __name__=='__main__':
    main()
