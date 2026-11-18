#!/usr/bin/env python3
"""Register constructed Galerkin flows with cutoff-uniform analytic tails and time bounds."""
import argparse, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parents[2]
MODULE='PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinCompactnessEnvelope'
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=('thirdFullThreeBand_z3WienerTail_twoRadius244', 'thirdFullThreeBand_z3WienerTail_150_from180_100Ball244', 'thirdFullThreeBand_z3GalerkinFiniteODE_closedLipschitz51000_244', 'thirdFullThreeBand_z3GalerkinFiniteODE_exists_compactnessEnvelope244', 'thirdFullThreeBand_z3GalerkinFiniteODE_exists_uniformCutoffFamily244')
IMPORT='import '+MODULE
CHECKS=tuple(row for n in THEOREMS for row in (
    '#check '+NS+n, '#print axioms '+NS+n))

def add_missing(path,rows,prepend=False):
    original=path.read_text(encoding='utf-8')
    known=set(original.splitlines())
    missing=[r for r in rows if r not in known]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+original if prepend else original.rstrip('\n')+'\n'+block,
                        encoding='utf-8')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply',action='store_true')
    group.add_argument('--check',action='store_true')
    args=parser.parse_args()
    source=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'
    audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for path in (source,root,audit):
        if not path.is_file(): parser.error('missing file: '+str(path))
    code=source.read_text(encoding='utf-8')
    scrub=re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrub=re.sub(r'--[^\n]*','',scrub)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',scrub):
        parser.error('unproved or unsafe source')
    if any(line!=line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code))!=1:
            parser.error('missing/duplicate theorem '+name)
    if args.apply:
        add_missing(root,(IMPORT,))
        add_missing(audit,(IMPORT,),prepend=True)
        add_missing(audit,CHECKS)
    for path, required in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=path.read_text(encoding='utf-8').splitlines()
        for entry in required:
            if lines.count(entry)!=1:
                parser.error('missing/duplicate registration: '+str(path)+': '+entry)
    print('PASS: Galerkin compactness envelope registered:',len(THEOREMS),'theorems,',len(CHECKS),'probes')

if __name__=='__main__': main()
