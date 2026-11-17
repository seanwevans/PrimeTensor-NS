#!/usr/bin/env python3
"""Register exact joint finite-Galerkin Wiener temporal FTC and bounds."""
from pathlib import Path
import argparse,re,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinJointTemporalWiener')
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=(
 'thirdFullThreeBand_z3GalerkinFiniteTimeIntegralSum244',
 'thirdFullThreeBand_z3GalerkinFieldTimeIntegral_interchange244',
 'thirdFullThreeBand_z3GalerkinFieldTimeIntegral_51000_100Ball244',
 'thirdFullThreeBand_z3GalerkinStrongODE_WienerIncrement51000_100Ball244',
 'thirdFullThreeBand_z3GalerkinSourceTimeVariation51000000_100Ball244',
 'thirdFullThreeBand_z3GalerkinFieldTimeVariation51510000_100Ball244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in THEOREMS
             for line in ('#check '+NS+name,'#print axioms '+NS+name))

def add_missing(path,entries,prepend=False):
    content=path.read_text(encoding='utf-8'); present=set(content.splitlines())
    missing=[x for x in entries if x not in present]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+content if prepend else content.rstrip('\n')+'\n'+block,
                        encoding='utf-8')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=p.parse_args()
    src=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'; audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for path in (src,root,audit):
        if not path.is_file():p.error('missing required file: '+str(path))
    code=src.read_text(encoding='utf-8')
    stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
    stripped=re.sub(r'--[^\n]*','',stripped)
    if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):p.error('placeholder or new axiom')
    if any(line!=line.rstrip() for line in code.splitlines()):p.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code))!=1:
            p.error('missing/repeated theorem '+name)
    if args.apply:
        add_missing(root,(IMPORT,))
        add_missing(audit,(IMPORT,),prepend=True)
        add_missing(audit,CHECKS)
    for path,req in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=path.read_text(encoding='utf-8').splitlines()
        for line in req:
            if lines.count(line)!=1:
                p.error('missing/duplicate registration: '+str(path)+' '+line)
    print(f'PASS: joint Z3 Galerkin temporal Wiener: {len(THEOREMS)} theorems, {len(CHECKS)} axiom probes')

if __name__=='__main__':main()
