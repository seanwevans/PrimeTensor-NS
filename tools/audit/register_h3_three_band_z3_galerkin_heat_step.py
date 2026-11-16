#!/usr/bin/env python3
"""Register exact nonzero/zero-mode Galerkin heat-step Wiener debt theorem."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinHeatStepWiener')
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=(
 'thirdFullThreeBand_z3GalerkinHeatFactor_bounds244',
 'thirdFullThreeBand_normHeatPlusSource_budget244',
 'thirdFullThreeBand_z3GalerkinHeatDebt_nonneg244',
 'thirdFullThreeBand_z3GalerkinHeatStepWienerBudget244',
 'thirdFullThreeBand_z3GalerkinHeatStepWienerGrowth244',
 'thirdFullThreeBand_z3GalerkinHeatStep_at_zero244',
)
DEFS=(
 'thirdFullThreeBandZ3GalerkinHeatFactor244',
 'thirdFullThreeBandZ3GalerkinHeatStep244',
 'thirdFullThreeBandZ3GalerkinWienerMass244',
 'thirdFullThreeBandZ3GalerkinWienerDerivative244',
 'thirdFullThreeBandZ3GalerkinHeatDebt244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in (*DEFS,*THEOREMS)
             for line in ('#check '+NS+name, '#print axioms '+NS+name))


def add_missing(path,entries,prepend=False):
    old=path.read_text(encoding='utf-8')
    existing=set(old.splitlines())
    missing=[x for x in entries if x not in existing]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,
                        encoding='utf-8')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    mode=ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=ap.parse_args()
    src=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'
    audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for f in (src,root,audit):
        if not f.is_file():ap.error(f'missing required file: {f}')
    code=src.read_text(encoding='utf-8')
    stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
    stripped=re.sub(r'--[^\n]*','',stripped)
    if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):
        ap.error('proof placeholder or new axiom')
    if any(line!=line.rstrip() for line in code.splitlines()):
        ap.error('trailing whitespace')
    for kind,names in (('theorem',THEOREMS),('def',DEFS)):
        for name in names:
            if len(re.findall(r'(?m)^'+kind+r'\s+'+re.escape(name)+r'\b',code))!=1:
                ap.error('missing or duplicated '+kind+': '+name)
    if args.apply:
        add_missing(root,[IMPORT])
        add_missing(audit,[IMPORT],prepend=True)
        add_missing(audit,CHECKS)
    for path,required in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line)!=1:
                ap.error('missing/duplicate registration: '+str(path)+' '+line)
    print(f'PASS: full-output Z3 heat-step Wiener budget: {len(THEOREMS)} '
          f'theorems, {len(DEFS)} definitions, {len(CHECKS)} axiom probes')

if __name__=='__main__':main()
