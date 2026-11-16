#!/usr/bin/env python3
"""Register cutoff-free Galerkin residual stability and cumulative Wiener debt."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinResidualBudget')
NS='PrimeTensor.FirstMonomialTriad.'
DEFS=('thirdFullThreeBandZ3GalerkinStepResidual244',)
THEOREMS=(
 'thirdFullThreeBand_z3GalerkinStepResidual_nonneg244',
 'thirdFullThreeBand_z3GalerkinMass_le_step_add_residual244',
 'thirdFullThreeBand_z3GalerkinResidualHeatBudget244',
 'thirdFullThreeBand_z3GalerkinCumulativeResidualBudget244',
 'thirdFullThreeBand_z3GalerkinCumulativeHeatDebt_nonneg244',
 'thirdFullThreeBand_z3GalerkinResidualSum_quadraticMesh244',
 'thirdFullThreeBand_z3GalerkinCumulativeOmeshBudget244',
 'thirdFullThreeBand_z3Laplacian_le_degreeSquare244',
 'thirdFullThreeBand_z3GalerkinAnalyticReserveSource244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in (*DEFS,*THEOREMS)
             for line in ('#check '+NS+name, '#print axioms '+NS+name))


def add_missing(path,entries,prepend=False):
    old=path.read_text(encoding='utf-8')
    present=set(old.splitlines())
    missing=[line for line in entries if line not in present]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,
                        encoding='utf-8')


def run():
    p=argparse.ArgumentParser(description=__doc__)
    action=p.add_mutually_exclusive_group(required=True)
    action.add_argument('--apply',action='store_true')
    action.add_argument('--check',action='store_true')
    args=p.parse_args()
    src=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'
    audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for f in (src,root,audit):
        if not f.is_file():p.error('missing required '+str(f))
    code=src.read_text(encoding='utf-8')
    stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
    stripped=re.sub(r'--[^\n]*','',stripped)
    if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):
        p.error('forbidden placeholder or axiom')
    if any(line!=line.rstrip() for line in code.splitlines()):
        p.error('trailing whitespace')
    for kind,names in (('def',DEFS),('theorem',THEOREMS)):
        for name in names:
            if len(re.findall(r'(?m)^'+kind+r'\s+'+re.escape(name)+r'\b',code))!=1:
                p.error('missing or duplicated '+kind+' '+name)
    if args.apply:
        add_missing(root,[IMPORT])
        add_missing(audit,[IMPORT],prepend=True)
        add_missing(audit,CHECKS)
    for f,lines in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        existing=f.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if existing.count(line)!=1:
                p.error('missing or duplicate registration '+str(f)+' '+line)
    print(f'PASS: Z3 Galerkin residual-budget registration: '
          f'{len(THEOREMS)} theorems, {len(DEFS)} defs, {len(CHECKS)} trust probes')

if __name__=='__main__':run()
