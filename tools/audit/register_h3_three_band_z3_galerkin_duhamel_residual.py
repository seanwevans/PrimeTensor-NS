#!/usr/bin/env python3
"""Register actual full-output Z3 Galerkin Duhamel residual and quadratic clock bounds."""
from pathlib import Path
import argparse,re,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinDuhamelResidual')
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=(
    'thirdFullThreeBand_z3GalerkinHeatLag_le_clock244',
    'thirdFullThreeBand_z3GalerkinLaggedSource_norm_bound244',
    'thirdFullThreeBand_z3GalerkinLaggedSource_mass_bound244',
    'thirdFullThreeBand_z3GalerkinDuhamelClockIntegral244',
    'thirdFullThreeBand_z3GalerkinDuhamelResidual_integral_bound244',
    'thirdFullThreeBand_z3GalerkinDuhamelResidual25750000_100Ball244',
    'thirdFullThreeBand_z3GalerkinDuhamelCumulativeOmesh244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in THEOREMS for line in
    ('#check '+NS+name,'#print axioms '+NS+name))

def add_missing(path,entries,prepend=False):
    old=path.read_text(encoding='utf-8');present=set(old.splitlines())
    missing=[line for line in entries if line not in present]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,encoding='utf-8')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    m=p.add_mutually_exclusive_group(required=True)
    m.add_argument('--apply',action='store_true')
    m.add_argument('--check',action='store_true')
    args=p.parse_args()
    src=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'; audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for f in (src,root,audit):
        if not f.is_file():p.error('missing required '+str(f))
    code=src.read_text(encoding='utf-8')
    clean=re.sub(r'/-.*?-/', '', code,flags=re.S)
    clean=re.sub(r'--[^\n]*','',clean)
    if re.search(r'\b(?:sorry|admit|axiom)\b',clean):
        p.error('forbidden placeholder or axiom')
    if any(line!=line.rstrip() for line in code.splitlines()):
        p.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code))!=1:
            p.error('missing or duplicated theorem '+name)
    if args.apply:
        add_missing(root,[IMPORT])
        add_missing(audit,[IMPORT],prepend=True)
        add_missing(audit,CHECKS)
    for f,req in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=f.read_text(encoding='utf-8').splitlines()
        for q in req:
            if lines.count(q)!=1:
                p.error('missing or duplicate '+str(f)+': '+q)
    print(f'PASS: exact Z3 Duhamel residual: {len(THEOREMS)} theorems, {len(CHECKS)} trust probes')

if __name__=='__main__':main()
