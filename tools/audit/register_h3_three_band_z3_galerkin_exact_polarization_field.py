#!/usr/bin/env python3
"""Register exact complex Galerkin polarization and uniform NS field speed."""
from pathlib import Path
import argparse, re, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinExactPolarizationField')
NS='PrimeTensor.FirstMonomialTriad.'
DEFS=(
    'thirdFullThreeBandZ3GalerkinLaplacianWiener244',
    'thirdFullThreeBandZ3GalerkinNSField244',
)
THEOREMS=(
    'thirdFullThreeBand_z3ComplexTransport_sub_left244',
    'thirdFullThreeBand_z3ComplexTransport_sub_right244',
    'thirdFullThreeBand_z3GalerkinQuadratic_sub_left244',
    'thirdFullThreeBand_z3GalerkinQuadratic_sub_right244',
    'thirdFullThreeBand_z3GalerkinQuadratic_exactPolarization244',
    'thirdFullThreeBand_z3GalerkinSourceDiff_1000_middle244',
    'thirdFullThreeBand_z3GalerkinSourceDiff_1000_lower244',
    'thirdFullThreeBand_z3GalerkinLaplacianWiener_reserved244',
    'thirdFullThreeBand_z3GalerkinNSField_mass_bound244',
    'thirdFullThreeBand_z3GalerkinNSField_speed51000_100Ball244',
    'thirdFullThreeBand_z3GalerkinLaplacianSource5000000_100Ball244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in (*DEFS,*THEOREMS)
             for line in ('#check '+NS+name, '#print axioms '+NS+name))

def add_missing(path,lines,prepend=False):
    old=path.read_text(encoding='utf-8'); present=set(old.splitlines())
    missing=[line for line in lines if line not in present]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+old if prepend else
                        old.rstrip('\n')+'\n'+block,encoding='utf-8')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=p.parse_args()
    source=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'; audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for f in (source,root,audit):
        if not f.is_file():p.error('missing '+str(f))
    code=source.read_text(encoding='utf-8')
    clean=re.sub(r'/-.*?-/', '', code, flags=re.S)
    clean=re.sub(r'--[^\n]*','',clean)
    if re.search(r'\b(?:sorry|admit|axiom)\b',clean):p.error('placeholder or new axiom')
    if any(line!=line.rstrip() for line in code.splitlines()):p.error('trailing whitespace')
    for kind,names in (('def',DEFS),('theorem',THEOREMS)):
        for name in names:
            if len(re.findall(r'(?m)^'+kind+r'\s+'+re.escape(name)+r'\b',code))!=1:
                p.error('missing/duplicate '+kind+' '+name)
    if args.apply:
        add_missing(root,(IMPORT,))
        add_missing(audit,(IMPORT,),prepend=True)
        add_missing(audit,CHECKS)
    for f,required in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        ls=f.read_text(encoding='utf-8').splitlines()
        for line in required:
            if ls.count(line)!=1:p.error('missing/duplicate '+str(f)+' '+line)
    print(f'PASS: exact Z3 Galerkin polarization and field speed: '
          f'{len(THEOREMS)} theorems, {len(DEFS)} defs, {len(CHECKS)} probes')

if __name__=='__main__':main()
