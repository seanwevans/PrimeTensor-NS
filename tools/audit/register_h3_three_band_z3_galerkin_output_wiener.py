#!/usr/bin/env python3
"""Register genuine Z3 projected Galerkin output Wiener source theorems."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinOutputWiener')
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=(
 'thirdFullThreeBand_z3ComplexFrequency_norm_le_degree244',
 'thirdFullThreeBand_z3ComplexOrderedWiener_unconditional244',
 'thirdFullThreeBand_z3GalerkinQuadratic_norm_le244',
 'thirdFullThreeBand_z3GalerkinAllOutputWienerBound244',
)
DEFS=('thirdFullThreeBandZ3GalerkinQuadratic244',)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in (*DEFS,*THEOREMS)
             for line in ('#check '+NS+name,'#print axioms '+NS+name))

def add_missing(path,entries,prepend=False):
 old=path.read_text(encoding='utf-8')
 existing=set(old.splitlines())
 missing=[line for line in entries if line not in existing]
 if missing:
  block='\n'.join(missing)+'\n'
  path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,encoding='utf-8')

def main():
 p=argparse.ArgumentParser(description=__doc__)
 mode=p.add_mutually_exclusive_group(required=True)
 mode.add_argument('--apply',action='store_true')
 mode.add_argument('--check',action='store_true')
 args=p.parse_args()
 src=ROOT/(MODULE.replace('.','/')+'.lean')
 root=ROOT/'PrimeTensor.lean'
 audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
 for path in (src,root,audit):
  if not path.is_file():p.error('missing '+str(path))
 code=src.read_text(encoding='utf-8')
 stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
 stripped=re.sub(r'--[^\n]*','',stripped)
 if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):p.error('proof placeholder or new axiom')
 if any(line!=line.rstrip() for line in code.splitlines()):p.error('trailing whitespace')
 for kind,names in (('theorem',THEOREMS),('def',DEFS)):
  for name in names:
   if len(re.findall(r'(?m)^'+kind+r'\s+'+re.escape(name)+r'\b',code))!=1:
    p.error('missing/duplicate '+kind+' '+name)
 if args.apply:
  add_missing(root,(IMPORT,))
  add_missing(audit,(IMPORT,),prepend=True)
  add_missing(audit,CHECKS)
 for path,required in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
  lines=path.read_text(encoding='utf-8').splitlines()
  for line in required:
   if lines.count(line)!=1:p.error('missing/duplicate registration: '+str(path)+' '+line)
 print(f'PASS: Z3 projected Galerkin complete-output Wiener ('
       f'{len(THEOREMS)} theorems, {len(DEFS)} definitions, {len(CHECKS)} probes)')

if __name__=='__main__':main()
