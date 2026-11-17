#!/usr/bin/env python3
"""Register exact Galerkin field Lipschitz, strong temporal FTC, and norm integral."""
from pathlib import Path
import argparse,re,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongTemporalFTC')
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=(
 'thirdFullThreeBand_z3GalerkinLaplacianLowerReserve244',
 'thirdFullThreeBand_z3GalerkinNSFieldDifference_mass_bound244',
 'thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_100Ball244',
 'thirdFullThreeBand_z3GalerkinNSField_Lipschitz1010_highBall244',
 'thirdFullThreeBand_z3GalerkinStrongODE_FTC244',
 'thirdFullThreeBand_z3GalerkinStrongODE_normIncrement244',
 'thirdFullThreeBand_z3GalerkinStrongODE_WienerIntegralBound244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in THEOREMS for line in
             ('#check '+NS+name,'#print axioms '+NS+name))

def add_missing(path,entries,prepend=False):
 old=path.read_text(encoding='utf-8'); lines=set(old.splitlines())
 missing=[x for x in entries if x not in lines]
 if missing:
  block='\n'.join(missing)+'\n'
  path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,encoding='utf-8')

def main():
 p=argparse.ArgumentParser(description=__doc__)
 group=p.add_mutually_exclusive_group(required=True)
 group.add_argument('--apply',action='store_true')
 group.add_argument('--check',action='store_true')
 opts=p.parse_args()
 src=ROOT/(MODULE.replace('.','/')+'.lean')
 root=ROOT/'PrimeTensor.lean';audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
 for path in (src,root,audit):
  if not path.is_file():p.error(f'missing required: {path}')
 code=src.read_text(encoding='utf-8')
 stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
 stripped=re.sub(r'--[^\n]*','',stripped)
 if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):p.error('proof hole or axiom')
 if any(x!=x.rstrip() for x in code.splitlines()):p.error('trailing whitespace')
 for name in THEOREMS:
  if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code))!=1:
   p.error(f'missing/repeated theorem: {name}')
 if opts.apply:
  add_missing(root,(IMPORT,))
  add_missing(audit,(IMPORT,),prepend=True)
  add_missing(audit,CHECKS)
 for path,expected in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
  lines=path.read_text(encoding='utf-8').splitlines()
  for x in expected:
   if lines.count(x)!=1:p.error(f'missing/duplicate registration: {path} {x}')
 print(f'PASS: Z3 Galerkin strong temporal FTC: {len(THEOREMS)} theorems, {len(CHECKS)} axiom checks')

if __name__=='__main__':main()
