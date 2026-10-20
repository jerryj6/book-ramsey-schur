#!/usr/bin/env python3
"""Collect all UNSAT leaf artifacts into cert_pack/{family}/{case}/ with COVERAGE.csv"""
import os, glob, shutil, hashlib, csv, sys

def link_or_copy(src,dst):
    try:
        if os.path.exists(dst): os.remove(dst)
        os.link(src,dst)
    except OSError: shutil.copy2(src,dst)

ROOT=os.path.expanduser('~/math_hunt')
OUT=os.path.join(ROOT,'cert_pack')

res={}
for r in glob.glob(ROOT+'/runs/*/*.res'):
    c=os.path.basename(r)[:-4]; t=open(r).read()
    res[c]=('UNSAT' if 'UNSATISFIABLE' in t else 'SAT' if 'SATISFIABLE' in t else 'TIMEOUT')

def frontier(prefix):
    S=set(os.path.basename(d) for d in glob.glob(ROOT+f'/runs/degfix_{prefix}*') if os.path.isdir(d) and not d.endswith('_kissat'))
    S|={'degfix_'+os.path.basename(c)[:-5] for c in glob.glob(ROOT+f'/cubes/orig_degfix/{prefix}*.cube')}
    uns={c for c in S if 'UNSAT' in res.get(c,'')}
    def anc_unsat(c): return any(u!=c and c.startswith(u+'x') for u in uns)
    return sorted(c for c in S if ('UNSAT' in res.get(c,'') and not anc_unsat(c))
                  or ('UNSAT' not in res.get(c,'') and not any(o!=c and o.startswith(c+'x') for o in S)))

_frontier=frontier('origT_0129')
_frontier40=frontier('origT_0040')
# origT leaves whose own solve timed out but which are covered by a degfix subtree:
_SUBSUMED={129} | ({40} if _frontier40 else set())

# case -> (family, case_label, leaf_case_names)
# leaf sets that CLOSE each case (superseded timed-out leaves excluded where a refinement covers them)
CASES = {
 'b49_d00_26_mono':('b49','R(B4,B9)<=27 monolithic cases d00-d09,d11L-d15L,d16-d26',
    [f'b49_d{d:02d}' for d in list(range(0,10))+list(range(16,27))]+[f'b49_d{d}L' for d in range(11,16)]),
 'b49_d10_v123':('b49','R(B4,B9)<=27 case d10 (deg=10 band) via v1v2v3 count split',
    [f'b49d10v3_leaf_{i:04d}' for i in range(27)]),
 'r47_mono':('r47','R(B4,B7)<=22 monolithic: extremes d0-d5,d14-d21 + routeA d7,d8',
    [f'r47_d{d:02d}' for d in list(range(0,6))+list(range(14,22))]+['r47_d07ra','r47_d08ra']),
 'r47_d6':('r47','d6 singleton (lo6 hi10) via v1 count split',[f'r47d6_leaf_{i:04d}' for i in range(6)]),
 'r47_d11':('r47','d11 singleton via v1 split',[f'r47d11_leaf_{i:04d}' for i in range(7)]),
 'r47_d12':('r47','d12 singleton via v1 split',[f'r47d12_leaf_{i:04d}' for i in range(8)]),
 'r47_d13':('r47','d13 via v1 split (leaf_0008 refined by corner v12 split)',
    [f'r47d13_leaf_{i:04d}' for i in range(8)]+[f'd13c_leaf_{i:04d}' for i in [8,17,26,35,44,53,62,71,80]]),
 'r47_d7':('r47','d7 via v12 split (leaf_0015=(9,9) refined by v123 leaves 0060-0063)',
    [f'd7s_leaf_{i:04d}' for i in range(15)]+[f'd7v3_{i:04d}' for i in range(60,64)]),
 'r47_d8':('r47','d8 via v123 count split (all 27) + v12 stragglers',
    [f'd8v3all_leaf_{i:04d}' for i in range(27)]+[f'd8s_leaf_{i:04d}' for i in [1,3,4,5,6,7,8]]),
 'r47_d9':('r47','d9 routeA original 10-cube split (edge-var cubes, portable verbatim); leaf 004 re-covered by edge-OR splits (d9ra_004pos + d9ra_004n* frontier)',
    [f'd9ra_{i:03d}' for i in range(10) if i != 4]+['d9ra_004pos']
    + sorted(c for c in (os.path.basename(d) for d in glob.glob(ROOT+'/runs/d9ra_004n*') if os.path.isdir(d))
             if c != 'd9ra_004neg' and ('UNSAT' in res.get(c,'') or not any(
                 os.path.basename(d)!=c and os.path.basename(d).startswith(c) for d in glob.glob(ROOT+'/runs/d9ra_004n*'))))),
 'r47_d10':('r47','d10 via v12 split; (10,10) corner refined v123 then v1234 then v12345',
    [f'd10s_leaf_{i:04d}' for i in range(24)]+[f'd10v3_{i:04d}' for i in range(120,124)]
    +[f'd10v4_{i}' for i in range(620,624)]+[f'd10v5_{i}' for i in range(3120,3124)]),
 'r47_d10_replay':('r47','d10 authoritative cover: 312 original-manifest leaf cubes, aux vars decoded to edge literals (origT_*); leaves 0129/0040 covered by degfix count-pin + edge-OR descent frontier (degfix_origT_0129*/origT_0040*)',
    [f'origT_{i:04d}' for i in range(312) if i not in _SUBSUMED]
    + _frontier + _frontier40),
 'controls':('controls','SAT controls (encoder sanity): N=16 B3B5 val, N=21 B4B7, N=26 B4B9',
    ['val_N16_35','val_N17_35','ctrl_N21_47','ctrl_N26_49']),
}

rows=[]; missing=[]
for key,(fam,desc,cases) in CASES.items():
    dst=os.path.join(OUT,fam,key); os.makedirs(dst,exist_ok=True)
    for c in cases:
        rd=f'{ROOT}/runs/{c}'; v=res.get(c,'NORUN')
        sha=''; sz=''
        lf=f'{rd}/{c}.lrat.gz'
        if v=='UNSAT' and os.path.exists(lf):
            sha=hashlib.sha256(open(lf,'rb').read()).hexdigest()
            sz=os.path.getsize(lf)
        rows.append([key,fam,c,v,sz,sha])
        if v not in ('UNSAT','SAT'): missing.append(c)
        # copy artifacts
        for ext in ['.cnf','.res','.log']:
            src=f'{rd}/{c}{ext}'
            if os.path.exists(src): link_or_copy(src,os.path.join(dst,c+ext))
        if v=='UNSAT' and os.path.exists(lf): link_or_copy(lf,os.path.join(dst,c+'.lrat.gz'))
        # cube file used
        cf=f'{rd}/{c}.cube'
        if os.path.exists(cf): link_or_copy(cf,os.path.join(dst,c+'.cube'))

with open(OUT+'/COVERAGE.csv','w',newline='') as f:
    w=csv.writer(f); w.writerow(['case_group','family','leaf','verdict','lrat_gz_bytes','sha256'])
    w.writerows(rows)
print('missing/nonfinal:',missing)
print('wrote',OUT)
