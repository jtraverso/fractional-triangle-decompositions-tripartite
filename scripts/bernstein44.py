"""Regenerates PartiteFractional/Bernstein44.lean.

Exact rational arithmetic only (fractions.Fraction). For the two polynomials of Case 3 of the
proof of Proposition 4.4 it subdivides the box until every Bernstein coefficient is nonnegative,
and writes one Lean lemma per piece (a `linear_combination` of the Bernstein products with the
exact coefficients) and the case split over the pieces.

Usage: python scripts/bernstein44.py [output path]
"""
from fractions import Fraction as F
from math import comb
import sys
def mul(p,q):
    r={}
    for (a,b),c in p.items():
        for (e,g),h in q.items():
            r[(a+e,b+g)]=r.get((a+e,b+g),0)+c*h
    return {k:v for k,v in r.items() if v!=0}
def add(*ps):
    r={}
    for p in ps:
        for k,v in p.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v!=0}
def sc(c,p): return {k:F(c)*v for k,v in p.items()}
def C(c): return {(0,0):F(c)}
S={(1,0):F(1)}; T={(0,1):F(1)}
def shift_scale(p,a,h,b,g):
    r={}
    for (i,j),c in p.items():
        for k in range(i+1):
            for l in range(j+1):
                r[(k,l)]=r.get((k,l),0)+c*comb(i,k)*a**(i-k)*h**k*comb(j,l)*b**(j-l)*g**l
    return r
def degs(p): return max(i for i,j in p), max(j for i,j in p)
def bern(p,box,n,m):
    (a1,a2),(b1,b2)=box
    q=shift_scale(p,a1,a2-a1,b1,b2-b1)
    B={}
    for I in range(n+1):
        for J in range(m+1):
            B[(I,J)]=sum(q.get((i,j),0)*F(comb(I,i)*comb(J,j),comb(n,i)*comb(m,j)) for i in range(I+1) for j in range(J+1))
    return B
d0=F(4621,20000); q0=F(83666,10000)  # sqrt 70 >= 8.3666
s2=mul(S,S); t2=mul(T,T)
ms_y=add(sc(2*q0,S),C(-1),sc(-10,s2))   # 6 s^2 msq(y)
ms_x=add(sc(2*q0,T),C(-1),sc(-10,t2))
base=add(mul(mul(add(t2,C(-d0)),t2),ms_y), mul(mul(add(s2,C(-d0)),s2),ms_x), sc(-6,mul(s2,t2)))
one_m=add(C(1),sc(-1,t2),sc(-1,s2))
P_lin=add(base, mul(mul(s2,add(C(7),sc(-10,t2))),one_m))
P_half=add(base, sc(3,mul(s2,one_m)))
def tree(P,box,outside,dep=0):
    n,m=degs(P)
    if outside(box): return ('out',box)
    B=bern(P,box,n,m)
    if min(B.values())>=0: return ('leaf',box,B)
    if dep>30: raise Exception('fail %s'%(box,))
    (a1,a2),(b1,b2)=box
    if a2-a1>=b2-b1:
        mid=(a1+a2)/2; return ('split','s',mid,tree(P,((a1,mid),(b1,b2)),outside,dep+1),tree(P,((mid,a2),(b1,b2)),outside,dep+1))
    mid=(b1+b2)/2; return ('split','t',mid,tree(P,((a1,a2),(b1,mid)),outside,dep+1),tree(P,((a1,a2),(mid,b2)),outside,dep+1))
def count(tr):
    if tr[0]=='split': a=count(tr[3]); b=count(tr[4]); return (a[0]+b[0],a[1]+b[1])
    return (1,0) if tr[0]=='leaf' else (0,1)
out=lambda b: b[0][0]>b[1][1] or b[0][0]**2+b[1][0]**2>1

import sys
from fractions import Fraction as F
from math import comb
def fr(x):
    x=F(x)
    return '(%d : ℝ)'%x.numerator if x.denominator==1 else '(%d / %d : ℝ)'%(x.numerator,x.denominator)
_unused=[]
def emit_poly(name, P, box, lean_def, doc):
    n,m=degs(P)
    tr=tree(P,box,out)
    leaves=[]
    def collect(t):
        if t[0]=='split': collect(t[3]); collect(t[4])
        elif t[0]=='leaf': leaves.append(t)
        else: raise Exception('outside leaf not supported')
    collect(tr)
    L=[]
    L.append('/-- %s -/'%doc)
    L.append('noncomputable def %s (s t : ℝ) : ℝ :=\n  %s\n'%(name,lean_def))
    for idx,(kind,bx,B) in enumerate(leaves):
        (a,b),(c,e)=bx
        L.append('theorem %s_leaf%d {s t : ℝ} (h1 : %s ≤ s) (h2 : s ≤ %s) (h3 : %s ≤ t) (h4 : t ≤ %s) :\n    0 ≤ %s s t := by'%(name,idx,fr(a),fr(b),fr(c),fr(e),name))
        L.append('  have u1 : 0 ≤ s - %s := by linarith'%fr(a))
        L.append('  have u2 : 0 ≤ %s - s := by linarith'%fr(b))
        L.append('  have v1 : 0 ≤ t - %s := by linarith'%fr(c))
        L.append('  have v2 : 0 ≤ %s - t := by linarith'%fr(e))
        terms=[]
        for (I,J),bij in sorted(B.items()):
            coef=bij*comb(n,I)*comb(m,J)/((b-a)**n*(e-c)**m)
            if coef==0: continue
            hn='k%d_%d'%(I,J)
            L.append('  have %s : 0 ≤ (s - %s) ^ %d * (%s - s) ^ %d * (t - %s) ^ %d * (%s - t) ^ %d :=\n    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg u1 _) (pow_nonneg u2 _)) (pow_nonneg v1 _))\n      (pow_nonneg v2 _)'%(hn,fr(a),I,fr(b),n-I,fr(c),J,fr(e),m-J))
            terms.append('%s * %s'%(fr(coef),hn))
        L.append('  unfold %s'%name)
        L.append('  linear_combination ' + ' +\n    '.join(terms))
        L.append('')
    # tree theorem
    def code(t,ind):
        p=' '*ind
        if t[0]=='leaf':
            return [p+'exact %s_leaf%d (by linarith) (by linarith) (by linarith) (by linarith)'%(name,leaves.index(t))]
        _,var,mid,l,r=t
        res=[p+'rcases le_total %s %s with h | h'%(var,fr(mid))]
        res.append(p+'· '+code(l,ind+2)[0].strip()); res+=code(l,ind+2)[1:]
        res.append(p+'· '+code(r,ind+2)[0].strip()); res+=code(r,ind+2)[1:]
        return res
    (a,b),(c,e)=box
    L.append('theorem %s_nonneg {s t : ℝ} (h1 : %s ≤ s) (h2 : s ≤ %s) (h3 : %s ≤ t) (h4 : t ≤ %s) :\n    0 ≤ %s s t := by'%(name,fr(a),fr(b),fr(c),fr(e),name))
    L+=code(tr,2)
    L.append('')
    print(name, len(leaves), file=sys.stderr)
    return L
d0s='(4621 / 20000 : ℝ)'; q0s='(83666 / 10000 : ℝ)'
base='(t ^ 2 - %s) * t ^ 2 * (2 * %s * s - 1 - 10 * s ^ 2) +\n    (s ^ 2 - %s) * s ^ 2 * (2 * %s * t - 1 - 10 * t ^ 2) - 6 * s ^ 2 * t ^ 2'%(d0s,q0s,d0s,q0s)
lin=emit_poly('polyLin',P_lin,((F(48,100),F(71,100)),(F(632,1000),F(837,1000))),
  base+' +\n    s ^ 2 * (7 - 10 * t ^ 2) * (1 - t ^ 2 - s ^ 2)',
  '`6 s² t² (B_d(t², s²) - 1)` with `√70` replaced by `8.3666`, where `f(x) = (7 - 10x)/6`.')
half=emit_poly('polyHalf',P_half,((F(48,100),F(633,1000)),(F(48,100),F(633,1000))),
  base+' +\n    3 * s ^ 2 * (1 - t ^ 2 - s ^ 2)',
  '`6 s² t² (B_d(t², s²) - 1)` with `√70` replaced by `8.3666`, where `f(x) = 1/2`.')
hdr='''/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Real.Basic

/-!
# Polynomial inequalities for Proposition 4.4

The two-variable inequalities of Case 3 of the proof of Proposition 4.4, with `x = t²` and
`y = s²`, `d = 0.23105` and `√70 ≥ 8.3666`. Each is proved on a box by subdividing it and writing
the polynomial on every piece as a nonnegative combination of the Bernstein products
`(s - a)^i (b - s)^(4-i) (t - c)^j (e - t)^(4-j)`. The subdivisions and the coefficients were
computed in exact rational arithmetic by a script; Lean checks each identity with `ring`.
-/

@[expose] public section

namespace ABLP

'''
open(sys.argv[1] if len(sys.argv)>1 else 'PartiteFractional/Bernstein44.lean','w',encoding='utf-8').write(hdr+'\n'.join(lin+half)+'\nend ABLP\n')
