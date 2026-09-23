#!/usr/bin/env python3
"""Independent finite certificate checks for Fauzan's September 2026 manuscript.

Run from any directory: python3 certificates/verify.py
Uses only Python's standard library. All acceptance decisions use integers,
Fractions or outward-rounded dyadic intervals; displayed decimals are not used
for decisions. This is NOT a Lean/kernel certificate and does not verify the
infinite/asymptotic parts of the proof.
"""
from __future__ import annotations
import json
import hashlib
from decimal import Decimal, localcontext
from fractions import Fraction as F
from pathlib import Path
from functools import lru_cache
import sys
from interval import IV, BITS, SCALE, log, atan, pi

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'data'
alpha=F(3,40); lam=F(37,40); H=F(23,20)

def load(name):
    return json.loads((DATA/name).read_text())

def dec(x: F) -> str:
    with localcontext() as c:
        c.prec=24
        return str(Decimal(x.numerator)/Decimal(x.denominator))

def require(b: bool, msg: str):
    if not b: raise AssertionError(msg)


def verify_A():
    raw=load('arcsine.json'); den=raw['denominator']
    rows=[tuple(F(v,den) for v in r) for r in raw['rows']]
    require(sum(c for a,b,c in rows)==lam,'mass')
    require(all(0<a<b<2 and c>0 and b-a>F(1,225) for a,b,c in rows),'positive lengths')
    require(all(rows[j+1][0]<rows[j][0]<rows[j][1]<rows[j+1][1] for j in range(15)),'nesting')
    caps=[log(IV.of((b-a)/4)) for a,b,c in rows]

    @lru_cache(maxsize=None)
    def potential(t: F):
        ans=IV.of(0)
        for (a,b,c),cap in zip(rows,caps):
            if a<=t<=b:
                u=cap
            else:
                arg=(IV.of(abs(t-(a+b)/2))+IV.of((t-a)*(t-b)).sqrt())/2
                u=log(arg)
            ans+=c*u
        return ans

    @lru_cache(maxsize=None)
    def V(t: F):
        if t==0: return -12*alpha*log(IV.of(alpha))-2+12*alpha
        root=IV.of(t).sqrt()
        return (log(IV.of(1+t))-6*alpha*log(IV.of(t+alpha**2))-2+12*alpha
                +2*root*(pi()+atan(1/root)-6*atan(alpha/root)))

    def phi_prime(t: F):
        root=IV.of(t).sqrt()
        return 2*(pi()+atan(1/root)-6*atan(alpha/root))

    qm=F(59205077,10**10); qp=F(59205079,10**10)
    require(phi_prime(qm).lt(0),'lower minimizer bracket')
    require(phi_prime(qp).gt(0),'upper minimizer bracket')
    par=pi()+atan(1/IV.of(qp).sqrt())-6*atan(alpha/IV.of(qm).sqrt())
    require(par.lt(0),'Vstar sign')
    Vstar=(log(IV.of(1+qm))-6*alpha*log(IV.of(qp+alpha**2))-2+12*alpha
           +2*IV.of(qp).sqrt()*par)
    endpoints=[F(0)]+[a for a,b,c in reversed(rows)]+[qm,qp]+[b for a,b,c in rows]+[F(2)]
    require(len(endpoints)==36 and all(a<b for a,b in zip(endpoints,endpoints[1:])),'ordered endpoints')
    cells=[]
    for j,d,ranges in load('partition.json')['rows']:
        for kl,kr in ranges:
            for k in range(kl,kr+1):
                l=endpoints[j]+(endpoints[j+1]-endpoints[j])*F(k,2**d)
                r=endpoints[j]+(endpoints[j+1]-endpoints[j])*F(k+1,2**d)
                require(endpoints[j]<=l<r<=endpoints[j+1],'cell domain')
                cells.append((l,r,j,d,k))
    cells.sort()
    require(cells[0][0]==0 and cells[-1][1]==2,'partition ends')
    require(all(a[1]==b[0] for a,b in zip(cells,cells[1:])),'partition gaps or overlaps')
    threshold=F(-6645002,10**6)
    records=[]; worst=None
    for l,r,j,d,k in cells:
        pl=potential(l); pr=potential(r)
        mx=IV(max(pl.lo,pr.lo),max(pl.hi,pr.hi))
        lowV=V(r) if r<=qm else V(l) if l>=qp else Vstar
        bound=2*mx-lowV
        require(bound.lt(threshold),f'potential cell {(j,d,k)}')
        if worst is None or bound.hi>worst[0].hi: worst=(bound,(j,d,k))
        records.append({'j':j,'d':d,'k':k,'l':str(l),'r':str(r),'B':bound.json()})
    accum=F(0); energy=IV.of(0)
    for (a,b,c),cap in zip(rows,caps):
        old=accum; accum+=c
        energy+=(accum**2-old**2)*cap
    Cstar=-2*lam+12*alpha*lam*(1-log(IV.of(alpha)))+3*lam**2-2*lam**2*log(IV.of(2*lam))
    require(energy.gt(F(-2126593445148,10**12)) and energy.lt(F(-2126593445147,10**12)),'energy enclosure')
    require(Cstar.gt(F(2653035990340,10**12)) and Cstar.lt(F(2653035990341,10**12)),'Cstar enclosure')
    real=lam*F(-1329,200)-energy+Cstar
    require(real.lt(F(-2733991,2000000)),'real constant')
    kappa=(2*pi()/IV.of(3).sqrt()+log(IV.of(F(4,3)))+F(9,20)*log(IV.of(18))
           +lam*(1+log(IV.of(F(1600,111))))
           +2*lam*log((43+4*IV.of(114).sqrt())/5))
    require(kappa.gt(F(2773171335773,200000000000)) and kappa.lt(F(6932928339433,500000000000)),'kappa narrow enclosure')
    require(kappa.lt(F(6933,500)),'kappa ceiling')
    output={'arithmetic':'outward-rounded dyadic intervals','bits':BITS,'cell_count':len(cells),
            'worst_cell':list(worst[1]),'worst_B':worst[0].json(),'energy':energy.json(),
            'Cstar':Cstar.json(),'real_quadratic_coefficient':real.json(),'kappa':kappa.json(),'cells':records}
    print(f'Appendix A: {len(cells)} cells PASS; worst B upper = {dec(F(worst[0].hi,SCALE))}')
    print(f'  energy upper = {dec(F(energy.hi,SCALE))}; kappa upper = {dec(F(kappa.hi,SCALE))}')
    return output

# Small exact polynomial class. Coefficients are in increasing degree order.
class Poly:
    def __init__(self, *c):
        if len(c)==1 and isinstance(c[0],Poly): c=c[0].c
        if not c: c=(0,)
        a=[F(v) for v in c]
        while len(a)>1 and a[-1]==0: a.pop()
        self.c=tuple(a)
    @staticmethod
    def of(x): return x if isinstance(x,Poly) else Poly(x)
    def __add__(self,other):
        b=Poly.of(other); n=max(len(self.c),len(b.c))
        return Poly(*( (self.c[i] if i<len(self.c) else 0)+(b.c[i] if i<len(b.c) else 0) for i in range(n)))
    __radd__=__add__
    def __neg__(self): return Poly(*(-x for x in self.c))
    def __sub__(self,other): return self+-Poly.of(other)
    def __rsub__(self,other): return Poly.of(other)+-self
    def __mul__(self,other):
        b=Poly.of(other); c=[F(0)]*(len(self.c)+len(b.c)-1)
        for i,x in enumerate(self.c):
            for j,y in enumerate(b.c): c[i+j]+=x*y
        return Poly(*c)
    __rmul__=__mul__
    def __truediv__(self,k): return self* (1/F(k))
    def __pow__(self,n):
        a=Poly(1)
        for _ in range(n): a=a*self
        return a
    def __call__(self,x):
        ans=F(0)
        for v in reversed(self.c): ans=ans*x+v
        return ans
    def __eq__(self,other): return self.c==Poly.of(other).c
    def json(self): return [str(v) for v in self.c]

X=Poly(0,1)

def affine_nonnegative(p,l,r):
    require(len(p.c)<=2,'branch expression not affine')
    require(p(l)>=0 and p(r)>=0,'unrecorded branch crossing')

def pick_min(a,b,l,r):
    a=Poly.of(a); b=Poly.of(b)
    if a((l+r)/2)<=b((l+r)/2):
        affine_nonnegative(b-a,l,r); return a
    affine_nonnegative(a-b,l,r); return b

def pos(a,l,r): return -pick_min(-Poly.of(a),0,l,r)

def floor_affine(p,l,r):
    require(len(p.c)<=2,'non-affine floor input')
    m=p((l+r)/2)//1
    affine_nonnegative(p-m,l,r); affine_nonnegative(m+1-p,l,r)
    # Endpoints may attain m+1; the open interval stays in the chosen branch.
    require(p((l+r)/2)<m+1,'floor branch at midpoint')
    return int(m)

def pieces_R(l,r):
    f=X-floor_affine(X,l,r); g=alpha*X-floor_affine(alpha*X,l,r)
    df=pick_min(f,1-f,l,r); dg=pick_min(g,1-g,l,r)
    ef=1 if f((l+r)/2)<=F(1,2) else -1
    eg=1 if g((l+r)/2)<=F(1,2) else -1
    affine_nonnegative(F(1,2)-f if ef==1 else f-F(1,2),l,r)
    affine_nonnegative(F(1,2)-g if eg==1 else g-F(1,2),l,r)
    q=floor_affine(2*X,l,r); T=floor_affine(2*H*X,l,r)
    tau=2*H*X-T; sigma=2*X-q
    eta=2*lam*X-floor_affine(2*lam*X,l,r)
    mixed=ef*eg*(pick_min(df,dg,l,r)-2*df*dg)
    square=dg*(1-2*dg)
    R_alt=(X*(4*lam+2*lam*f-12*lam*g)
           +(tau*(tau-sigma)-pos(tau-sigma,l,r)+eta*(1-eta))/2+9*square-3*mixed)
    # Recompute Gamma from its original integral, integrating exactly on the
    # z-strips determined by df and dg. Endpoint order is certified on [l,r].
    zs=[Poly(0),df,dg,Poly(F(1,2))]
    zs.sort(key=lambda a:a((l+r)/2))
    unique=[]
    for z in zs:
        if not unique or z!=unique[-1]: unique.append(z)
    gamma=Poly(0)
    for za,zb in zip(unique,unique[1:]):
        affine_nonnegative(zb-za,l,r)
        zmid=(za+zb)/2
        ia=1 if zmid((l+r)/2)<df((l+r)/2) else 0
        ib=1 if zmid((l+r)/2)<dg((l+r)/2) else 0
        affine_nonnegative(df-zmid if ia else zmid-df,l,r)
        affine_nonnegative(dg-zmid if ib else zmid-dg,l,r)
        ell=2*X+ef*(ia-2*df)
        b=3*(2*alpha*X+eg*(ib-2*dg))
        gamma+=(zb-za)*(T-b)*(T+b-ell-5)
    s=H*X-F(T,2); nplus=(2*X-q)/2
    gamma+=s*(2*T-q-5)+pos(s-nplus,l,r)
    mm=floor_affine(2*lam*X,l,r)
    J=mm*lam*X-F(mm*(mm+1),4)
    NN=2*lam*X*floor_affine(X,l,r)-12*lam*X*floor_affine(alpha*X,l,r)-2*J
    R_original=-gamma-NN
    require(R_original==R_alt,'original Gamma definition and F/Q expansion disagree')
    require(len(R_original.c)<=2,'R not affine')
    return R_original

def outer_poly(l,r):
    y=X
    if r<=F(1,2):
        R0=8-9*y-8*alpha-5*pick_min(alpha,1-2*y,l,r)-5*pos(1+alpha-3*y,l,r)
        d=pos(1+4*alpha-3*y-pos(1+alpha-3*y,l,r),l,r)
    elif r<=1:
        R0=7*(1-y)-6*pick_min(alpha,1-y,l,r)-6*pos(1+alpha-2*y,l,r)+pos(1+4*alpha-2*y,l,r)
        d=Poly(0)
    else: R0=Poly(0); d=Poly(0)
    m=int((1/((l+r)/2))//1)
    require(1/r>=m and 1/l<=m+1,'outer floor branch')
    return R0-d-2*lam*m+sum((pos(2*lam-j*y,l,r) for j in range(1,6)),Poly(0))

def verify_B():
    points={F(3),F(20)}
    for c in {F(2),2*alpha,2*lam,2*H,4*alpha,2*(1-alpha),2*(1+alpha)}:
        for k in range(int(3*c),int(20*c)+2):
            t=F(k)/c
            if 3<t<20: points.add(t)
    pts=sorted(points)
    require(len(pts)-1==143,'inner partition size')
    total=F(0); units=[F(0)]*17; records=[]
    for l,r in zip(pts,pts[1:]):
        P=pieces_R(l,r)
        b=P.c[0]; a=P.c[1] if len(P.c)>1 else F(0)
        value=a*(1/l-1/r)+b*F(1,2)*(1/l**2-1/r**2)
        total+=value
        idx=int(((l+r)/2)//1)-3
        require(3+idx<=l<r<=4+idx,'unit partition')
        units[idx]+=value
        records.append({'l':str(l),'r':str(r),'coefficients':P.json(),'integral':str(value)})
    require(units==[F(x) for x in load('inner_unit_integrals.json')['values']],'inner unit integrals')
    expected=F(322437603634266857629,7535670527041937280000)
    require(total==expected,'inner total')
    outer=F(0); outrecs=[]
    for raw in load('outer_pieces.json')['rows']:
        l,r,b,c=map(F,raw)
        P=outer_poly(l,r)
        require(P==Poly(b,c),f'outer table piece {l},{r}')
        val=b*(r-l)+c*(r*r-l*l)/2
        outer+=val
        outrecs.append({'l':str(l),'r':str(r),'b':str(b),'c':str(c),'integral':str(val)})
    require(outer==F(127751,96000),'outer total')
    Astar=outer+total-F(2689,48000)
    require(Astar==F(9928298118277006344769,7535670527041937280000),'Astar')
    U=F(-2733991,2000000)
    def AM(m): return Astar+7*lam/m-(F(2923,240)-F(1,4))/m**2+F(32,m**3)
    margin200=-1600*(AM(200)+U)-F(139,5)
    margin100000=-1600*(AM(100000)+U)-F(7907,100)
    require(margin200==F(3089837638249482469,58872425992515135000),'first margin')
    require(margin100000==F(29873543950273155160680943,3679526624532195937500000000),'second margin')
    require(margin200>0 and margin100000>0,'positive final margins')
    require(F(6933,500)*F(75,4)-260==F(-1,80),'approximation product')
    require(F(79,1600)-lam/F(75,4)==F(1,24000),'approximation slack')
    # Independent elementary tail-bound arithmetic.
    tail20=-lam/20-F(37,2)/400+F(2923,240)/400+F(32,20**3)+F(13,16*20**2)
    require(tail20==F(-2689,48000),'tail at 20')
    print(f'Appendix B: 143 symbolic inner pieces, 11 outer pieces PASS')
    print(f'  inner={total}; outer={outer}; margins strictly positive')
    return {'inner_total':str(total),'outer_total':str(outer),'inner_pieces':records,
            'outer_pieces':outrecs,'Astar':str(Astar),'A200':str(AM(200)),
            'A100000':str(AM(100000)),'margin200':str(margin200),
            'margin100000':str(margin100000)}

if __name__=='__main__':
    a=verify_A(); b=verify_B()
    report={'status':'PASS','scope':'finite rational/interval certificates only; not Lean-verified',
            'source_sha256':'a42c05ccc46b9a7c36428913453c4617202c59109713ba20f464ab9ec640d0da',
            'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in sorted(list(DATA.glob('*.json'))+[Path(__file__),ROOT/'certificates'/'interval.py'])},
            'appendix_A':a,'appendix_B':b}
    out=ROOT/'certificates'/'verification_results.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    print('Wrote',out)
