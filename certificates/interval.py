"""Outward-rounded dyadic interval arithmetic. No float is used in any check.

An interval (lo,hi) denotes [lo/2**BITS, hi/2**BITS]. Every operation rounds
outward with integer arithmetic. log/atan use finite series with explicit
remainder bounds. sqrt uses math.isqrt, followed by integer inequalities.
This is a reproducible mathematical computation, not a Lean proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import isqrt

BITS = 192
SCALE = 1 << BITS

def ceil_div(a: int, b: int) -> int:
    if b <= 0: raise ValueError("positive divisor required")
    return -((-a) // b)

@dataclass(frozen=True)
class IV:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError('reversed interval')

    @classmethod
    def of(cls, x: int | Fraction | str | IV) -> IV:
        if isinstance(x, cls):
            return x
        q = Fraction(x)
        return cls((q.numerator*SCALE)//q.denominator,
                   ceil_div(q.numerator*SCALE, q.denominator))

    @classmethod
    def bounds(cls, lo: Fraction, hi: Fraction) -> IV:
        return cls(cls.of(lo).lo, cls.of(hi).hi)

    def __add__(self, other) -> IV:
        b = IV.of(other)
        return IV(self.lo+b.lo,self.hi+b.hi)
    __radd__ = __add__

    def __neg__(self) -> IV:
        return IV(-self.hi,-self.lo)
    def __sub__(self, other) -> IV:
        return self + (-IV.of(other))
    def __rsub__(self, other) -> IV:
        return IV.of(other) + (-self)

    def __mul__(self, other) -> IV:
        b = IV.of(other)
        vals=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return IV(min(vals)//SCALE,ceil_div(max(vals),SCALE))
    __rmul__ = __mul__

    def reciprocal(self) -> IV:
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError('interval contains zero')
        if self.hi < 0:
            return -((-self).reciprocal())
        return IV((SCALE*SCALE)//self.hi,ceil_div(SCALE*SCALE,self.lo))

    def __truediv__(self, other) -> IV:
        return self * IV.of(other).reciprocal()
    def __rtruediv__(self, other) -> IV:
        return IV.of(other) * self.reciprocal()

    def __pow__(self, n: int) -> IV:
        if n < 0:
            return self.reciprocal()**(-n)
        ans=IV.of(1); x=self
        while n:
            if n & 1: ans=ans*x
            n //= 2
            if n: x=x*x
        return ans

    def sqrt(self) -> IV:
        if self.lo < 0:
            raise ValueError('negative square-root lower bound')
        l=isqrt(self.lo*SCALE)
        u=isqrt(self.hi*SCALE)
        if u*u < self.hi*SCALE: u+=1
        if not (l*l <= self.lo*SCALE and u*u >= self.hi*SCALE):
            raise ArithmeticError("invalid integer square-root enclosure")
        return IV(l,u)

    def exact_bounds(self) -> tuple[Fraction,Fraction]:
        return Fraction(self.lo,SCALE),Fraction(self.hi,SCALE)

    def json(self) -> dict:
        return {'lo_numerator':str(self.lo),'hi_numerator':str(self.hi),
                'denominator':str(SCALE)}

    def lt(self, q: int | Fraction | str) -> bool:
        return Fraction(self.hi,SCALE) < Fraction(q)
    def gt(self, q: int | Fraction | str) -> bool:
        return Fraction(self.lo,SCALE) > Fraction(q)


def _log_reduced(x: IV) -> IV:
    # The caller ensures the entire interval is contained in [1,2].
    if not (x.lo >= SCALE and x.hi <= 2*SCALE):
        raise ValueError("log reduction outside [1,2]")
    z=(x-1)/(x+1)
    z2=z*z
    power=z; total=IV.of(0)
    for k in range(64):
        total+=power/Fraction(2*k+1)
        power*=z2
    remainder=2*power/(129*(1-z2))
    if remainder.lo < 0: raise ArithmeticError("negative remainder bound")
    return 2*total + IV(0,remainder.hi)

@lru_cache(maxsize=None)
def log2() -> IV:
    return _log_reduced(IV.of(2))

@lru_cache(maxsize=65536)
def log_point(q: Fraction) -> IV:
    if q <= 0: raise ValueError('log domain')
    e=q.numerator.bit_length()-q.denominator.bit_length()
    scale=Fraction(2)**e
    r=q/scale
    if r<1: e-=1; r*=2
    if r>=2: e+=1; r/=2
    if not (1<=r<2): raise ArithmeticError("invalid logarithm reduction")
    return e*log2()+_log_reduced(IV.of(r))

def log(x: IV | Fraction | int) -> IV:
    a=IV.of(x)
    lo,hi=a.exact_bounds()
    return IV(log_point(lo).lo,log_point(hi).hi)


def _atan_reduced(x: IV) -> IV:
    if not (x.lo >= 0 and x.hi <= SCALE//2):
        raise ValueError("arctangent reduction outside [0,1/2]")
    x2=x*x; power=x; total=IV.of(0)
    for k in range(80):
        term=power/Fraction(2*k+1)
        total=total+term if k%2==0 else total-term
        power*=x2
    err=power/161
    # Symmetric bound avoids relying on the sign of the next term.
    return total+IV(-err.hi,err.hi)

@lru_cache(maxsize=None)
def pi() -> IV:
    return 16*_atan_reduced(IV.of(Fraction(1,5)))-4*_atan_reduced(IV.of(Fraction(1,239)))

@lru_cache(maxsize=65536)
def atan_point(q: Fraction) -> IV:
    if q < 0: return -atan_point(-q)
    if q > 1: return pi()/2-atan_point(1/q)
    if q <= Fraction(1,2): return _atan_reduced(IV.of(q))
    x=IV.of(q)
    return 2*_atan_reduced(x/(1+(1+x*x).sqrt()))

def atan(x: IV | Fraction | int) -> IV:
    a=IV.of(x); lo,hi=a.exact_bounds()
    return IV(atan_point(lo).lo,atan_point(hi).hi)
