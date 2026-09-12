"""Divisibility root finishes, extracted unchanged from the proof source."""
from witness import Compiler, Witness, X, Y, inv, mul, power, conjugate

class RecordingCompiler(Compiler):
    def __init__(self, initial):
        super().__init__(initial)
        self.route = []
    def conj(self, slot, g):
        self.route.append(('conj', slot, g))
        super().conj(slot, g)
    def invert(self, slot):
        self.route.append(('inv', slot))
        super().invert(slot)
    def multiply(self, slot):
        self.route.append(('mul', slot, 1))
        super().multiply(slot)


def root(k):
    return mul(power(Y, -k), power(X, 2), power(Y, k), inv(X))


def companion(s):
    return mul(power(Y, -s-1), inv(X), power(Y, s), inv(X))


def doubling(k):
    return Witness(conjugate(power(Y,k), X), power(X,2),
                   ((mul(power(Y,k),inv(X)),True),))


def iterated(k, m):
    w = Witness.refl(X)
    for j in range(m):
        w = w.conj(power(Y,k)).trans(doubling(k).zpow(2**j))
    return w


def replace(c, slot, w):
    if c.state[slot] != w.source: raise ValueError('Witness source does not match relator.')
    w.verify(c.state[1-slot])
    for f in w.factors: c.factor(slot, f)
    if c.state[slot] != w.target: raise ValueError('Witness target was not reached.')


def power_finish(c, k, e):
    if c.state != (root(k),mul(inv(Y),power(X,e))): raise ValueError('Power entry mismatch.')
    w = Witness(Y, power(X,e), (((),True),))
    a = w.zpow(-k).product(Witness.refl(power(X,2))).product(w.zpow(k)).product(Witness.refl(inv(X)))
    replace(c, 0, a)
    c.zpow(1, -e)
    c.invert(1)
    if c.state != (X,Y): raise ValueError('Power finish failed.')


def root_constructor(s, p=2):
    if type(p) is not int or p < 1 or type(s) is not int or s < 0:
        raise ValueError('The divisibility constructor needs p >= 1 and s >= 0.')
    m, residue = divmod(s,p)
    if residue not in (0,p-1): raise ValueError('No supplied finish for this residue.')
    parity = residue != 0
    c = RecordingCompiler((root(p), companion(s)))
    d = 2**m
    c.conj(1,power(Y,p*m))
    prefix = mul(inv(Y), inv(X)) if parity == 0 else mul(power(Y,-p),inv(X),power(Y,p-1))
    replace(c,1,Witness.refl(prefix).product(iterated(p,m).inverse()))
    if parity == 0:
        power_finish(c,p,-d-1)
    else:
        v = mul(inv(X),power(Y,p-1),power(X,-d))
        w = Witness(power(Y,p),v,(((),True),))
        a = w.inverse().product(Witness.refl(power(X,2))).product(w).product(Witness.refl(inv(X)))
        replace(c,0,a)
        c.conj(0,power(X,-d))
        if c.state[0] != root(p-1): raise ValueError('Odd degree reduction failed.')
        c.conj(1,power(Y,p-1))
        replace(c,1,Witness.refl(mul(inv(Y),inv(X))).product(doubling(p-1).zpow(-d)))
        power_finish(c,p-1,-2*d-1)
    return c


def apply_route(c, route, map_conjugator=lambda w:w):
    for kind,i,*args in route:
        if kind == 'conj': c.conj(i,map_conjugator(args[0]))
        elif kind == 'inv': c.invert(i)
        elif kind == 'mul': c.zpow(i,args[0])
        else: raise ValueError(kind)


def map_concrete(w, fx, fy):
    return mul(*(fx if a==1 else inv(fx) if a==-1 else fy if a==2 else inv(fy) for a in w))
