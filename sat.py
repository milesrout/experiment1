import formula
import itertools
import utils


def assignments(f):
    ps = props(f) - {formula.bot.a}
    cs = itertools.product({True, False}, repeat=len(ps))
    return (dict(zip(ps, c)) for c in cs)


def tautological(f):
    return all(sat(f, a) for a in assignments(f))


def satisfiable(f):
    return any(sat(f, a) for a in assignments(f))


@utils.overload()
def sat(f, a):
    ...


@sat.on(formula.impl)
def sat_impl(f, a):
    if f.b is formula.bot:
        return not sat(f.a, a)
    return not sat(f.a, a) or sat(f.b, a)


@sat.on(formula.conj)
def sat_conj(f, a):
    return sat(f.a, a) and sat(f.b, a)


@sat.on(formula.disj)
def sat_disj(f, a):
    return sat(f.a, a) or sat(f.b, a)


@sat.on(formula.atomic)
def sat_atomic(f, a):
    if f is formula.bot:
        return False
    return a[f.a]


@utils.overload()
def props(f):
    ...


@props.on(formula.impl)
def props_impl(f):
    return props(f.a) | props(f.b)


@props.on(formula.conj)
def props_conj(f):
    return props(f.a) | props(f.b)


@props.on(formula.disj)
def props_disj(f):
    return props(f.a) | props(f.b)


@props.on(formula.atomic)
def props_atomic(f):
    return {f.a}


if __name__ == '__main__':
    a = formula.atomic('a')
    b = formula.atomic('b')
    print(tautological(a | ~b))
    print(tautological((a & b) > a))
