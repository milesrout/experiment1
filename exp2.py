import collections
import functools
import itertools
import random
import unicodedata

import sat
import rand
from formula import atomic, bot, impl, conj, disj


MAXDEPTH = 4
POPSIZE = 20
PROB_MUTATION = 0.2
PROB_CROSSOVER = 0.5
ADD_OR_REMOVE_FACTOR = 0.99
depths = collections.Counter()

PHI = unicodedata.lookup('GREEK SMALL LETTER PHI')
THETA = unicodedata.lookup('GREEK SMALL LETTER THETA')
PSI = unicodedata.lookup('GREEK SMALL LETTER PSI')
IMPL = unicodedata.lookup('RIGHTWARDS ARROW')
CONJ = '^'
DISJ = 'v'
TSTILE = unicodedata.lookup('RIGHT TACK')


def shuffled(pop):
    return random.sample(pop, len(pop))


def compose(f):
    def outer(g):
        @functools.wraps(g)
        def inner(*args, **kwds):
            return f(g(*args, **kwds))
        return inner
    return outer


def impl_left(formula):
    def _impl_left(premises, goal):
        return ByImplLeft, [(premises, formula.a),
                            (premises | {formula.b}, goal)]
    return _impl_left


def impl_right():
    def _impl_right(premises, goal):
        return ByImplRight, [(premises | {goal.a}, goal.b)]
    return _impl_right


def conj_left_1(formula):
    def _conj_left_1(premises, goal):
        return ByConjLeft1, [(premises | {formula.a}, goal)]
    return _conj_left_1


def conj_left_2(formula):
    def _conj_left_2(premises, goal):
        return ByConjLeft2, [(premises | {formula.b}, goal)]
    return _conj_left_2


def conj_right():
    def _conj_right(premises, goal):
        return ByConjRight, [(premises, goal.a),
                             (premises, goal.b)]
    return _conj_right


def disj_left(formula):
    def _disj_left(premises, goal):
        return ByDisjLeft, [(premises | {formula.a}, goal),
                            (premises | {formula.b}, goal)]
    return _disj_left


def disj_right_1():
    def _disj_right_1(premises, goal):
        return ByDisjRight1, [(premises, goal.a)]
    return _disj_right_1


def disj_right_2():
    def _disj_right_2(premises, goal):
        return ByDisjRight2, [(premises, goal.b)]
    return _disj_right_2


class WeightedHeuristic:
    NUMWEIGHTS = 1

    def __init__(self, weights):
        self.weights = weights

    def __repr__(self):
        w = ','.join(f'{W:.2f}' for W in self.weights)
        return f'({w})'

    @classmethod
    def random(cls):
        weights = [random.random() for i in range(cls.NUMWEIGHTS)]
        return WeightedHeuristic(weights)

    @staticmethod
    def crossover(left, right):
        wl = left.weights
        wr = right.weights
        w_ = [random.uniform(l, r) for (l, r) in zip(wl, wr)]
        return [WeightedHeuristic(w_)]

    def mutate(self):
        return self

    def apply(self, stmt):
        (premises, goal) = stmt
        opts = [option for options in map(self.options_left, premises)
                for option in options]
        return opts + self.options_right(goal)

    def options_right(self, formula):
        if isinstance(formula, impl):
            return [impl_right()]
        if isinstance(formula, conj):
            return [conj_right()]
        if isinstance(formula, disj):
            return [disj_right_1(), disj_right_2()]
        return []

    def options_left(self, formula):
        if isinstance(formula, impl):
            return [impl_left(formula)]
        if isinstance(formula, conj):
            return [conj_left_1(formula), conj_left_2(formula)]
        if isinstance(formula, disj):
            return [disj_left(formula)]
        return []


backtrack_stack = [{}]


def seen():
    return backtrack_stack[-1]


class Backtrack(BaseException):
    pass


def freeze(stmt):
    premises, goal = stmt
    return frozenset(premises), goal


def prove(statement, heuristic):
    try:
        return do_prove(statement, heuristic)
    except Backtrack:
        return None


@compose('\n'.join)
def centre(text, width):
    for line in text.splitlines():
        yield f'{line:^{width}}'


@compose('\n'.join)
def concat(text1, text2):
    lines1 = text1.splitlines()
    lines2 = text2.splitlines()
    max1 = max(map(len, lines1))
    max2 = max(map(len, lines2))
    for (line1, line2) in itertools.zip_longest(lines1, lines2, fillvalue=""):
        yield '{0:^{2}} {1:^{3}}'.format(line1, line2, max1, max2)


def width(text):
    return max(map(len, text.splitlines()))


class Proof:
    def __repr__(self):
        return str(self)

    @classmethod
    def fmtstmt(cls, stmt):
        premises, goal = stmt
        p = ', '.join(map(str, premises))
        # if goal in premises:
        #     return f'{p} {TSTILE} {goal} *'
        return f'{p} {TSTILE} {goal}'

    @classmethod
    def fmtbinary(cls, op, stmt, left, right):
        root = cls.fmtstmt(stmt)
        line = concat(str(left), str(right))
        mwidth = max(width(line), width(root))
        divider = '-' * mwidth
        rootC = centre(root, mwidth)
        lineC = centre(line, mwidth)
        return f'{rootC}   \n{divider} {op}\n{lineC}'

    @classmethod
    def fmtunary(cls, op, stmt, result):
        root = cls.fmtstmt(stmt)
        res = str(result)
        mwidth = max(width(res), len(root))
        divider = '-' * mwidth
        rootC = centre(root, mwidth)
        resC = centre(res, mwidth)
        return f'{rootC}   \n{divider} {op}\n{resC}'


class ByAxiom(Proof):
    def __init__(self, premises, goal):
        self.premises = premises
        self.goal = goal

    def __str__(self):
        p2g1 = self.fmtstmt((self.premises, self.goal))
        p2g2 = self.fmtstmt(({self.goal}, self.goal))
        mwidth = max(len(p2g1), len(p2g2))
        divider = '-' * mwidth
        divider2 = '-' * len(p2g2)
        return (f'{p2g1:^{mwidth}}   \n{divider}  W\n' +
                f'{p2g2 + "   ":^{mwidth}}\n{divider2 + " Ax":^{mwidth}}')


class ByConjLeft1(Proof):
    def __init__(self, ganb2c, ga2c):
        self.ganb2c = ganb2c
        self.ga2c = ga2c

    def __str__(self):
        return self.fmtunary(CONJ + 'L', self.ganb2c, self.ga2c)


class ByConjLeft2(Proof):
    def __init__(self, ganb2c, gb2c):
        self.ganb2c = ganb2c
        self.gb2c = gb2c

    def __str__(self):
        return self.fmtunary(CONJ + 'L', self.ganb2c, self.gb2c)


class ByConjRight(Proof):
    def __init__(self, g2anb, g2a, g2b):
        self.g2anb = g2anb
        self.g2a = g2a
        self.g2b = g2b

    def __str__(self):
        return self.fmtbinary(CONJ + 'R', self.g2anb, self.g2a, self.g2b)


class ByDisjRight1(Proof):
    def __init__(self, g2aob, g2a):
        self.g2aob = g2aob
        self.g2a = g2a

    def __str__(self):
        return self.fmtunary(DISJ + 'R', self.g2aob, self.g2a)


class ByDisjRight2(Proof):
    def __init__(self, g2aob, g2b):
        self.g2aob = g2aob
        self.g2b = g2b

    def __str__(self):
        return self.fmtunary(DISJ + 'R', self.g2aob, self.g2b)


class ByDisjLeft(Proof):
    def __init__(self, gaob2c, ga2c, gb2c):
        self.gaob2c = gaob2c
        self.ga2c = ga2c
        self.gb2c = gb2c

    def __str__(self):
        return self.fmtbinary(DISJ + 'L', self.gaob2c, self.ga2c, self.gb2c)


class ByImplLeft(Proof):
    def __init__(self, gaib2c, g2a, gb2c):
        self.gaib2c = gaib2c
        self.g2a = g2a
        self.gb2c = gb2c

    def __str__(self):
        return self.fmtbinary(IMPL + 'L', self.gaib2c, self.g2a, self.gb2c)


class ByImplRight(Proof):
    def __init__(self, g2aib, ga2b):
        self.g2aib = g2aib
        self.ga2b = ga2b

    def __str__(self):
        return self.fmtunary(IMPL + 'R', self.g2aib, self.ga2b)


def do_prove(statement, heuristic):
    premises, goal = statement
    # We can restrict the A |- A rule to only atomic formulas. Every proof that
    # can be done with that restriction can be done without it, but they're
    # longer and in trivial ways, so we don't do so.
    # if goal in premises and isinstance(goal, atomic):
    if goal in premises:
        return ByAxiom(premises, goal)
    if freeze(statement) in seen():
        # print('seen', statement)
        if seen()[freeze(statement)] is None:
            raise Backtrack
        return seen()[freeze(statement)]
    options = heuristic.apply(statement)
    for option in options:
        results = []
        try:
            seen()[freeze(statement)] = None
            name, stmts = option(*statement)
            for stmt in stmts:
                results.append(do_prove(stmt, heuristic))
        except Backtrack:
            del seen()[freeze(statement)]
            continue
        seen()[freeze(statement)] = name(statement, *results)
        return seen()[freeze(statement)]
    raise Backtrack


def _prove(statement, heuristic):
    if freeze(statement) in seen():
        raise Backtrack
    seen()[freeze(statement)] = None
    for stmts in heuristic.apply(statement):
        print(' ' * len(backtrack_stack), end='')
        backtrack_stack.append(dict(seen()))
        res = stmts(*statement)
        for stmt in res:
            try:
                prove(stmt, heuristic)
            except Backtrack:
                print('BACKTRACK')
                backtrack_stack.pop()
                continue
    raise Backtrack


def evaluate(implications):
    def _evaluate(heur):
        successes = 0
        total = 0
        for statement in random_statements():
            proof = prove(statement, heur)
            print(proof)
            if proof is not None:
                successes += 1
            else:
                print('not minimally provable:')
                print(Proof.fmtstmt(statement))
            total += 1
            print(successes, total, successes / total)
        print('DONE')
        raise
        return total / len(implications)
    return _evaluate


pA = atomic('A')
pB = atomic('B')
pC = atomic('C')

pa = atomic(PHI)
pb = atomic(THETA)
pc = atomic(PSI)

p1 = pp = lambda pa, pb: ((pa > pb) > pa) > pa
p2 = tfa = lambda pa, pb: ~pa > ~~(pa > pb)
p3 = dgp = lambda pa, pb: (pa > pb) | (pb > pa)
p4 = wdgp = lambda pa, pb: dgp(~pa, ~pb)
p5 = dgpa = lambda pa, pb: ~(pa > pb) > ~~(pb > pa)
p6 = lambda pa: ~(pa > ~pa) > pa
p7 = lambda pa, pb: ~pa > (pa > pb)
p8 = lambda pa: (~pa > pa) > pa
dne = lambda pa: ~~pa > pa
efq = lambda pa: bot > pa
lem = lambda pa: pa | ~pa
wlem = lambda pa: ~pa | ~~pa


implications = [
    # 4.1, P6 and DNE are equivalent
    (set(), dne(pA) > p6(pA)),
    ({dne(pA)}, p6(pA)),
    ({p6(pA)}, dne(pA)),
    # 4.2, P7 and EFQ are equivalent
    ({efq(pB)}, p7(pA, pB)),
    ({p7(~pA, pB)}, efq(pB)),
    # 4.3, P8 and LEM are equivalent
    ({lem(pA)}, p8(pA)),
    ({p8(lem(pA))}, lem(pA)),
    # 4.4, WDGP and WLEM are equivalent
    ({wdgp(pA, ~pA)}, wlem(pA)),
    ({wlem(pB)}, wdgp(pA, pB)),
    # 4.5, DNE implies PP
    ({dne(pB), dne(pA)}, pp(pA, pB)),
    # 4.6, PP implies DGP
    ({pp(dgp(pA, pB), pA)}, dgp(pA, pB)),
    # 4.7, PP implies TF>
    ({pp(bot, pB)}, tfa(pA, pB)),
    # 4.8, DNE implies EFQ
    ({dne(pA)}, efq(pA)),
    # 4.9, PP implies LEM
    ({pp(lem(pA), bot)}, lem(pA)),
    # 4.10, DGP implies WLEM
    ({dgp(pA, ~pA)}, wlem(pA)),
    # 4.11, EFQ implies TF>
    ({efq(pB)}, tfa(pA, pB)),
    # 4.12, TF> implies DGP>
    ({tfa(pB, pA)}, dgpa(pA, pB)),
    # 4.13, LEM implies WLEM
    ({lem(pA)}, wlem(pA)),
    # 4.14, DGP implies DGP>
    ({dgp(pA, pB)}, dgpa(pA, pB)),
]


def random_statements():
    stmts = set()
    while len(stmts) < 1000:
        formula = rand.rand_lt_depth(MAXDEPTH, [pA, pB, pC, ~pA, ~pB, ~pC], (impl,))
        if sat.tautological(formula):
            print(len(stmts), formula)
            stmts.add((frozenset(), formula))
    return list(stmts)


def main():
    lastgen = None
    newgen = [WeightedHeuristic.random() for i in range(POPSIZE)]
    # print(f'{", ".join(map(str, premises))} {TSTILE} {goal}')
    for generation in itertools.count():
        lastgen, newgen = newgen, []

        for i, indiv in enumerate(lastgen):
            if random.random() < PROB_CROSSOVER:
                idx = random.randrange(len(lastgen))
                new = WeightedHeuristic.crossover(indiv, lastgen[idx])
                for x in new:
                    newgen.append(x)
            else:
                newgen.append(indiv)

        m = [x.mutate() for x in newgen if random.random() < PROB_MUTATION]
        newgen.extend(m)

        # print('Before pruning:')
        # print(newgen)

        # STRICT ELITISM
        # newgen.sort(key=Heuristic.fitness(goal, premises), reverse=True)
        # newgen = newgen[:POPSIZE]

        # WEIGHTED ELITISM
        print(newgen)
        weights = map(evaluate(implications), newgen)
        newgen = random.choices(newgen, weights, k=POPSIZE)

        # print('After pruning:')
        # if generation % 3000 == 0:
        if 1:
            print(f'Generation {generation}:')
            print(newgen)

        # print(depths)


if __name__ == '__main__':
    main()
