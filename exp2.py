#!/usr/bin/env python3

from abc import ABC, abstractmethod
import argparse
import collections
import itertools
import pickle
import random
import statistics
import sys
import unicodedata

from formula import atomic, bot, impl, conj, disj, forall, exists, proposition, variable, equality, zero, succ
from randfol import FormulaGenerator, generate_formulas
import stats
from utils import compose, TimeLimit, timelimit_soft, check_timelimit

# If this parameter is False, formulae are removed from premises when they are
# used. Oddly this doesn't seem to reduce the number of formulae that are
# provable if the only connective used is implication.
KEEP_USED_PREMISES = True

# Whether to print out the steps while backtracking/proving
DEBUG_PROOF_STEPS = False

# Whether to abbreviate the statistical output
ABBREV = False

PHI = unicodedata.lookup('GREEK SMALL LETTER PHI')
THETA = unicodedata.lookup('GREEK SMALL LETTER THETA')
PSI = unicodedata.lookup('GREEK SMALL LETTER PSI')
IMPL = unicodedata.lookup('RIGHTWARDS ARROW')
CONJ = '∧'
DISJ = '∨'
TSTILE = unicodedata.lookup('RIGHT TACK')
FORALL = '∀'
EXISTS = '∃'
EQUALITY = '='

P_ONEPOINT = 0.3
P_MUTATION = 0.05

# Returns a copy of the original list in a random order
def shuffled(pop):
    return random.sample(pop, len(pop))

def take(n, iterable):
    return list(itertools.islice(iterable, n))

# These are the rules of the minimal propositional sequent calculus. This
# presentation of the rules is a little different from normal because formulae
# are never removed from 'premises' and premises is treated as a set, so there
# is no need for the structural rules of Contraction, Weakening,
# or Permutation.

def iterate(f, x):
    yield x
    yield from map(f, iterate(f, x))

def terms():
    x, y, z = variable('x'), variable('y'), zero
    while True:
        yield x
        yield y
        yield z
        x, y, z = succ(x), succ(y), succ(z)

def fresh(premises, goal):
    vs = (variable(f'x{i}') for i in itertools.count(0))
    FV = set.union(goal.free_vars(), *[p.free_vars() for p in premises])
    return next(v for v in vs if v not in FV)

def equality_right(premises, goal):
    return ByEqualityRight, [(premises, goal)]

def equality_left_1(premise, premises, goal):
    return [(ByEqualityLeft1, [(premises | {p.subst(premise.t1, premise.t2)}, goal)])
            for p in premises]

def equality_left_2(premise, premises, goal):
    return [(ByEqualityLeft2, [(premises | {p.subst(premise.t2, premise.t1)}, goal)])
            for p in premises]

def exists_right(premises, goal):
    ts = take(3, terms())
    return [(ByExistsRight, [(premises, goal.instantiate(t))]) for t in ts]

def forall_right(premises, goal):
    return ByForallRight, [(premises, goal.instantiate(fresh(premises, goal)))]

def exists_left(premise, premises, goal):
    if KEEP_USED_PREMISES:
        return ByExistsLeft, [((premises | {premise.instantiate(fresh(premises, goal))}), goal)]
    else:
        raise NotImplementedError()

def forall_left(premise, premises, goal):
    ts = take(3, terms())
    if KEEP_USED_PREMISES:
        return [(ByForallLeft, [(premises | {premise.instantiate(t)}, goal)]) for t in ts]
    else:
        raise NotImplementedError()

def impl_left(premise, premises, goal):
    if KEEP_USED_PREMISES:
        return ByImplLeft, [(premises, premise.a),
                            (premises | {premise.b}, goal)]
    else:
        return ByImplLeft, [(premises - {premise}, premise.a),
                            (premises - {premise} | {premise.b}, goal)]


def conj_left_1(premise, premises, goal):
    if KEEP_USED_PREMISES:
        return ByConjLeft1, [(premises | {premise.a}, goal)]
    else:
        return ByConjLeft1, [(premises - {premise} | {premise.a}, goal)]


def conj_left_2(premise, premises, goal):
    if KEEP_USED_PREMISES:
        return ByConjLeft2, [(premises | {premise.b}, goal)]
    else:
        return ByConjLeft2, [(premises - {premise} | {premise.b}, goal)]


def disj_left(premise, premises, goal):
    if KEEP_USED_PREMISES:
        return ByDisjLeft, [(premises | {premise.a}, goal),
                            (premises | {premise.b}, goal)]
    else:
        return ByDisjLeft, [(premises - {premise} | {premise.a}, goal),
                            (premises - {premise} | {premise.b}, goal)]


def impl_right(premises, goal):
    return ByImplRight, [(premises | {goal.a}, goal.b)]


def conj_right(premises, goal):
    return ByConjRight, [(premises, goal.a),
                         (premises, goal.b)]


def disj_right_1(premises, goal):
    return ByDisjRight1, [(premises, goal.a)]


def disj_right_2(premises, goal):
    return ByDisjRight2, [(premises, goal.b)]


class Heuristic(ABC):
    @abstractmethod
    def weight(self, option):
        ...

    def choose_options(self, sequent):
        (premises, goal) = sequent

        # work out all the options
        options = options_right(premises, goal)
        for premise in sorted(premises, key=str):
            for option in options_left(premise, premises, goal):
                options.append(option)

        # choose the order of them - THIS is the key part, the heuristic!
        options.sort(key=self.weight)

        return options


class SimplisticHeuristic(Heuristic):
    def __init__(self, *, reverse=False):
        self.reverse = reverse

    def weight(self, opt):
        "An extremely simple heuristic: always favour options in this order"

        if self.reverse:
            return 1 / (1 + RULES.index(opt[0]))
        return RULES.index(opt[0])


def options_right(premises, goal):
    """All the possible next steps from the goal"""
    if isinstance(goal, impl):
        return [impl_right(premises, goal)]
    if isinstance(goal, conj):
        return [conj_right(premises, goal)]
    if isinstance(goal, disj):
        return [disj_right_1(premises, goal),
                disj_right_2(premises, goal)]
    if isinstance(goal, exists):
        return exists_right(premises, goal)
    if isinstance(goal, forall):
        return [forall_right(premises, goal)]
    if isinstance(goal, equality):
        print(goal.t1, goal.t2, goal.t1 == goal.t2)
        if goal.t1 == goal.t2:
            return [equality_right(premises, goal)]
        return [(ByEqualityFlip, [(premises, equality(goal.t2, goal.t1))])]
    #print('--------------------------------')
    #for premise in premises:
    #    print(f'    pre: {str(type(premise)) + ":":<35} {str(premise):<15}')
    #print(f'goal:    {str(type(goal)) + ":":<35} {str(goal):<15}')
    return []


def options_left(premise, premises, goal):
    """All the possible next steps from the given premise"""
    if isinstance(premise, impl):
        return [impl_left(premise, premises, goal)]
    if isinstance(premise, conj):
        return [conj_left_1(premise, premises, goal),
                conj_left_2(premise, premises, goal)]
    if isinstance(premise, disj):
        return [disj_left(premise, premises, goal)]
    if isinstance(premise, exists):
        return [exists_left(premise, premises, goal)]
    if isinstance(premise, forall):
        return forall_left(premise, premises, goal)
    if isinstance(premise, equality):
        if isinstance(premise.t1, variable) and isinstance(premise.t2, variable):
            return (equality_left_1(premise, premises, goal) +
                    equality_left_2(premise, premises, goal))
        elif isinstance(premise.t1, variable):
            return equality_left_1(premise, premises, goal)
        elif isinstance(premise.t2, variable):
            return equality_left_2(premise, premises, goal)
        else:
            return []
    #print('--------------------------------')
    #for premise in premises:
    #    print(f'    pre: {str(type(premise)) + ":":<35} {str(premise):<15}')
    #print(f'goal:    {str(type(goal)) + ":":<35} {str(goal):<15}')
    #print(f'premise: {str(type(premise)) + ":":<35} {str(premise):<15}')
    return []


# A 'loop' backtrack is where we backtrack because we tried to prove something
# that we were already trying to prove i.e. while trying to prove P we had to
# prove Q and while trying to prove Q we had to prove P.
# If something cannot be proved because of 'loop' backtracks only, it isn't
# marked as unprovable.
class LoopBacktrack(BaseException):
    pass


# A 'fail' backtrack is where we backtrack because we ran out of options for
# proving something, or because we tried to prove something that we've
# previously marked as unprovable. If something cannot be proved because of a
# 'fail' backtrack, it is marked as unprovable.
class FailBacktrack(BaseException):
    pass


# Non-frozen sets (mutable sets) cannot be used as keys in dictionaries or
# elements of sets.
def freeze(stmt):
    premises, goal = stmt
    return frozenset(premises), goal


@compose('\n'.join)
def centre(text, width):
    """Centre the lines in a multi-line block of text within a given width"""
    for line in text.splitlines():
        yield f'{line:^{width}}'


@compose('\n'.join)
def concat(text1, text2):
    """Join two multi-line blocks of text horizontally with a space"""
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
    def fmtsequent(cls, seq):
        premises, goal = seq
        ps = ', '.join(str(p) for p in premises)
        return f'{ps} {TSTILE} {goal}'


class NullaryProof(Proof):
    """A proof with no further steps required"""
    def __init__(self, result):
        self.result = result


class UnaryProof(Proof):
    """A proof with one further step required"""
    def __init__(self, result, a):
        self.result = result
        self.a = a

    def fmtunary(self, op):
        root = self.fmtsequent(self.result)
        res = str(self.a)
        mwidth = max(width(res), len(root))
        divider = '-' * mwidth
        rootC = centre(root, mwidth)
        resC = centre(res, mwidth)
        return f'{rootC}   \n{divider} {op}\n{resC}'

    @property
    def size(self):
        return 1 + self.a.size


class BinaryProof(Proof):
    """A proof with two further steps required"""
    def __init__(self, result, a, b):
        self.result = result
        self.a = a
        self.b = b

    def fmtbinary(self, op):
        root = self.fmtsequent(self.result)
        line = concat(str(self.a), str(self.b))
        mwidth = max(width(line), width(root))
        divider = '-' * mwidth
        rootC = centre(root, mwidth)
        lineC = centre(line, mwidth)
        return f'{rootC}   \n{divider} {op}\n{lineC}'

    @property
    def size(self):
        return 1 + self.a.size + self.b.size


class ByAxiom(NullaryProof):
    def __str__(self):
        seq = self.fmtsequent(self.result)
        divider = '-' * len(seq)
        return f'{seq}   \n{divider} Ax'

    @property
    def size(self):
        return 1


class ByEqualityRight(NullaryProof):
    def __str__(self):
        seq = self.fmtsequent(self.result)
        divider = '-' * len(seq)
        return f'{seq}   \n{divider} Ax'

    @property
    def size(self):
        return 1


def unaryrule(symbol1, symbol2, num=None):
    if num is None:
        num = ''
    else:
        num = str(num)
    abbrev = globals()[symbol1] + symbol2[0] + num

    class Rule(UnaryProof):
        def __str__(self):
            return self.fmtunary(abbrev)
    Rule.__name__ = f'By{symbol1.title()}{symbol2.title()}{num}'
    Rule.__qualname__ = f'unaryrule.<locals>.{Rule.__name__}{num}'
    Rule.abbrev = abbrev
    return Rule


def binaryrule(symbol1, symbol2):
    abbrev = globals()[symbol1] + symbol2[0]

    class Rule(BinaryProof):
        def __str__(self):
            return self.fmtbinary(abbrev)
    Rule.__name__ = f'By{symbol1.title()}{symbol2.title()}'
    Rule.__qualname__ = f'binaryrule.<locals>.{Rule.__name__}'
    Rule.abbrev = abbrev
    return Rule


ByConjRight = binaryrule('CONJ', 'RIGHT')
ByConjLeft1 = unaryrule('CONJ', 'LEFT', 1)
ByConjLeft2 = unaryrule('CONJ', 'LEFT', 2)

ByImplLeft = binaryrule('IMPL', 'LEFT')
ByImplRight = unaryrule('IMPL', 'RIGHT')

ByDisjLeft = binaryrule('DISJ', 'LEFT')
ByDisjRight1 = unaryrule('DISJ', 'RIGHT', 1)
ByDisjRight2 = unaryrule('DISJ', 'RIGHT', 2)

ByForallLeft = unaryrule('FORALL', 'LEFT')
ByForallRight = unaryrule('FORALL', 'RIGHT')

ByExistsLeft = unaryrule('EXISTS', 'LEFT')
ByExistsRight = unaryrule('EXISTS', 'RIGHT')

ByEqualityLeft1 = unaryrule('EQUALITY', 'LEFT', 1)
ByEqualityLeft2 = unaryrule('EQUALITY', 'LEFT', 2)
ByEqualityFlip = unaryrule('EQUALITY', 'FLIP')

RULES = [
    ByImplLeft,
    ByConjRight,
    ByDisjLeft,
    ByConjLeft1,
    ByConjLeft2,
    ByDisjRight1,
    ByDisjRight2,
    ByImplRight,
    ByForallLeft,
    ByForallRight,
    ByExistsLeft,
    ByExistsRight,
    ByEqualityLeft1,
    ByEqualityLeft2,
    ByEqualityRight,
    ByEqualityFlip,
]


class Prover:
    def __init__(self, restrict_axiom, heuristic):
        self.restrict_axiom = restrict_axiom
        self.heuristic = heuristic
        self.trivial_equality = False
        self.inprogress = []
        self.proved = {}
        self.failed = []

    def isproved(self, sequent):
        return sequent in self.proved

    def isinprogress(self, sequent):
        return sequent in self.inprogress

    def hasfailed(self, sequent):
        return sequent in self.failed

    def getproof(self, sequent):
        return self.proved[sequent]

    def markinprogress(self, sequent):
        self.inprogress.append(sequent)

    def markproved(self, sequent, proof):
        self.proved[sequent] = proof

    def markfailed(self, sequent):
        self.failed.append(sequent)

    def backtrack(self):
        self.inprogress.pop()

    def do_prove(self, sequent):
        self.search_size += 1
        #check_timelimit()

        premises, goal = sequent

        # We can restrict the A |- A rule to only atomic formulas. Every proof
        # that can be done with that restriction can be done without it, but
        # they're longer as they include a few more (trivial) steps.
        if self.restrict_axiom:
            if goal in premises and isinstance(goal, atomic):
                return ByAxiom((premises, goal))
        else:
            if goal in premises:
                return ByAxiom((premises, goal))

        # We can allow equality to be treated as an axiom in the same way we
        # treat A |- A as an axiom, but for now we will require this to be
        # covered by an explicit deduction rule.
        if self.trivial_equality:
            if isinstance(goal, equality):
                if goal.t1 == goal.t2:
                    return ByAxiom((premises, goal))

        # Memoise proofs
        if self.isproved(sequent):
            return self.getproof(sequent)

        # Memoise failures to prove
        if self.hasfailed(sequent):
            if DEBUG_PROOF_STEPS:
                print(' ' * len(self.inprogress) + 'failed already:',
                      Proof.fmtsequent(sequent))
            raise FailBacktrack

        # Don't get into trivial infinite loops
        if self.isinprogress(sequent):
            if DEBUG_PROOF_STEPS:
                print(' ' * len(self.inprogress) + 'loop:',
                      Proof.fmtsequent(sequent))
            raise LoopBacktrack

        try:
            self.markinprogress(sequent)
            options = self.heuristic.choose_options(sequent)

            fail_backtrack = False
            for option in options:
                results = []

                try:
                    name, stmts = option
                    if DEBUG_PROOF_STEPS:
                        print(name.__name__, Proof.fmtsequent(sequent))
                        for stmt in stmts:
                            print(' ' * len(self.inprogress), end='')
                            print(Proof.fmtsequent(stmt))
                    for stmt in stmts:
                        results.append(self.do_prove(stmt))
                except LoopBacktrack:
                    pass
                except FailBacktrack:
                    fail_backtrack = True
                else:
                    proof = name(sequent, *results)

                    # Memoise proofs
                    self.markproved(sequent, proof)

                    # The current sequent is no longer in progress (proved it)
                    self.backtrack()

                    return proof

                if DEBUG_PROOF_STEPS:
                    print(' ' * len(self.inprogress) + '<==')

                # Stop backtracking, because we're at a point where we can
                # make a different decision
                continue

            # We ran out of options - backtrack
            if fail_backtrack:
                self.markfailed(sequent)
                raise FailBacktrack
            raise LoopBacktrack
        except (LoopBacktrack, FailBacktrack):
            # Wind back the state of the prover
            self.backtrack()
            raise
        raise RuntimeError('Should never get here')

    def prove(self, statement):
        self.search_size = 0
        try:
            proof = self.do_prove(freeze(statement))
        except (FailBacktrack, LoopBacktrack):
            proof = None
        # return len(self.proved) + len(self.failed), proof
        return self.search_size, proof


def evaluate(implications, restrict_axiom, time_limit, heuristic, verbose):
    successes = 0
    timeouts = 0
    total = 0
    sizes = []
    search_space_explored = []
    proofs = []
    for statement in implications:
        try:
            with timelimit_soft(time_limit):
                prover = Prover(restrict_axiom, heuristic)
                proof = prover.prove(statement)
                if proof is not None:
                    search_size, proof = proof
        except TimeLimit:
            print('TIMED OUT')
            timeouts += 1
            proof = None
        if proof is not None:
            if len(implications) <= 25:
                proof_str = str(proof)
                if width(proof_str) <= 120:
                    print(f'Proof of {Proof.fmtsequent(statement)}:')
                    print(proof_str)
                else:
                    print(f'Proof of {Proof.fmtsequent(statement)} is too '
                          f'wide: {width(proof_str)} characters')
                print()
            successes += 1
            sizes.append(proof.size)
            search_space_explored.append(search_size)
            if len(implications) < 40:
                if proof.size > 10000:
                    print(proof.size, Proof.fmtsequent(statement))
            proofs.append((statement, proof))
        else:
            if len(implications) < 40:
                print('not minimally provable:')
                print(Proof.fmtsequent(statement))
        total += 1

    return proofs, sizes, search_space_explored, total, successes, timeouts


def print_stats(proofs, sizes, search_sizes, total, successes, timeouts):
    print(f'Successes: {successes}/{total}: {int(100 * (successes / total))}%')
    print(f'Timeouts: {timeouts}/{total}: {int(100 * (timeouts / total))}%')

    mean = statistics.mean(sizes)
    median = statistics.median_low(sizes)
    most_common = collections.Counter(sizes).most_common(3)
    longest = max(sizes)
    shortest = min(sizes)
    # most_common = collections.Counter(sizes).most_common(1)[0][0]
    for p in proofs:
        print('=======')
        print(p[1])
    skewness = stats.skewness(sizes, mean)
    variance = statistics.variance(sizes, mean)
    excess_kurtosis = stats.excess_kurtosis(sizes, mean)

    if ABBREV:
        print(f'{mean:.2f}, {median}, {most_common},', end=' ')
        print(f'{skewness:.2f}, {variance:.2f}, {excess_kurtosis:.2f}')
    else:
        print(f'mean: {mean}')
        print(f'median: {median}')
        print(f'most_common: {most_common}')
        print(f'shortest: {shortest}')
        print(f'longest: {longest}')
        print(f'skewness: {skewness}')
        print(f'variance: {variance}')
        print(f'excess kurtosis: {excess_kurtosis}')
    return successes / len(implications)


pA = proposition('A')
pB = proposition('B')
pC = proposition('C')

print(pA, pB, pA > pB)

pa = proposition(PHI)
pb = proposition(THETA)
pc = proposition(PSI)

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
    # Some things that definitely aren't provable in minimal logic
    (set(), dne(pA)),
    (set(), lem(pA)),
    (set(), efq(pA)),
    (set(), wlem(pA)),
    (set(), dgp(pA, pB)),
    (set(), pp(pA, pB)),
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


class WeightedHeuristic(Heuristic):
    def __init__(self, weights):
        self.weights = weights

    @staticmethod
    def random():
        return WeightedHeuristic([random.random() for i in range(len(RULES))])

    def __repr__(self):
        rules = self.rules()
        return (','.join(rule.abbrev for rule in rules) + '|' +
                ','.join(f'{W:.2f}' for W in self.weights))

    def rules(self):
        return sorted(RULES, key=lambda x: self.weight((x, None)))

    def nearby(self, x, a=0, b=1, alpha=20):
        """Returns a value near x within the range [a,b]

        alpha - higher means nearer x
        """
        v = (x - a) / (b - a)
        if v == 1:
            return v
        return a + (b - a) * random.betavariate(alpha, alpha * ((1 / v) - 1))

    def weight(self, option):
        return self.weights[RULES.index(option[0])]

    def crossover(self, other):
        w = list(map(random.uniform, self.weights, other.weights))
        return WeightedHeuristic(w)

    def mutate(self):
        if random.random() < P_ONEPOINT:
            if random.random() < P_ONEPOINT:
                print('reset')
                return WeightedHeuristic.random()
            # Mutate a single weight
            w = self.weights[:]
            w[random.randint(0, len(w) - 1)] = random.random()
        else:
            # Change all the weights slightly
            w = [self.nearby(x) for x in self.weights]
        return WeightedHeuristic(w)


def similarity(h1, h2):
    """Return the similarity between two WeightedHeuristics"""
    return sum(x == y for x, y in zip(h1.rules(), h2.rules())) / len(RULES)


def all_similarity(h0, hs):
    """Return the average similarity between a heuristic and a list of heuristics"""
    return statistics.mean((similarity(h0, h) for h in hs))


def use_data(data):
    """Helper function for argument handling cleanly"""
    return lambda: data


def use_random_statements(args):
    """Helper function for argument handling cleanly"""
    if args.num_connectives == 1:
        conns = [impl]
    elif args.num_connectives == 3:
        conns = [impl, conj, disj]
    return lambda: random_statements(args.allow_dups, args.max_depth,
                                     conns, args.num_stmts)


def evolve_main(args):
    if args.input is not None:
        with args.input as f:
            generate_data = use_data(pickle.load(f))
    else:
        generate_data = use_random_statements(args)

    population = [WeightedHeuristic.random() for i in range(args.pop_size)]
    new_population = []

    # basically is 'for generation in range(1, inf):'
    for generation in itertools.count(1):
        print(f'Generation {generation}')
        formulae = generate_data()

        # This is probably the worst possible way of doing it
        for h in population:
            new_population.append(h)
            new_population.append(h.crossover(random.choice(population)))
        for i, h in enumerate(population):
            if random.random() < P_MUTATION:
                new_population[i] = new_population[i].mutate()

        # Swap
        population, new_population = new_population, []

        fitness = {}
        for h in population:
            # before_time = time.perf_counter()
            proofs, sizes, search_sizes, total, successes, timeouts = evaluate(
                formulae, args.restrict_axiom, args.time_limit, h, False)
            # fitness[h] = time.perf_counter() - before_time
            # fitness[h] = (1 - successes / total)
            fitness[h] = statistics.mean(search_sizes)

        # Calculate the similarity between each heuristic and each other heuristic
        population = [(h, all_similarity(h, population[:i] + population[i + 1:]))
                      for i, h in enumerate(population)]

        # Use fitness function to encourage diversity (bad results)
        # for (h, sim) in population:
        #     fitness[h] *= math.sqrt(sim)

        # Sort the population by fitness and then by similarity
        population.sort(key=lambda x: (fitness[x[0]], x[1]))

        # Print out the population: columns INDIVIDUAL, FITNESS, SIMILARITY
        for i, (k, sim) in enumerate(population):
            print(f'{k} {fitness[k]:.3f} {sim:.3f}')
            # Anything below the line gets cut off
            if i == args.pop_size - 1:
                print('-----')

        # Cut off the population (MINIMISING fitness function)
        population = [x for (x, s) in population][:args.pop_size]

        print()


def random_statements(allow_dups, max_depth, connectives, num_stmts=None):
    if num_stmts is None:
        num_stmts = 10000
    fg = FormulaGenerator(binary_connectives=[impl])
    goals = generate_formulas(md=max_depth, n=num_stmts, fg=fg)
    stmts = [(frozenset(), goal) for goal in goals]
    for stmt in stmts:
        print(Proof.fmtsequent(stmt))
    input()
    return list(stmts)


def generate_main(args):
    if args.num_connectives == 1:
        conns = [impl]
    elif args.num_connectives == 3:
        conns = [impl, conj, disj]
    else:
        raise NotImplementedError

    stmts = random_statements(args.allow_dups, args.max_depth,
                              conns, args.num_stmts)

    pickle.dump(stmts, args.output)


def stats_main(args):
    global DEBUG_PROOF_STEPS

    if args.debug:
        DEBUG_PROOF_STEPS = True

    if args.use_fixed:
        data = implications
    elif args.input is not None:
        with args.input as f:
            data = pickle.load(f)
    else:
        if args.num_connectives == 1:
            conns = [impl]
        elif args.num_connectives == 3:
            conns = [impl, conj, disj]
        else:
            raise NotImplementedError

        data = random_statements(args.allow_dups, args.max_depth,
                                 conns, args.num_stmts)

    for d in data:
        pass  # print(d[1])

    if args.reverse:
        heuristic = SimplisticHeuristic(reverse=True)
    else:
        heuristic = SimplisticHeuristic()

    # don't print out info about each statement if dealing with lots of them
    verbose = len(data) < 40

    stats = evaluate(data, args.restrict_axiom, args.time_limit,
                     heuristic, verbose)
    print_stats(*stats)


def add_input_arguments(parser):
    parser.add_argument(
        '--input', metavar='FILE', type=argparse.FileType('rb'), default=None,
        help='A file containing a list of formulae')
    add_generation_arguments(parser)


def add_generation_arguments(parser):
    group = parser.add_argument_group('generation arguments '
                                      '(mutually exclusive with --input)')
    group.add_argument(
        '--allow-dups', action='store_true', default=False,
        help='Whether to allow formulae like ((a -> a) -> b) and '
             '((a -> b) -> (a -> b))')
    group.add_argument(
        '--max-depth', type=int, default=3,
        help='The maximum depth of a generated formula')
    group.add_argument(
        '--num-connectives', type=int, default=1,
        help='The number of connectives to use (1 = impl, 3 = impl/conj/disj)')
    group.add_argument(
        '--num-stmts', type=int, default=1000,
        help='The number of statements to generate')


def add_prover_arguments(parser):
    group = parser.add_argument_group('prover arguments')
    group.add_argument(
        '--use-fixed', action='store_true', default=False,
        help='Use a fixed set of formulae instead of formulae from a file')
    group.add_argument(
        '--restrict-axiom', action='store_true', default=False,
        help='Whether to restrict the axiom rule to just atomic formulae')
    group.add_argument(
        '--debug', action='store_true', default=False,
        help='Debug the proof steps')
    group.add_argument(
        '--time-limit', type=float, default=1.0,
        help='Time limit per proof (in milliseconds)')


# The code inside this if statement runs if you run this file directly, but not
# if you import this file.
if __name__ == '__main__':
    # Remove the default recursion limit of 1000
    # I think Python would crash before it got to this new limit
    sys.setrecursionlimit(1000000)

    parser = argparse.ArgumentParser(description='Theorem prover')

    subparsers = parser.add_subparsers()
    parser_stats = subparsers.add_parser(
        'stats', aliases=['s', 'stat'],
        help='Determine some statistics about the formulae')
    parser_stats.set_defaults(main=stats_main)
    add_prover_arguments(parser_stats)
    add_input_arguments(parser_stats)
    heuristic_mutex = parser_stats.add_mutually_exclusive_group()
    heuristic_mutex.add_argument(
        '--heuristic-file', metavar='FILE', type=argparse.FileType('rb'),
        help='The file to load the heuristic from')
    heuristic_mutex.add_argument(
        '--reverse', action='store_true', default=False,
        help='Reverse the simplistic heuristic')

    parser_generate = subparsers.add_parser(
        'generate', aliases=['g', 'gen'],
        help='Generate and store a list of formulae')
    parser_generate.set_defaults(main=generate_main)
    parser_generate.add_argument(
        '--output', metavar='FILE', type=argparse.FileType('wb'),
        help='Where to put the generated formulae')
    add_generation_arguments(parser_generate)

    parser_evolve = subparsers.add_parser(
        'evolve', aliases=['e'],
        help='Evolve a simple weighted heuristic')
    parser_evolve.set_defaults(main=evolve_main)
    parser_evolve.add_argument(
        '--output', metavar='FILE', type=argparse.FileType('wb'),
        help='Where to put checkpoints')
    parser_evolve.add_argument(
        '--pop-size', type=int,
        help='Population size')
    add_input_arguments(parser_evolve)
    add_prover_arguments(parser_evolve)

    args = parser.parse_args()

    if hasattr(args, 'main') and args.main is not None:
        args.main(args)
    else:
        parser.print_usage()
