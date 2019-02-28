#!/usr/bin/env python3

import argparse
import collections
import itertools
import pickle
import random
import statistics
import sys
import unicodedata

from formula import atomic, bot, impl, conj, disj
import rand
import sat
import stats
from utils import TimeLimit, timelimit, memoise, compose

# If this parameter is False, formulae are removed from premises when they are
# used. Oddly this doesn't seem to reduce the number of formulae that are
# provable.
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


# Returns a copy of the original list in a random order
def shuffled(pop):
    return random.sample(pop, len(pop))


# These are the rules of the minimal propositional sequent calculus. This
# presentation of the rules is a little different from normal because formulae
# are never removed from 'premises' and premises is treated as a set, so there
# is no need for the structural rules of Contraction, Weakening,
# or Permutation.

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


def simplistic_weight(opt):
    "An extremely simple heuristic - always favour the options in this order"

    options = [
        ByImplLeft,
        ByConjRight,
        ByDisjLeft,
        ByConjLeft1,
        ByConjLeft2,
        ByDisjRight1,
        ByDisjRight2,
        ByImplRight
    ]
    return options.index(opt[0])


@memoise
def consistent_key_option(option):
    return (option[0].__name__ + '!!' +
            '!'.join(consistent_key_branch(b)
                     for b in sorted(option[1], key=consistent_key_branch)))


@memoise
def consistent_key_branch(branch):
    return (str(branch[1]) + '??' +
            '?'.join(str(x) for x in sorted(branch[0], key=str)))


def choose_options(stmt, weight):
    (premises, goal) = stmt

    # work out all the options
    options = options_right(premises, goal)

    for premise in sorted(premises, key=lambda x: consistent_key_branch(({x}, 'a'))):
        for option in options_left(premise, premises, goal):
            options.append(option)

    # ensure the options are in a consistent (but arbitrary) order
    options.sort(key=consistent_key_option)

    # choose the order of them - THIS is the key part, the heuristic!
    options.sort(key=weight)

    return options


def options_right(premises, goal):
    """All the possible next steps from the goal"""
    if isinstance(goal, impl):
        return [impl_right(premises, goal)]
    if isinstance(goal, conj):
        return [conj_right(premises, goal)]
    if isinstance(goal, disj):
        return [disj_right_1(premises, goal),
                disj_right_2(premises, goal)]
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
        ps = ', '.join(str(p) for p in sorted(premises, key=str))
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


def unaryrule(symbol1, symbol2):
    class Rule(UnaryProof):
        def __str__(self):
            return self.fmtunary(globals()[symbol1] + symbol2[0])
    Rule.__name__ = f'By{symbol1.title()}{symbol2.title()}'
    Rule.__qualname__ = f'unaryrule.<locals>.{Rule.__name__}'
    return Rule


def binaryrule(symbol1, symbol2):
    class Rule(BinaryProof):
        def __str__(self):
            return self.fmtbinary(globals()[symbol1] + symbol2[0])
    Rule.__name__ = f'By{symbol1.title()}{symbol2.title()}'
    Rule.__qualname__ = f'binaryrule.<locals>.{Rule.__name__}'
    return Rule


ByConjRight = binaryrule('CONJ', 'RIGHT')
ByConjLeft1 = unaryrule('CONJ', 'LEFT')
ByConjLeft2 = unaryrule('CONJ', 'LEFT')

ByImplLeft = binaryrule('IMPL', 'LEFT')
ByImplRight = unaryrule('IMPL', 'RIGHT')

ByDisjLeft = binaryrule('DISJ', 'LEFT')
ByDisjRight1 = unaryrule('DISJ', 'RIGHT')
ByDisjRight2 = unaryrule('DISJ', 'RIGHT')


class Prover:
    def __init__(self, restrict_axiom, heuristic):
        self.restrict_axiom = restrict_axiom
        self.heuristic = heuristic
        self.inprogress = collections.ChainMap({})
        self.proved = {}
        self.failed = set()

    def bookmark(self):
        self.inprogress = self.inprogress.new_child()

    def isproved(self, sequent):
        return sequent in self.proved

    def isinprogress(self, sequent):
        p0, g0 = sequent
        for p, g in self.inprogress:
            if g0 == g and p0 <= p:
                return True
        return False

    def hasfailed(self, sequent):
        return sequent in self.failed

    def getproof(self, sequent):
        return self.proved[sequent]

    def markinprogress(self, sequent):
        # using only the 'set' part of the ChainMap, the values don't matter
        self.inprogress[sequent] = None

    def markproved(self, sequent, proof):
        self.proved[sequent] = proof

    def markfailed(self, sequent):
        print('FAILED:', Proof.fmtsequent(sequent))
        self.failed.add(sequent)

    def backtrack(self):
        self.inprogress = self.inprogress.parents

    def print_failed(self):
        print('FAILURES:')
        for seq in self.failed:
            print(Proof.fmtsequent(seq))

    def do_prove(self, sequent):
        premises, goal = sequent

        # We can restrict the A |- A rule to only atomic formulas. Every proof
        # that can be done with that restriction can be done without it, but
        # they're longer as they include a few more (trivial) steps.
        if self.restrict_axiom == 1:
            if goal in premises and isinstance(goal, atomic):
                return ByAxiom((premises, goal))
        else:
            if goal in premises:
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

        self.bookmark()
        try:
            self.markinprogress(sequent)
            options = choose_options(sequent, self.heuristic)

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
                    if DEBUG_PROOF_STEPS:
                        print(' ' * len(self.inprogress) + '<==')

                    # Stop backtracking, because we're at a point where we can
                    # make a different decision
                    continue
                except FailBacktrack:
                    fail_backtrack = True
                    if DEBUG_PROOF_STEPS:
                        print(' ' * len(self.inprogress) + '<==')

                    # Stop backtracking, because we're at a point where we can
                    # make a different decision
                    continue

                proof = name(sequent, *results)

                # Memoise proofs
                self.markproved(sequent, proof)

                # The current sequent is no longer in progress (we proved it)
                self.backtrack()

                return proof

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
        try:
            return self.do_prove(freeze(statement))
        except (FailBacktrack, LoopBacktrack):
            return None


def evaluate(restrict_axiom, heuristic, implications):
    successes = 0
    timeouts = 0
    total = 0
    sizes = []
    for statement in implications:
        try:
            # with timelimit(500):
                prover = Prover(restrict_axiom, heuristic)
                proof = prover.prove(statement)
        except TimeLimit:
            # print('TIMED OUT')
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
            if len(implications) < 40:
                if proof.size > 10000:
                    print(proof.size, Proof.fmtsequent(statement))
        else:
            if len(implications) < 40:
                print('not minimally provable:')
                print(Proof.fmtsequent(statement))
        total += 1

    print(f'Successes: {successes}/{total}: {int(100 * (successes / total))}%')
    print(f'Timeouts: {timeouts}/{total}: {int(100 * (timeouts / total))}%')

    mean = statistics.mean(sizes)
    median = statistics.median_low(sizes)
    most_common = collections.Counter(sizes).most_common(3)
    longest = max(sizes)
    shortest = min(sizes)
    # most_common = collections.Counter(sizes).most_common(1)[0][0]
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
    return total / len(implications)


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


def random_statements(allow_dups, max_depth, connectives, num_stmts=None):
    base_formulae = [pA, pB, pC, ~pA, ~pB, ~pC]
    if num_stmts is None:
        num_stmts = 10000
    stmts = []
    while len(stmts) < num_stmts:
        if allow_dups:
            formula = rand.rand_lt_depth(max_depth, base_formulae, connectives)
        else:
            formula = rand.rand_lt_depth_nodups(max_depth, base_formulae,
                                                connectives)
        if sat.tautological(formula):
            stmts.append((frozenset(), formula))
    print(f'generated {num_stmts} statements')
    return list(stmts)


def generate_main(args):
    if args.connectives == 1:
        conns = [impl]
    elif args.connectives == 3:
        conns = [impl, conj, disj]
    else:
        raise NotImplementedError
    stmts = random_statements(args.allow_dups, args.max_depth,
                              conns, args.statements)
    pickle.dump(stmts, args.output)


def stats_main(args):
    global DEBUG_PROOF_STEPS
    if args.debug:
        DEBUG_PROOF_STEPS = True
    if args.use_fixed:
        data = implications
    else:
        with args.input as f:
            data = pickle.load(f)
    if args.reverse:
        heuristic = simplistic_weight
    else:
        heuristic = lambda x: 1 / (1 + simplistic_weight(x))
    evaluate(args.restrict_axiom, heuristic, data)


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
    parser_stats.add_argument(
        '--input', metavar='FILE', type=argparse.FileType('rb'),
        help='A file containing a list of formulae')
    parser_stats.add_argument(
        '--use-fixed', action='store_true', default=False,
        help='Use a fixed set of formulae instead of formulae from a file')
    parser_stats.add_argument(
        '--restrict-axiom', action='store_true', default=False,
        help='Whether to restrict the axiom rule to just atomic formulae')
    parser_stats.add_argument(
        '--debug', action='store_true', default=False,
        help='Debug the proof steps')
    parser_stats.add_argument(
        '--reverse', action='store_true', default=False,
        help='Reverse the heuristic')

    parser_stats.set_defaults(main=stats_main)

    parser_generate = subparsers.add_parser(
        'generate', aliases=['g', 'gen'],
        help='Generate and store a list of formulae')
    parser_generate.add_argument(
        '--output', metavar='FILE', type=argparse.FileType('wb'),
        help='Where to put the generated formulae')
    parser_generate.add_argument(
        '--allow-dups', action='store_true', default=False,
        help='Whether to allow formulae like ((a -> a) -> b) and '
             '((a -> b) -> (a -> b))')
    parser_generate.add_argument(
        '--max-depth', type=int, required=True,
        help='The maximum depth of a generated formula')
    parser_generate.add_argument(
        '--connectives', type=int, default=1,
        help='The number of connectives to use (1 = impl, 3 = impl/conj/disj)')
    parser_generate.add_argument(
        '--statements', type=int,
        help='The number of statements to generate')
    parser_generate.set_defaults(main=generate_main)

    args = parser.parse_args()
    if hasattr(args, 'main') and args.main is not None:
        args.main(args)
    else:
        parser.print_usage()
