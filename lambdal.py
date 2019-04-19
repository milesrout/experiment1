from collections import namedtuple, Counter
import itertools
import random
import utils
from formula import zero, succ

POPSIZE = 100
REDUCTION_STEPS = 200
TOURNAMENT_SIZE = 20
TOURNAMENT_PROB = 0.9

def pairs(list):
    return [(list[2 * i], list[2 * i + 1]) for i in range(len(list) // 2)]

def rand_term_guesser(depth):
    expr = rand_of_type(depth, Term(), {
        Variable('p'): List(Formula()),
        Variable('g'): Formula(),
    })
    return Lambda(Variable('p'),
                  Lambda(Variable('g'),
                         expr))

def calc_fitness(termguesser, premises, goal):
    tg = Application(Application(termguesser, premises), goal)
    v = reduce(REDUCTION_STEPS, tg)
    if not value(v):
        return 0
    return random.random()

def tournament(population, fitnesses):
    indices = random.sample(range(len(population)), k=TOURNAMENT_SIZE)
    indices.sort(key=lambda i: fitnesses[i])
    for i in indices[:-1]:
        if random.random() < TOURNAMENT_PROB:
            return population[i]
    return population[indices[-1]]

def mutate(t):
    pass

def crossover(t1, t2):
    s1 = subexprs(t1)
    s2 = subexprs(t2)
    print('s1', s1)
    print('s2', s2)

def evolve(premises, goal):
    for iteration in itertools.count(0):
        population = [rand_term_guesser(2) for i in range(POPSIZE)]
        fitnesses = [calc_fitness(tg, premises, goal) for tg in population]
        crossover_base = [tournament(population, fitnesses) for i in range(POPSIZE)]
        indices = pairs(utils.shuffled(range(POPSIZE)))
        population = [crossover(crossover_base[i], crossover_base[j]) for i, j in indices]
        print(population)
        for i in range(POPSIZE):
            population[i] = mutate(population[i])
        print(population)
        print(fitnesses)
        print(crossover_base)
        print(indices)

def main():
    sucC = Lambda(Variable('n'), NSuc(Variable('n')))
    twoC = Lambda(
        Variable('s'),
        Lambda(
            Variable('z'),
            Application(Variable('s'), Application(Variable('s'), Variable('z')))))
    plusC = Lambda(
        Variable('m'),
        Lambda(
            Variable('n'),
            Lambda(
                Variable('s'),
                Lambda(
                    Variable('z'),
                    Application(
                        Application(Variable('m'), Variable('s')),
                        Application(
                            Application(Variable('n'), Variable('s')),
                            Variable('z')))))))
    fourC = Application(Application(plusC, twoC), twoC)
    length = Fixpoint(Variable('l'), Lambda(Variable('x'),
                      LCase(Variable('x'),
                            NZero(),
                            Variable('y'), Variable('z'), NSuc(Application(Variable('l'), Variable('z'))))))
    list123 = LCons(NSuc(NZero()), LCons(NSuc(NSuc(NZero())), LCons(NSuc(NSuc(NSuc(NZero()))), LEmpty())))
    tests = {
        # Application(length, list123): NSuc(NSuc(NSuc(NZero()))),
        # Application(Application(fourC, sucC), NZero()): NSuc(NSuc(NSuc(NSuc(NZero())))),
    }

    goal_type = Arrow(List(Formula()), Arrow(Formula(), Arrow(Natural(), Term())))

    for expression, expected in tests.items():
        actual = reduce(100, expression)
        if isinstance(actual, expected.__class__) and actual == expected:
            print(string(expression), '--->', string(expected))
        else:
            print(string(expression), '--->', string(actual))
            print(string(expression), '-/->', string(expected))
            raise RuntimeError

    counter = Counter()

    for i in itertools.count():
        expr = rand_of_type(2, Term(), {
            Variable('p'): List(Formula()),
            Variable('g'): Formula()
        })
        premises = LEmpty()
        goal = FBottom()
        try:
            result = reduce(50000, Application(Application(Lambda(Variable('p'), Lambda(Variable('g'), expr)), premises), goal))
        except RanOutOfFuel as exc:
            continue
            # print('Problematic term:', string(expr))
            # print('Problematic term:', string(exc.term))
        print(string(expr), end='\n--->\n')
        print(result)
        counter[result] += 1
        print(counter)
        if i % 1000 == 0 and i != 0:
            print(i)

def fresh(fvs):
    return next(Variable(i) for i in itertools.count() if Variable(i) not in fvs)

def encode_list(l):
    result = LEmpty()
    for x in l:
        result = LCons(x, result)
    return result

def encode_nat(nat):
    result = NZero()
    for i in range(nat):
        result = NSuc(result)
    return result

def random_type():
    return random.choice([
        lambda: Natural(),
        lambda: Term(),
        lambda: Formula(),
        lambda: Boolean(),
        lambda: List(random_type()),
        lambda: Arrow(random_type(), random_type())
    ])()

def type_equal(a, b):
    if isinstance(a, Arrow) and isinstance(b, Arrow):
        return type_equal(a.t1, b.t1) and type_equal(a.t2, b.t2)
    if isinstance(a, List) and isinstance(b, List):
        return type_equal(a.t, b.t)
    return isinstance(a, type(b)) and a == b

def random_variable(md, typ, fvs):
    valid = [v for v, t in fvs.items() if type_equal(t, typ)]
    if len(valid) == 0:
        return None  # rand_of_type(md - 1, typ, fvs)
    return random.choice(valid)

def random_application(md, typ, fvs):
    t = random_type()
    f = rand_of_type(md - 1, Arrow(t, typ))
    x = rand_of_type(md - 1, t)
    return Application(f, x)

def random_fixpoint(md, typ, fvs):
    v = fresh(fvs)
    return Fixpoint(v, rand_of_type(md - 1, typ, {v: typ, **fvs}))

def random_ncase(md, typ, fvs):
    v = fresh(fvs)
    return NCase(rand_of_type(md - 1, Natural(), fvs),
                 rand_of_type(md - 1, typ, fvs),
                 v,
                 rand_of_type(md - 1, typ, {**fvs, v: Natural()}))

def random_ifthenelse(md, typ, fvs):
    return BIfThenElse(rand_of_type(md - 1, Boolean(), fvs),
                       rand_of_type(md - 1, typ, fvs),
                       rand_of_type(md - 1, typ, fvs))

def random_lcase(md, typ, fvs):
    t = random_type()
    v1 = fresh(fvs)
    v2 = fresh({v1: t, **fvs})
    return LCase(rand_of_type(md - 1, List(t), fvs),
                 rand_of_type(md - 1, typ, fvs),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: t, v2: List(t), **fvs}))

def random_tcase(md, typ, fvs):
    v1 = fresh(fvs)
    return TCase(rand_of_type(md - 1, Term(), fvs),
                 rand_of_type(md - 1, typ, fvs),
                 v1,
                 rand_of_type(md - 1, typ, {v1: Term(), **fvs}),
                 v1,
                 rand_of_type(md - 1, typ, {v1: Natural(), **fvs}))

def random_fcase(md, typ, fvs):
    v1 = fresh(fvs)
    v2 = fresh({v1: None, **fvs})
    return FCase(rand_of_type(md - 1, Formula(), fvs),
                 rand_of_type(md - 1, typ, fvs),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: Term(), v2: Term(), **fvs}),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: Formula(), v2: Formula(), **fvs}),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: Formula(), v2: Formula(), **fvs}),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: Formula(), v2: Formula(), **fvs}),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: Natural(), v2: Formula(), **fvs}),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: Natural(), v2: Formula(), **fvs}))

def random_specific_base(typ, fvs):
    if isinstance(typ, Natural):
        return NZero()
    if isinstance(typ, Term):
        return TZero()
    if isinstance(typ, Formula):
        return FBottom()
    if isinstance(typ, Boolean):
        return random.choice([BTrue(), BFalse()])
    if isinstance(typ, List):
        return LEmpty()
    if isinstance(typ, Arrow):
        v = fresh(fvs)
        x = Lambda(v, rand_of_type(0, typ.t2, {**fvs, v: typ.t1}))
        #print('RSB', fvs, v, typ.t1, typ.t2, string(x))
        return x
    # print(typ, fvs)
    raise NotImplementedError

def random_specific(md, typ, fvs):
    if isinstance(typ, Natural):
        return encode_nat(utils.randnat())
    if isinstance(typ, Term):
        return random.choice([
            lambda: TZero(),
            lambda: TSuc(rand_of_type(md - 1, Term(), fvs)),
            lambda: TVar(rand_of_type(md - 1, Natural(), fvs))])()
    if isinstance(typ, Formula):
        return random.choice([
            lambda: FBottom(),
            lambda: FEquality(rand_of_type(md - 1, Term(), fvs),
                              rand_of_type(md - 1, Term(), fvs)),
            lambda: FImplication(rand_of_type(md - 1, Formula(), fvs),
                                 rand_of_type(md - 1, Formula(), fvs)),
            lambda: FConjunction(rand_of_type(md - 1, Formula(), fvs),
                                 rand_of_type(md - 1, Formula(), fvs)),
            lambda: FDisjunction(rand_of_type(md - 1, Formula(), fvs),
                                 rand_of_type(md - 1, Formula(), fvs)),
            lambda: FForall(rand_of_type(md - 1, Natural(), fvs),
                            rand_of_type(md - 1, Formula(), fvs)),
            lambda: FExists(rand_of_type(md - 1, Natural(), fvs),
                            rand_of_type(md - 1, Formula(), fvs))])()
    if isinstance(typ, Boolean):
        return random.choice([BTrue(), BFalse()])
    if isinstance(typ, List):
        return encode_list([rand_of_type(md, typ.t) for i in range(utils.randnat())])
    if isinstance(typ, Arrow):
        v = fresh(fvs)
        x = Lambda(v, rand_of_type(md, typ.t2, {**fvs, v: typ.t1}))
        #print('RS ', fvs, v, typ.t1, typ.t2, string(x))
        return x
    print(typ, fvs)
    raise NotImplementedError

def _rand_of_type(md, typ, fvs=None):
    x = _rand_of_type(md, typ, fvs)
    print(f'md={md} typ={typ} fvs={fvs} => {string(x)}')
    return x

def rand_of_type(md, typ, fvs=None):
    if fvs is None:
        fvs = {}

    x = random_variable(md, typ, fvs)
    if md <= 0:
        if x is None:
            return random_specific_base(typ, fvs)
        else:
            return random.choice([
                lambda: x,
                lambda: random_specific_base(typ, fvs)])()
    else:
        if x is None:
            return random.choice([
                lambda: rand_of_type(md - 1, typ, fvs),
                lambda: random_application(md, typ, fvs),
                # lambda: random_fixpoint(md, typ, fvs),
                lambda: random_ncase(md, typ, fvs),
                lambda: random_ifthenelse(md, typ, fvs),
                lambda: random_lcase(md, typ, fvs),
                lambda: random_tcase(md, typ, fvs),
                lambda: random_fcase(md, typ, fvs),
                lambda: random_specific(md, typ, fvs)])()
        else:
            return random.choice([
                lambda: rand_of_type(md - 1, typ, fvs),
                lambda: x,
                lambda: random_application(md, typ, fvs),
                # lambda: random_fixpoint(md, typ, fvs),
                lambda: random_ncase(md, typ, fvs),
                lambda: random_ifthenelse(md, typ, fvs),
                lambda: random_lcase(md, typ, fvs),
                lambda: random_tcase(md, typ, fvs),
                lambda: random_fcase(md, typ, fvs),
                lambda: random_specific(md, typ, fvs)])()

# the lambda_L calculus

# types

Natural = namedtuple('Natural', '')
Term = namedtuple('Term', '')
Formula = namedtuple('Formula', '')
Boolean = namedtuple('Boolean', '')
List = namedtuple('List', 't')
Arrow = namedtuple('Arrow', 't1 t2')

# explicitly typed

class Typed(namedtuple('Typed', 'term typ')):
    pass

# basic lambda calculus

Variable = namedtuple('Variable', 'x')
Application = namedtuple('Application', 't1 t2')
Lambda = namedtuple('Lambda', 'x t')
Fixpoint = namedtuple('Fixpoint', 'x t')

# with natural numbers

NZero = namedtuple('NZero', '')
NSuc = namedtuple('NSuc', 't')
NCase = namedtuple('NCase', 't0 t1 x2 t2')

# with booleans

BFalse = namedtuple('BFalse', '')
BTrue = namedtuple('BTrue', '')
BIfThenElse = namedtuple('BIfThenElse', 't0 t1 t2')

# with lists

LEmpty = namedtuple('LEmpty', '')
LCons = namedtuple('LCons', 't1 t2')
LCase = namedtuple('LCase', 't0 t1 x2 y2 t2')

# with terms

TZero = namedtuple('TZero', '')
TSuc = namedtuple('TSuc', 't')
TVar = namedtuple('TVar', 't')
TCase = namedtuple('TCase', 't0 t1 x2 t2 x3 t3')

# with formulae

FBottom = namedtuple('FBottom', '')
FEquality = namedtuple('FEquality', 't1 t2')
FImplication = namedtuple('FImplication', 't1 t2')
FConjunction = namedtuple('FConjunction', 't1 t2')
FDisjunction = namedtuple('FDisjunction', 't1 t2')
FForall = namedtuple('FForall', 't1 t2')
FExists = namedtuple('FExists', 't1 t2')
FCase = namedtuple('FCase', 't0, t1, x2 y2 t2, x3 y3 t3, x4 y4 t4, x5 y5 t5, x6 y6 t6, x7 y7 t7')

# values

def value(t):
    if isinstance(t, (Lambda, NZero, BFalse, BTrue, LEmpty, TZero, FBottom)):
        return True
    if isinstance(t, (NSuc, TSuc, TVar)):
        return value(t.t)
    if isinstance(t, (LCons, FEquality, FImplication, FConjunction, FDisjunction, FForall, FExists)):
        return value(t.t1) and value(t.t2)
    return False

# substitution

# def subst(term, v, t):
#    result = _subst(term, v, t)
#    print('SUBST', term, '[', v, '/', t, '] -->', result)
#    return result

def subst(term, v, t):
    if isinstance(term, Variable):
        if term == v:
            # print(term, v)
            return t
        else:
            return term
    if isinstance(term, Application):
        return Application(subst(term.t1, v, t),
                           subst(term.t2, v, t))
    if isinstance(term, Lambda):
        if term.x == v:
            # print(term.x, v)
            return term
        else:
            return Lambda(term.x, subst(term.t, v, t))
    if isinstance(term, Fixpoint):
        if term.x == v:
            # print(term.x, v)
            return term
        else:
            return Fixpoint(term.x, subst(term.t, v, t))
    if isinstance(term, NZero):
        return term
    if isinstance(term, NSuc):
        return NSuc(subst(term.t, v, t))
    if isinstance(term, NCase):
        return NCase(subst(term.t0, v, t),
                     subst(term.t1, v, t),
                     term.x2,
                     subst(term.t2, v, t) if term.x2 != v else term.t2)
    if isinstance(term, BFalse):
        return term
    if isinstance(term, BTrue):
        return term
    if isinstance(term, BIfThenElse):
        return BIfThenElse(subst(term.t0, v, t),
                           subst(term.t1, v, t),
                           subst(term.t2, v, t))
    if isinstance(term, LEmpty):
        return term
    if isinstance(term, LCons):
        return LCons(subst(term.t1, v, t), subst(term.t2, v, t))
    if isinstance(term, LCase):
        return LCase(subst(term.t0, v, t),
                     subst(term.t1, v, t),
                     term.x2, term.y2,
                     subst(term.t2, v, t) if term.x2 != v and term.y2 != v else term.t2)
    if isinstance(term, TZero):
        return term
    if isinstance(term, TSuc):
        return TSuc(subst(term.t, v, t))
    if isinstance(term, TVar):
        return TVar(subst(term.t, v, t))
    if isinstance(term, TCase):
        return TCase(subst(term.t0, v, t),
                     subst(term.t1, v, t),
                     term.x2,
                     subst(term.t2, v, t) if term.x2 != v else term.t2,
                     term.x3,
                     subst(term.t3, v, t) if term.x3 != v else term.t3)
    if isinstance(term, FBottom):
        return term
    if isinstance(term, FEquality):
        return FEquality(subst(term.t1, v, t), subst(term.t2, v, t))
    if isinstance(term, FImplication):
        return FImplication(subst(term.t1, v, t), subst(term.t2, v, t))
    if isinstance(term, FConjunction):
        return FConjunction(subst(term.t1, v, t), subst(term.t2, v, t))
    if isinstance(term, FDisjunction):
        return FDisjunction(subst(term.t1, v, t), subst(term.t2, v, t))
    if isinstance(term, FForall):
        return FForall(subst(term.t1, v, t), subst(term.t2, v, t))
    if isinstance(term, FExists):
        return FExists(subst(term.t1, v, t), subst(term.t2, v, t))
    if isinstance(term, FCase):
        return FCase(subst(term.t0, v, t),
                     subst(term.t1, v, t),
                     term.x2, term.y2,
                     subst(term.t2, v, t) if term.x2 != v and term.y2 != v else term.t2,
                     term.x3, term.y3,
                     subst(term.t3, v, t) if term.x3 != v and term.y3 != v else term.t3,
                     term.x4, term.y4,
                     subst(term.t4, v, t) if term.x4 != v and term.y4 != v else term.t4,
                     term.x5, term.y5,
                     subst(term.t5, v, t) if term.x5 != v and term.y5 != v else term.t5,
                     term.x6, term.y6,
                     subst(term.t6, v, t) if term.x6 != v and term.y6 != v else term.t6,
                     term.x7, term.y7,
                     subst(term.t7, v, t) if term.x7 != v and term.y7 != v else term.t7)
    raise NotImplementedError

class RanOutOfFuel(BaseException):
    def __init__(self, term):
        self.term = term

def reduce(fuel, term):
    while fuel:
        if value(term):
            return term
        term = do_reduce(term)
        fuel -= 1
    raise RanOutOfFuel(term)

def _do_reduce(term):
    print('TRYING TO REDUCE', term)
    r = _do_reduce(term)
    print(string(term), '--->', string(r))
    return r

def do_reduce(term):
    if isinstance(term, Variable):
        return term
    if isinstance(term, Application):
        if not value(term.t1):
            return Application(do_reduce(term.t1), term.t2)
        if not value(term.t2):
            return Application(term.t1, do_reduce(term.t2))
        if isinstance(term.t1, Lambda):
            return subst(term.t1.t, term.t1.x, term.t2)
        print('application failed')
    if isinstance(term, Fixpoint):
        return subst(term.t, term.x, term)
    if isinstance(term, NSuc):
        return NSuc(do_reduce(term.t))
    if isinstance(term, NCase):
        if not value(term.t0):
            return NCase(do_reduce(term.t0), term.t1, term.x2, term.t2)
        elif isinstance(term.t0, NZero):
            return term.t1
        elif isinstance(term.t0, NSuc):
            return subst(term.t2, term.x2, term.t0.t)
        print('ncase failed')
    if isinstance(term, BIfThenElse):
        if not value(term.t0):
            return BIfThenElse(do_reduce(term.t0), term.t1, term.t2)
        elif isinstance(term.t0, BTrue):
            return term.t1
        elif isinstance(term.t0, BFalse):
            return term.t2
        print('bifthenelse failed')
    if isinstance(term, LCons):
        if not value(term.t1):
            return LCons(do_reduce(term.t1), term.t2)
        if not value(term.t2):
            return LCons(term.t1, do_reduce(term.t2))
        print('lcons failed')
    if isinstance(term, LCase):
        if not value(term.t0):
            return LCase(do_reduce(term.t0), term.t1, term.x2, term.y2, term.t2)
        elif isinstance(term.t0, LEmpty):
            return term.t1
        elif isinstance(term.t0, LCons):
            return subst(subst(term.t2, term.x2, term.t0.t1),
                         term.y2, term.t0.t2)
        print('lcase failed')
    if isinstance(term, TSuc):
        return TSuc(do_reduce(term.t))
    if isinstance(term, TVar):
        return TVar(do_reduce(term.t))
    if isinstance(term, TCase):
        if not value(term.t0):
            return TCase(do_reduce(term.t0), term.t1, term.x2, term.t2, term.x3, term.t3)
        elif isinstance(term.t0, TZero):
            return term.t1
        elif isinstance(term.t0, TSuc):
            return subst(term.t2, term.x2, term.t0.t)
        elif isinstance(term.t0, TVar):
            return subst(term.t3, term.x3, term.t0.t)
        print('tcase failed')
    if isinstance(term, (FEquality, FImplication, FDisjunction, FConjunction)):
        if not value(term.t1):
            return term.__class__(do_reduce(term.t1), term.t2)
        if not value(term.t2):
            return term.__class__(term.t1, do_reduce(term.t2))
        return term
    if isinstance(term, (FForall, FExists)):
        if not value(term.t1):
            return term.__class__(do_reduce(term.t1), term.t2)
        if not value(term.t2):
            return term.__class__(term.t1, do_reduce(term.t2))
        return term
    if isinstance(term, FCase):
        if not value(term.t0):
            return FCase(do_reduce(term.t0), term.t1, term.x2, term.y2, term.t2, term.x3, term.y3, term.t3, term.x4, term.y4, term.t4, term.x5, term.y5, term.t5, term.x6, term.y6, term.t6, term.x7, term.y7, term.t7)
        elif isinstance(term.t0, FBottom):
            return term.t1
        elif isinstance(term.t0, FEquality):
            return subst(subst(term.t2, term.x2, term.t0.t1),
                         term.y2, term.t0.t2)
        elif isinstance(term.t0, FImplication):
            return subst(subst(term.t3, term.x3, term.t0.t1),
                         term.y3, term.t0.t2)
        elif isinstance(term.t0, FConjunction):
            return subst(subst(term.t4, term.x4, term.t0.t1),
                         term.y4, term.t0.t2)
        elif isinstance(term.t0, FDisjunction):
            return subst(subst(term.t5, term.x5, term.t0.t1),
                         term.y5, term.t0.t2)
        elif isinstance(term.t0, FForall):
            return subst(subst(term.t6, term.x6, term.t0.t1),
                         term.y6, term.t0.t2)
        elif isinstance(term.t0, FExists):
            return subst(subst(term.t7, term.x7, term.t0.t1),
                         term.y7, term.t0.t2)
        print('fcase failed')
    print(term)
    raise NotImplementedError

def string(term):
    if isinstance(term, Variable):
        return f'{term.x}'
    if isinstance(term, Application):
        return f'({string(term.t1)} ∘ {string(term.t2)})'
    if isinstance(term, Lambda):
        return f'(λ{string(term.x)}.{string(term.t)})'
    if isinstance(term, Fixpoint):
        return f'(μ{string(term.x)}.{string(term.t)})'
    if isinstance(term, NZero):
        return 'z'
    if isinstance(term, NSuc):
        return f's{string(term.t)}'
    if isinstance(term, NCase):
        return f'(ℕ-case {string(term.t0)} [z => {string(term.t1)} | s {string(term.x2)} => {string(term.t2)}])'
    if isinstance(term, BFalse):
        return 'false'
    if isinstance(term, BTrue):
        return 'true'
    if isinstance(term, BIfThenElse):
        return f'(if {string(term.t0)} then {string(term.t1)} else {string(term.t2)})'
    if isinstance(term, LEmpty):
        return '[]'
    if isinstance(term, LCons):
        return f'{string(term.t1)} :: {string(term.t2)}'
    if isinstance(term, LCase):
        return f'(L-case {string(term.t0)} [ [] => {string(term.t1)} | {string(term.x2)} :: {string(term.y2)} => {string(term.t2)}])'
    if isinstance(term, TZero):
        return f'zero'
    if isinstance(term, TSuc):
        return f'succ({string(term.t)})'
    if isinstance(term, TVar):
        return f'x{string(term.t)}'
    if isinstance(term, TCase):
        return f'(T-Case {string(term.t0)} [ zero => {string(term.t1)} | succ {string(term.x2)} => {string(term.t2)} | x{string(term.x3)} => {string(term.t3)}])'
    if isinstance(term, FBottom):
        return '⊥'
    if isinstance(term, FEquality):
        return f'{string(term.t1)} = {string(term.t2)}'
    if isinstance(term, FImplication):
        return f'{string(term.t1)} → {string(term.t2)}'
    if isinstance(term, FConjunction):
        return f'{string(term.t1)} ∧ {string(term.t2)}'
    if isinstance(term, FDisjunction):
        return f'{string(term.t1)} ∨ {string(term.t2)}'
    if isinstance(term, FForall):
        return f'∀ {string(term.t1)} . {string(term.t2)}'
    if isinstance(term, FExists):
        return f'∃ {string(term.t1)} . {string(term.t2)}'
    if isinstance(term, FCase):
        return (f'(F-case {string(term.t0)} [⊥ => {string(term.t1)} | '
                f'{string(term.x2)} = {string(term.y2)} => {string(term.t2)} | '
                f'{string(term.x3)} → {string(term.y3)} => {string(term.t3)} | '
                f'{string(term.x4)} ∧ {string(term.y4)} => {string(term.t4)} | '
                f'{string(term.x5)} ∨ {string(term.y5)} => {string(term.t5)} | '
                f'∀ {string(term.x6)} . {string(term.y6)} => {string(term.t6)} | '
                f'∃ {string(term.x7)} . {string(term.y7)} => {string(term.t7)}])')
    print(term)
    raise NotImplementedError


def subexprs(term):
    return [term] + [y for x in strict_subexprs(term) for y in subexprs(x)]

def strict_subexprs(term):
    if isinstance(term, (Variable, NZero, BFalse, BTrue, LEmpty, TZero, FBottom)):
        return []
    if isinstance(term, (Lambda, Fixpoint, NSuc, TSuc, TVar)):
        return [term.t]
    if isinstance(term, (Application, LCons, FEquality, FImplication, FConjunction, FDisjunction, FForall, FExists)):
        return [term.t1, term.t2]
    if isinstance(term, NCase):
        return [term.t0, term.t1, term.t2]
    if isinstance(term, BIfThenElse):
        return [term.t0, term.t1, term.t2]
    if isinstance(term, LCase):
        return [term.t0, term.t1, term.t2]
    if isinstance(term, TCase):
        return [term.t0, term.t1, term.t2, term.t3]
    if isinstance(term, FCase):
        return [term.t0, term.t1, term.t2, term.t4, term.t5, term.t6, term.t7]
    raise NotImplementedError

def example(term):
    if isinstance(term, Variable):
        pass
    if isinstance(term, Application):
        pass
    if isinstance(term, Lambda):
        pass
    if isinstance(term, Fixpoint):
        pass
    if isinstance(term, NZero):
        pass
    if isinstance(term, NSuc):
        pass
    if isinstance(term, NCase):
        pass
    if isinstance(term, BFalse):
        pass
    if isinstance(term, BTrue):
        pass
    if isinstance(term, BIfThenElse):
        pass
    if isinstance(term, LEmpty):
        pass
    if isinstance(term, LCons):
        pass
    if isinstance(term, LCase):
        pass
    if isinstance(term, TZero):
        pass
    if isinstance(term, TSuc):
        pass
    if isinstance(term, TVar):
        pass
    if isinstance(term, TCase):
        pass
    if isinstance(term, FBottom):
        pass
    if isinstance(term, FEquality):
        pass
    if isinstance(term, FImplication):
        pass
    if isinstance(term, FConjunction):
        pass
    if isinstance(term, FDisjunction):
        pass
    if isinstance(term, FForall):
        pass
    if isinstance(term, FExists):
        pass
    if isinstance(term, FCase):
        pass
    raise NotImplementedError

if __name__ == '__main__':
    main()
