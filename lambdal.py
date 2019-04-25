from collections import namedtuple, Counter
import itertools
import math
import random
import utils
from formula import zero, succ, bot, forall, exists, impl, conj, disj, equality, application, variable
import exp2

POPSIZE = 100
REDUCTION_STEPS = 200
TOURNAMENT_SIZE = 5
TOURNAMENT_PROB = 0.9
NUMBER_SEQUENTS = 50

def pairs(list):
    return [(list[2 * i], list[2 * i + 1]) for i in range(len(list) // 2)]

def rand_term_guesser(depth):
    varP = Variable(List(Formula()), 'p')
    varG = Variable(Formula(), 'g')
    expr = rand_of_type(depth, Term(), {
        varP: varP.type,
        varG: varG.type,
    })
    print(string(expr))
    return Lambda(varP, Lambda(varG, expr))

def encode_term(t, variables=None):
    if variables is None:
        variables = []
    # print('TERM', t, type(t))
    if isinstance(t, application):
        if len(t.ts) == 0:
            return TZero()
        return TSuc(encode_term(t.ts[0], variables))
    if isinstance(t, variable):
        return TVar(encode_nat(variables.index(t.name)))
        #return TSuc(encode_term(t.ts[0], variables))
    raise NotImplementedError

def encode_formula(f, variables=None):
    if variables is None:
        variables = []
    # print('FORMULA', f, type(f))
    if f is bot:
        return FBottom()
    if isinstance(f, forall):
        variables = variables + [f.v.name]
        return FForall(encode_nat(variables.index(f.v.name)), encode_formula(f.p, variables))
    if isinstance(f, exists):
        variables = variables + [f.v.name]
        return FExists(encode_nat(variables.index(f.v.name)), encode_formula(f.p, variables))
    if isinstance(f, conj):
        return FConjunction(encode_formula(f.a, variables),
                            encode_formula(f.b, variables))
    if isinstance(f, disj):
        return FDisjunction(encode_formula(f.a, variables),
                            encode_formula(f.b, variables))
    if isinstance(f, impl):
        return FImplication(encode_formula(f.a, variables),
                            encode_formula(f.b, variables))
    if isinstance(f, equality):
        return FEquality(encode_term(f.t1, variables),
                         encode_term(f.t2, variables))
    raise NotImplementedError

def encode_sequent(sequent):
    premises, goal = sequent
    return encode_list([encode_formula(p) for p in premises], Formula()), encode_formula(goal)

def calc_fitness(termguesser, sequents):
    fitnesses = []
    for sequent in sequents:
        premises, goal = encode_sequent(sequent)
        fitnesses.append(do_calc_fitness(termguesser, premises, goal))
    return sum(fitnesses) / len(fitnesses)

def do_calc_fitness(termguesser, premises, goal):
    tg = Application(Application(termguesser, premises), goal)
    try:
        v = reduce(REDUCTION_STEPS, tg)
    except RanOutOfFuel:
        return 0
    if not value(v):
        return 0
    if v == TSuc(TZero()):
        #print('DING', string(termguesser))
        return 1.0
    return 0.0

def tournament(population, fitnesses):
    indices = random.sample(range(len(population)), k=TOURNAMENT_SIZE)
    indices.sort(key=lambda i: 1 - fitnesses[i])
    for i in indices[:-1]:
        if random.random() < TOURNAMENT_PROB:
            return population[i]
    return population[indices[-1]]

def mutate(t):
    return t

def crossover(t1, t2):
    s1 = subexprs(t1)
    s2 = subexprs(t2)
    # print('s1')
    # for x in s1:
    #     print('\t', x)
    # print('s2')
    # for x in s2:
    #     print('\t', x)
    s1t = {(x, l): vtype(x) for x, l in s1}
    s2t = {(x, l): vtype(x) for x, l in s2}
    # print('s1t')
    # for x in s1t.items():
    #     print('\t', x)
    # print('s2t')
    # for x in s2t.items():
    #     print('\t', x)
    t1s = {}
    for k, v in s1t.items():
        t1s[(v, str(v))] = t1s.get((v, str(v)), [])
        t1s[(v, str(v))].append(k)
    t2s = {}
    for k, v in s2t.items():
        t2s[(v, str(v))] = t2s.get((v, str(v)), [])
        t2s[(v, str(v))].append(k)
    # print('t1s')
    # for ((x, y), z) in t1s.items():
    #     print('\t', (x, z))
    # print('t2s')
    # for ((x, y), z) in t2s.items():
    #     print('\t', (x, z))
    # for (typ, strtyp) in t1s.keys() & t2s.keys():
    #     print('Type:', typ)
    #     print('Left:')
    #     for x, l in t1s[(typ, strtyp)]:
    #         print('\t', string(x), string(l(...)))
    #     print('Right:')
    #     for x, l in t2s[(typ, strtyp)]:
    #         print('\t', string(x), string(l(...)))
    #     print()

    shared = list(t1s.keys() & t2s.keys())
    # print(shared)
    typ = random.choices(population=shared,
                         weights=[len(t1s[k]) * len(t2s[k]) for k in shared])[0]
    xl, ll = random.choice(t1s[typ])
    xr, lr = random.choice(t2s[typ])
    # print(typ, string(xl), string(ll(...)), string(xr), string(lr(...)))
    return [ll(xr), lr(xl)]

def evolve():
    population = [rand_term_guesser(2) for i in range(POPSIZE)]
    for iteration in itertools.count(0):
        sequents = exp2.random_statements(max_depth=3,
                                          allow_dups=True,
                                          num_stmts=NUMBER_SEQUENTS,
                                          connectives=None)
        fitnesses = [calc_fitness(tg, sequents) for tg in population]
        crossover_base = [tournament(population, fitnesses) for i in range(2 * POPSIZE)]
        indices = pairs(utils.shuffled(range(2 * POPSIZE)))
        population = [x for i, j in indices for x in crossover(crossover_base[i], crossover_base[j])]
        # print(population)
        for i in range(POPSIZE):
            population[i] = mutate(population[i])
        print('POPULATION:', [string(x) for x in population])
        print('FITNESSES:', fitnesses)
        print('CROSSOVERB:', [string(x) for x in crossover_base])
        print('INDICES:', indices)

def main():
    # sucC = Lambda(Variable('n'), NSuc(Variable('n')))
    # twoC = Lambda(
    #     Variable('s'),
    #     Lambda(
    #         Variable('z'),
    #         Application(Variable('s'), Application(Variable('s'), Variable('z')))))
    # plusC = Lambda(
    #     Variable('m'),
    #     Lambda(
    #         Variable('n'),
    #         Lambda(
    #             Variable('s'),
    #             Lambda(
    #                 Variable('z'),
    #                 Application(
    #                     Application(Variable('m'), Variable('s')),
    #                     Application(
    #                         Application(Variable('n'), Variable('s')),
    #                         Variable('z')))))))
    # fourC = Application(Application(plusC, twoC), twoC)
    # length = Fixpoint(Variable('l'), Lambda(Variable('x'),
    #                   LCase(Variable('x'),
    #                         NZero(),
    #                         Variable('y'), Variable('z'), NSuc(Application(Variable('l'), Variable('z'))))))
    # list123 = LCons(NSuc(NZero()), LCons(NSuc(NSuc(NZero())), LCons(NSuc(NSuc(NSuc(NZero()))), LEmpty(Natural()))))
    # tests = {
    #     # Application(length, list123): NSuc(NSuc(NSuc(NZero()))),
    #     # Application(Application(fourC, sucC), NZero()): NSuc(NSuc(NSuc(NSuc(NZero())))),
    # }

    # goal_type = Arrow(List(Formula()), Arrow(Formula(), Arrow(Natural(), Term())))

    # for expression, expected in tests.items():
    #     actual = reduce(100, expression)
    #     if isinstance(actual, expected.__class__) and actual == expected:
    #         print(string(expression), '--->', string(expected))
    #     else:
    #         print(string(expression), '--->', string(actual))
    #         print(string(expression), '-/->', string(expected))
    #         raise RuntimeError

    counter = Counter()

    for i in itertools.count():
        expr = rand_of_type(2, Term(), {
            Variable(List(Formula()), 'p'): List(Formula()),
            Variable(Formula(), 'g'): Formula()
        })
        premises = LCons(FEquality(TVar(NZero()), TSuc(TVar(NZero()))), LEmpty(Formula()))
        goal = FBottom()
        try:
            result = reduce(50000, Application(Application(Lambda(Variable(List(Formula()), 'p'), Lambda(Variable(Formula(), 'g'), expr)), premises), goal))
        except RanOutOfFuel as exc:
            continue
            # print('Problematic term:', string(expr))
            # print('Problematic term:', string(exc.term))
        print(string(expr), end='\n--->\n')
        print(string(result))
        counter[string(result)] += 1
        print(counter)
        if i % 1000 == 0 and i != 0:
            print(i)

def fresh(fvs, typ):
    return next(Variable(typ, str(i)) for i in itertools.count() if Variable(typ, str(i)) not in fvs)

def encode_list(l, typ):
    result = LEmpty(typ)
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
    v = fresh(fvs, typ)
    return Fixpoint(v, rand_of_type(md - 1, typ, {v: typ, **fvs}))

def random_ncase(md, typ, fvs):
    v = fresh(fvs, Natural())
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
    v1 = fresh(fvs, t)
    v2 = fresh({v1: t, **fvs}, List(t))
    return LCase(rand_of_type(md - 1, List(t), fvs),
                 rand_of_type(md - 1, typ, fvs),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: t, v2: List(t), **fvs}))

def random_tcase(md, typ, fvs):
    v1 = fresh(fvs, Term())
    v2 = fresh(fvs, Natural())
    return TCase(rand_of_type(md - 1, Term(), fvs),
                 rand_of_type(md - 1, typ, fvs),
                 v1,
                 rand_of_type(md - 1, typ, {v1: Term(), **fvs}),
                 v2,
                 rand_of_type(md - 1, typ, {v2: Natural(), **fvs}))

def random_fcase(md, typ, fvs):
    v1 = fresh(fvs, Term())
    v2 = fresh({v1: Term(), **fvs}, Term())
    v3 = fresh(fvs, Formula())
    v4 = fresh({v1: Formula(), **fvs}, Formula())
    v5 = fresh(fvs, Natural())
    v6 = fresh({v1: Natural(), **fvs}, Formula())
    return FCase(rand_of_type(md - 1, Formula(), fvs),
                 rand_of_type(md - 1, typ, fvs),
                 v1, v2,
                 rand_of_type(md - 1, typ, {v1: Term(), v2: Term(), **fvs}),
                 v3, v4,
                 rand_of_type(md - 1, typ, {v1: Formula(), v2: Formula(), **fvs}),
                 v3, v4,
                 rand_of_type(md - 1, typ, {v1: Formula(), v2: Formula(), **fvs}),
                 v3, v4,
                 rand_of_type(md - 1, typ, {v1: Formula(), v2: Formula(), **fvs}),
                 v5, v6,
                 rand_of_type(md - 1, typ, {v1: Natural(), v2: Formula(), **fvs}),
                 v5, v6,
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
        return LEmpty(typ.t)
    if isinstance(typ, Arrow):
        v = fresh(fvs, typ.t1)
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
        return encode_list([rand_of_type(md, typ.t) for i in range(utils.randnat())], typ.t)
    if isinstance(typ, Arrow):
        v = fresh(fvs, typ.t1)
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

# basic lambda calculus

Variable = namedtuple('Variable', 'type x')
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

LEmpty = namedtuple('LEmpty', 'type')
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
    if term is ...:
        return '_'
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

def removed(dct, key):
    return {k: v for k, v in dct.items() if k != key}

def dict_union(d1, d2):
    return {k: v for k, v in itertools.chain(d1.items(), d2.items())}

def vtype(term):
    d, ty = fvtype(term)
    # print(d.items())
    return (tuple(sorted(d.items())), ty)

def fvtype(term):
    if isinstance(term, Variable):
        return {term.x: term.type}, term.type
    if isinstance(term, Application):
        vs1, t1 = fvtype(term.t1)
        vs2, t2 = fvtype(term.t2)
        assert isinstance(t1, Arrow)
        assert type_equal(t2, t1.t1)
        return {**vs1, **vs2}, t1.t2
    if isinstance(term, Lambda):
        v, typ = fvtype(term.t)
        return {x: t for x, t in v.items() if x != term.x.x}, Arrow(term.x.type, typ)
    if isinstance(term, Fixpoint):
        return fvtype(term.t)
    if isinstance(term, NZero):
        return {}, Natural()
    if isinstance(term, NSuc):
        return fvtype(term.t)
    if isinstance(term, NCase):
        vs0, ty0 = fvtype(term.t0)
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs0, **vs1, **{k: v for k, v in vs2.items() if k != term.x2.x}}, ty1
    if isinstance(term, BFalse):
        return {}, Boolean()
    if isinstance(term, BTrue):
        return {}, Boolean()
    if isinstance(term, BIfThenElse):
        vs0, ty0 = fvtype(term.t0)
        if not type_equal(ty0, Boolean()):
            raise
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs0, **vs1, **vs2}, ty1
    if isinstance(term, LEmpty):
        return {}, List(term.type)
    if isinstance(term, LCons):
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs1, **vs2}, ty2
    if isinstance(term, LCase):
        vs0, ty0 = fvtype(term.t0)
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs0, **vs1, **{k: v for k, v in vs2.items() if k != term.x2.x and k != term.y2.x}}, ty1
    if isinstance(term, TZero):
        return {}, Term()
    if isinstance(term, TSuc):
        return fvtype(term.t)
    if isinstance(term, TVar):
        v, t = fvtype(term.t)
        return v, Term()
    if isinstance(term, TCase):
        return fvtype(term.t1)
        vs0, ty0 = fvtype(term.t0)
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        vs3, ty3 = fvtype(term.t3)
        return {**vs0, **vs1, **{k: v for k, v in vs2.items() if k != term.x2.x}, **{k: v for k, v in vs3.items() if k != term.x3.x}}, ty1
    if isinstance(term, FBottom):
        return {}, Formula()
    if isinstance(term, FEquality):
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs1, **vs2}, Formula()
    if isinstance(term, FImplication):
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs1, **vs2}, Formula()
    if isinstance(term, FConjunction):
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs1, **vs2}, Formula()
    if isinstance(term, FDisjunction):
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs1, **vs2}, Formula()
    if isinstance(term, FForall):
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs1, **vs2}, Formula()
    if isinstance(term, FExists):
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        return {**vs1, **vs2}, Formula()
    if isinstance(term, FCase):
        vs0, ty0 = fvtype(term.t0)
        vs1, ty1 = fvtype(term.t1)
        vs2, ty2 = fvtype(term.t2)
        vs3, ty3 = fvtype(term.t3)
        vs4, ty4 = fvtype(term.t4)
        vs5, ty5 = fvtype(term.t5)
        vs6, ty6 = fvtype(term.t6)
        vs7, ty7 = fvtype(term.t7)
        vs2 = {k: v for k, v in vs2.items() if k != term.x2.x and k != term.y2.x}
        vs3 = {k: v for k, v in vs3.items() if k != term.x3.x and k != term.y3.x}
        vs4 = {k: v for k, v in vs4.items() if k != term.x4.x and k != term.y4.x}
        vs5 = {k: v for k, v in vs5.items() if k != term.x5.x and k != term.y5.x}
        vs6 = {k: v for k, v in vs6.items() if k != term.x6.x and k != term.y6.x}
        vs7 = {k: v for k, v in vs7.items() if k != term.x7.x and k != term.y7.x}
        return {**vs0, **vs1, **vs2, **vs3, **vs4, **vs5, **vs6, **vs7}, ty1
    raise NotImplementedError

def ltype(term):
    if isinstance(term, Variable):
        return term.type
    if isinstance(term, Application):
        return ltype(term.t1).t2
    if isinstance(term, Lambda):
        return Arrow(term.x.type, ltype(term.t))
    if isinstance(term, Fixpoint):
        return ltype(term.t)
    if isinstance(term, (NZero, NSuc)):
        return Natural()
    if isinstance(term, NCase):
        return ltype(term.t1)
    if isinstance(term, BFalse):
        return Boolean()
    if isinstance(term, BTrue):
        return Boolean()
    if isinstance(term, BIfThenElse):
        return ltype(term.t1)
    if isinstance(term, LEmpty):
        return List(term.type)
    if isinstance(term, LCons):
        return ltype(term.t2)
    if isinstance(term, LCase):
        return ltype(term.t1)
    if isinstance(term, TZero):
        return Term()
    if isinstance(term, TSuc):
        return Term()
    if isinstance(term, TVar):
        return Term()
    if isinstance(term, TCase):
        return ltype(term.t1)
    if isinstance(term, FBottom):
        return Formula()
    if isinstance(term, FEquality):
        return Formula()
    if isinstance(term, FImplication):
        return Formula()
    if isinstance(term, FConjunction):
        return Formula()
    if isinstance(term, FDisjunction):
        return Formula()
    if isinstance(term, FForall):
        return Formula()
    if isinstance(term, FExists):
        return Formula()
    if isinstance(term, FCase):
        return ltype(term.t1)
    raise NotImplementedError

def compose(co_x, co_y):
    return (lambda z: co_x(co_y(z)))

def subexprs(term):
    return [(term, lambda x: x)] + [(y, compose(co_x, co_y)) for x, co_x in strict_subexprs(term) for y, co_y in subexprs(x)]

def strict_subexprs(term):
    if isinstance(term, (Variable, NZero, BFalse, BTrue, LEmpty, TZero, FBottom)):
        return []
    if isinstance(term, (Lambda, Fixpoint)):
        return [(term.t, lambda x: term.__class__(term.x, x))]
    if isinstance(term, (NSuc, TSuc, TVar)):
        return [(term.t, lambda x: term.__class__(x))]
    if isinstance(term, (Application, LCons, FEquality, FImplication, FConjunction, FDisjunction, FForall, FExists)):
        return [(term.t1, lambda x: term.__class__(x, term.t2)),
                (term.t2, lambda y: term.__class__(term.t1, y))]
    if isinstance(term, NCase):
        return [(term.t0, lambda x: NCase(x, term.t1, term.x2, term.t2)),
                (term.t1, lambda y: NCase(term.t0, y, term.x2, term.t2)),
                (term.t2, lambda z: NCase(term.t0, term.t1, term.x2, z))]
    if isinstance(term, BIfThenElse):
        return [(term.t0, lambda x: BIfThenElse(x, term.t1, term.t2)),
                (term.t1, lambda y: BIfThenElse(term.t0, y, term.t2)),
                (term.t2, lambda z: BIfThenElse(term.t0, term.t1, z))]
    if isinstance(term, LCase):
        return [(term.t0, lambda x: LCase(x, term.t1, term.x2, term.y2, term.t2)),
                (term.t1, lambda y: LCase(term.t0, y, term.x2, term.y2, term.t2)),
                (term.t2, lambda z: LCase(term.t0, term.t1, term.x2, term.y2, z))]
    if isinstance(term, TCase):
        return [(term.t0, lambda x: TCase(x, term.t1, term.x2, term.t2, term.x3, term.t3)),
                (term.t1, lambda y: TCase(term.t0, y, term.x2, term.t2, term.x3, term.t3)),
                (term.t2, lambda z: TCase(term.t0, term.t1, term.x2, z, term.x3, term.t3)),
                (term.t3, lambda w: TCase(term.t0, term.t1, term.x2, term.t2, term.x3, w))]
    if isinstance(term, FCase):
        return [(term.t0, lambda x: FCase(x, term.t1, term.x2, term.y2, term.t2, term.x3, term.y3, term.t3, term.x4, term.y4, term.t4, term.x5, term.y5, term.t5, term.x6, term.y6, term.t6, term.x7, term.y7, term.t7)),
                (term.t1, lambda x: FCase(term.t0, x, term.x2, term.y2, term.t2, term.x3, term.y3, term.t3, term.x4, term.y4, term.t4, term.x5, term.y5, term.t5, term.x6, term.y6, term.t6, term.x7, term.y7, term.t7)),
                (term.t2, lambda x: FCase(term.t0, term.t1, term.x2, term.y2, x, term.x3, term.y3, term.t3, term.x4, term.y4, term.t4, term.x5, term.y5, term.t5, term.x6, term.y6, term.t6, term.x7, term.y7, term.t7)),
                (term.t3, lambda x: FCase(term.t0, term.t1, term.x2, term.y2, term.t2, term.x3, term.y3, x, term.x4, term.y4, term.t4, term.x5, term.y5, term.t5, term.x6, term.y6, term.t6, term.x7, term.y7, term.t7)),
                (term.t4, lambda x: FCase(term.t0, term.t1, term.x2, term.y2, term.t2, term.x3, term.y3, term.t3, term.x4, term.y4, x, term.x5, term.y5, term.t5, term.x6, term.y6, term.t6, term.x7, term.y7, term.t7)),
                (term.t5, lambda x: FCase(term.t0, term.t1, term.x2, term.y2, term.t2, term.x3, term.y3, term.t3, term.x4, term.y4, term.t4, term.x5, term.y5, x, term.x6, term.y6, term.t6, term.x7, term.y7, term.t7)),
                (term.t6, lambda x: FCase(term.t0, term.t1, term.x2, term.y2, term.t2, term.x3, term.y3, term.t3, term.x4, term.y4, term.t4, term.x5, term.y5, term.t5, term.x6, term.y6, x, term.x7, term.y7, term.t7)),
                (term.t7, lambda x: FCase(term.t0, term.t1, term.x2, term.y2, term.t2, term.x3, term.y3, term.t3, term.x4, term.y4, term.t4, term.x5, term.y5, term.t5, term.x6, term.y6, term.t6, term.x7, term.y7, x))]
    print(term)
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
