from utils import memoisemethod
import random
from formula import impl, conj, disj, negation, variable, forall, exists, function_symbol, application, atomic, equality
from formula import _Implication, _Conjunction, _Disjunction, _Forall, _Exists


def interesting_formula(f):
    if isinstance(f, _Disjunction):
        return False
    return interesting_subformula(f)

def interesting_subformula(f):
    if isinstance(f, (_Implication, _Conjunction, _Disjunction)):
        return interesting_subformula(f.a) and interesting_subformula(f.b)
    if isinstance(f, (_Forall, _Exists)):
        return f.v in f.p.free_vars() and interesting_subformula(f.p)
    return True

def close_formula(f):
    for v in f.free_vars():
        f = forall(v, f)
    return f

def generate_formulas(*, md, n, fg=None):
    if fg is None:
        fg = FormulaGenerator()
    fs = []
    while len(fs) < n:
        f = fg.rand_f_lt(md)
        if interesting_formula(f):
            fs.append(close_formula(f))
    return fs

class FormulaGenerator:
    def __init__(self, **kwds):
        self.propositions = []
        self.quantifiers = [forall, exists]
        self.variables = [variable('x'), variable('y')]
        self.constants = [application(function_symbol('0', 0), ())]
        self.function_symbols = [function_symbol('S', 1)]
        self.predicate_symbols = []
        self.unary_connectives = [negation]
        self.binary_connectives = [impl, conj, disj]

        # override the above defaults
        for k, v in kwds.items():
            setattr(self, k, v)

        self.base_terms = self.variables + self.constants

    def random_t_depth(self, d):
        '''A weighted random depth less than d'''
        weights = [self.t_eq(n) for n in range(d)]
        return random.choices(population=range(d), weights=weights, k=1)[0]

    def random_f_depth(self, d):
        '''A weighted random depth less than d'''
        weights = [self.f_eq(n) for n in range(d)]
        return random.choices(population=range(d), weights=weights, k=1)[0]

    def rand_f_lt(self, d):
        '''A random formula of depth less than d'''
        return self.rand_f_eq(self.random_f_depth(d))

    def rand_f_eq(self, d):
        '''A random formula of exactly depth d'''
        if d == 0:
            return random.choice(self.propositions)
        pop_weights = ([self.pred_eq(d, ps) for ps in self.predicate_symbols] +
                       [self.bin_eq(d, bc) for bc in self.binary_connectives] +
                       [self.un_eq(d, uc) for uc in self.unary_connectives] +
                       [self.quant_eq(d, q) for q in self.quantifiers] +
                       [self.equ_eq(d)])
        p = random.choices(population=[p for p, w in pop_weights],
                           weights=[w for p, w in pop_weights],
                           k=1)[0]
        return p()

    def rand_t_lt(self, d):
        '''A random term of depth less than d'''
        return self.rand_t_eq(self.random_t_depth(d))

    def rand_t_eq(self, d):
        '''A random term of exactly depth d'''
        if d == 0:
            return random.choice(self.base_terms)
        weights = [self.weight((d, fs.arity)) for fs in self.function_symbols]
        fs = random.choices(population=self.function_symbols,
                            weights=weights,
                            k=1)[0]
        while True:
            args = random.choices(population=['lt', 'eq'],
                                  weights=[self.t_lt(d - 1), self.t_eq(d - 1)],
                                  k=fs.arity)
            if any(x == 'eq' for x in args):
                break
        return application(fs, tuple(self.rand_t_eq(d - 1) if x == 'eq' else self.rand_t_lt(d - 1)
                                     for x in args))

    def rand_pred_eq(self, d, ps):
        while True:
            args = random.choices(population=['lt', 'eq'],
                                  weights=[self.t_lt(d - 1), self.t_eq(d - 1)],
                                  k=ps.arity)
            if any(x == 'eq' for x in args):
                break
        return atomic(ps, tuple(self.rand_t_eq(d - 1) if x == 'eq' else self.rand_t_lt(d - 1)
                                for x in args))

    def rand_bin_eq(self, d, bc):
        while True:
            args = random.choices(population=['lt', 'eq'],
                                  weights=[self.f_lt(d - 1), self.f_eq(d - 1)],
                                  k=2)
            if any(x == 'eq' for x in args):
                break
        params = [self.rand_f_eq(d - 1) if x == 'eq' else self.rand_f_lt(d - 1) for x in args]
        # This is for 'nodups' later
        # while True:
        #     params = [self.rand_f_eq(d - 1) if x == 'eq' else self.rand_f_lt(d - 1) for x in args]
        #     if params[0] is not params[1]:
        #         break
        return bc(*params)

    def rand_un_eq(self, d, uc):
        return uc(self.rand_f_eq(d - 1))

    def rand_quant_eq(self, d, q):
        return q(random.choice(self.variables), self.rand_f_eq(d - 1))

    def rand_equ_eq(self, d):
        while True:
            args = random.choices(population=['lt', 'eq'],
                                  weights=[self.t_lt(d - 1), self.t_eq(d - 1)],
                                  k=2)
            if any(x == 'eq' for x in args):
                break
        params = [self.rand_t_eq(d - 1) if x == 'eq' else self.rand_t_lt(d - 1) for x in args]
        return equality(*params)

    def pred_eq(self, d, ps):
        return (lambda: self.rand_pred_eq(d, ps)), self.weight((d, ps.arity))

    def bin_eq(self, d, bc):
        return (lambda: self.rand_bin_eq(d, bc)), self.f_eq(d - 1) ** 2 + 2 * self.f_eq(d - 1) * self.f_lt(d - 1)

    def un_eq(self, d, uc):
        return (lambda: self.rand_un_eq(d, uc)), self.f_eq(d - 1)

    def quant_eq(self, d, q):
        return (lambda: self.rand_quant_eq(d, q)), len(self.variables) * self.f_eq(d - 1)

    def equ_eq(self, d):
        return (lambda: self.rand_equ_eq(d)), self.t_eq(d - 1) ** 2 + 2 * self.t_eq(d - 1) * self.t_lt(d - 1)

    @memoisemethod
    def weight(self, pair):
        '''The number of terms of depth d for an application of arity d

        Equivalently, the number of formulae of depth d for an atomic formula
        of arity d.
        '''
        d, arity = pair
        return (self.t_eq(d - 1) + self.t_lt(d - 1)) ** arity - self.t_lt(d - 1) ** arity

    @memoisemethod
    def t_eq(self, x):
        '''The number of terms of exactly depth x'''
        if x == 0:
            return len(self.variables) + len(self.constants)
        k = [self.weight((x, sym.arity)) for sym in self.function_symbols]
        return sum(k)

    @memoisemethod
    def t_lt(self, x):
        '''The number of terms of depth less than x'''
        return sum(self.t_eq(i) for i in range(x))

    @memoisemethod
    def f_eq(self, x):
        '''The number of formulae of exactly depth x'''
        if x == 0:
            return len(self.propositions)
        num_pred_forms = sum([self.weight((x, sym.arity)) for sym in self.predicate_symbols])
        num_bin_forms = len(self.binary_connectives) * (self.f_eq(x - 1)**2 + 2 * self.f_eq(x - 1) * self.f_lt(x - 1))
        num_un_forms = len(self.unary_connectives) * (self.f_eq(x - 1))
        num_quant_forms = len(self.quantifiers) * len(self.variables) * (self.f_eq(x - 1))
        num_equ_forms = self.weight((x, 2))
        # print(num_pred_forms, num_bin_forms, num_un_forms, num_quant_forms, num_equ_forms)
        return num_pred_forms + num_bin_forms + num_un_forms + num_quant_forms + num_equ_forms

    @memoisemethod
    def f_lt(self, x):
        '''The number of formulae of depth less than x'''
        return sum(self.f_eq(i) for i in range(x))
