from abc import ABCMeta, abstractmethod
from collections import namedtuple

class formula(metaclass=ABCMeta):
    def __gt__(self, other):
        return impl(self, other)

    def __or__(self, other):
        return disj(self, other)

    def __and__(self, other):
        return conj(self, other)

    def __invert__(self):
        return impl(self, bot)

    # @abstractmethod
    # def subformulae(self):
    #     ...

    # @abstractmethod
    # def depth(self):
    #     ...

    @abstractmethod
    def free_vars(self):
        raise NotImplementedError(repr(self.__class__))

    @abstractmethod
    def subst(self, var, term):
        raise NotImplementedError(repr(self.__class__))

    @abstractmethod
    def __hash__(self):
        raise NotImplementedError(repr(self.__class__))

def raise_arity(expected, actual):
    raise TypeError(f'too many arguments: expected {expected}, got {actual}')

# This can be applied only to classes that are subclasses of namedtuples
def deduplicate(cls):

    # Store the instances by their arguments
    instances = dict()

    def __new__(cls, *args, **kwds):
        # kwds.items() is a dictionary, which cannot be hashed because it is
        # mutable, so as a result we have to turn it into an immutable type
        # like a tuple if we want to use it as a key.
        key = (args, tuple(kwds.items()))
        if key not in instances:
            # get the namedtuple base class of cls, so that we call the right
            # __new__ method, otherwise we get an error that it is unsafe to
            # call object.__new__ and need to use tuple.__new__.
            base = next(b for b in cls.__bases__ if tuple in b.__bases__)
            obj = base.__new__(cls, *args, **kwds)
            instances[key] = obj
        return instances[key]

    cls.__new__ = __new__

    return cls

class term(metaclass=ABCMeta):
    def __add__(self, other):
        if type(other) is not int:
            raise NotImplementedError
        for i in range(other):
            self = s(self)
        return self

    @abstractmethod
    def free_vars(self):
        raise NotImplementedError(repr(self.__class__))

    @abstractmethod
    def subst(self, var, term):
        raise NotImplementedError(repr(self.__class__))

    @abstractmethod
    def __hash__(self):
        raise NotImplementedError(repr(self.__class__))

_FunctionSymbol = namedtuple('_FunctionSymbol', 'name arity')

_PredicateSymbol = namedtuple('_PredicateSymbol', 'name arity')

# Terms
_Variable = namedtuple('_Variable', 'name')

_Application = namedtuple('_Application', 'fsym ts')

# Formulas
_Atomic = namedtuple('_Atomic', 'psym ts')

_Equality = namedtuple('_Equality', 't1 t2')

_Negation = namedtuple('_Negation', 'p')

_Conjunction = namedtuple('_Conjunction', 'a b')

_Disjunction = namedtuple('_Disjunction', 'a b')

_Implication = namedtuple('_Implication', 'a b')

_Forall = namedtuple('_Forall', 'v p')

_Exists = namedtuple('_Exists', 'v p')

@deduplicate
class function_symbol(_FunctionSymbol):
    def __str__(self):
        return self.name

    def __hash__(self):
        return hash((function_symbol, self.name))

@deduplicate
class predicate_symbol(_PredicateSymbol):
    def __str__(self):
        return self.name

    def __hash__(self):
        return hash((predicate_symbol, self.name))

@deduplicate
class variable(term, _Variable):
    def __str__(self):
        return self.name

    def __hash__(self):
        return hash((variable, self.name))

    def subst(self, var, term):
        if var == self:
            return term
        return self

    def free_vars(self):
        return {self}

@deduplicate
class application(term, _Application):
    def __str__(self):
        return str(self.fsym) + ''.join(str(t) for t in self.ts)

    def free_vars(self):
        if len(self.ts) == 0:
            return set()
        return set.union(*[t.free_vars() for t in self.ts])

    def subst(self, var, term):
        return application(self.fsym, tuple(t.subst(var, term) for t in self.ts))

    def __hash__(self):
        return hash((application, self.fsym, self.ts))

@deduplicate
class atomic(formula, _Atomic):
    def __str__(self):
        if self.psym.arity == 2:
            return f'({self.ts[0]} {self.psym} {self.ts[1]})'
        return str(self.psym) + ''.join(str(t) for t in self.ts)

    def free_vars(self):
        if len(self.ts) == 0:
            return set()
        return set.union(*[t.free_vars() for t in self.ts])

    def subst(self, var, term):
        return atomic(self.psym, tuple(t.subst(var, term) for t in self.ts))

    def __hash__(self):
        return hash((atomic, self.psym, self.ts))

@deduplicate
class equality(formula, _Equality):
    def __str__(self):
        return f'({self.t1} = {self.t2})'

    def free_vars(self):
        return self.t1.free_vars() | self.t2.free_vars()

    def subst(self, var, term):
        return equality(self.t1.subst(var, term), self.t2.subst(var, term))

    def __hash__(self):
        return hash((equality, self.t1, self.t2))

# @deduplicate
# class negation(formula, _Negation):
#     def __str__(self):
#         return f'¬{self.p}'
#
#     def free_vars(self):
#         return self.p.free_vars()
#
#     def __hash__(self):
#         return hash((negation, self.p))

def negation(p):
    return impl(p, bot)

@deduplicate
class forall(formula, _Forall):
    def __str__(self):
        return f'∀{self.v}.{self.p}'

    def free_vars(self):
        return self.p.free_vars() - {self.v}

    def subst(self, var, term):
        if self.v == var:
            return self
        return forall(self.v, self.p.subst(var, term))

    def __hash__(self):
        return hash((forall, self.v, self.p))

    def instantiate(self, v):
        return self.p.subst(self.v, v)

@deduplicate
class exists(formula, _Exists):
    def __str__(self):
        return f'∃{self.v}.{self.p}'

    def free_vars(self):
        return self.p.free_vars() - {self.v}

    def subst(self, var, term):
        if self.v == var:
            return self
        return exists(self.v, self.p.subst(var, term))

    def __hash__(self):
        return hash((exists, self.v, self.p))

    def instantiate(self, v):
        return self.p.subst(self.v, v)

def proposition(p):
    return atomic(predicate_symbol(p, 0), ())

bot = proposition('⊥')

ZERO = function_symbol('0', 0)
SUCC = function_symbol('S', 1)

zero = application(ZERO, ())

def succ(x):
    return application(SUCC, (x,))

# class propositional_atomic(formula):
#    def __new__(cls, a):
#        if a not in cls.store:
#            cls.store[a] = super().__new__(cls)
#        return cls.store[a]
#
#    def __getnewargs__(self):
#        return (self.a,)
#
#    def __init__(self, a):
#        self.a = a
#
#    @property
#    def depth(self):
#        return 1
#
#    def __str__(self):
#        return self.a
#
#    def __repr__(self):
#        return f'atomic({self.a!r})'
#
#    def subformulae(self):
#        return {self}
#
#    def free_vars(self):
#        return {self}
#
#    def subst(self, subst):
#        if self in subst:
#            return subst[self]
#        else:
#            return self

@deduplicate
class impl(formula, _Implication):
    def __str__(self):
        if self.b is bot and self.a is not bot:
            return f'¬{self.a}'
        return f'({self.a} → {self.b})'

    def __repr__(self):
        return f'impl({self.a!r}, {self.b!r})'

    def free_vars(self):
        return self.a.free_vars() | self.b.free_vars()

    def subst(self, var, term):
        return impl(self.a.subst(var, term), self.b.subst(var, term))

    def __hash__(self):
        return hash((impl, self.a, self.b))


@deduplicate
class disj(formula, _Disjunction):
    def __str__(self):
        return f'({self.a} ∨ {self.b})'

    def __repr__(self):
        return f'disj({self.a!r}, {self.b!r})'

    def free_vars(self):
        return self.a.free_vars() | self.b.free_vars()

    def subst(self, var, term):
        return disj(self.a.subst(var, term), self.b.subst(var, term))

    def __hash__(self):
        return hash((disj, self.a, self.b))


@deduplicate
class conj(formula, _Conjunction):
    def __str__(self):
        return f'({self.a} ∧ {self.b})'

    def __repr__(self):
        return f'conj({self.a!r}, {self.b!r})'

    def free_vars(self):
        return self.a.free_vars() | self.b.free_vars()

    def subst(self, var, term):
        return conj(self.a.subst(var, term), self.b.subst(var, term))

    def __hash__(self):
        return hash((conj, self.a, self.b))


if __name__ == '__main__':
    a = atomic('A')
    b = atomic('B')
    c = atomic('C')
    print(a | ~a)
    print(a > a | b)
    print(a & b > a)
    print(a | b & c)
