class formula:
    def __gt__(self, other):
        return impl(self, other)

    def __or__(self, other):
        return disj(self, other)

    def __and__(self, other):
        return conj(self, other)

    def __invert__(self):
        return impl(self, bot)


def raise_arity(expected, actual):
    raise TypeError(f'too many arguments: expected {expected}, got {actual}')


def operator(*, arity):
    class operator_(type):
        def __new__(cls, name, bases, dct):
            def init(self, *args):
                if len(args) != arity:
                    raise_arity(arity, len(args))
                self.data = args

            def new(cls, *args):
                if len(args) != arity:
                    raise_arity(arity, len(args))
                k = tuple(args)
                if k not in cls.store:
                    cls.store[k] = super(cls, result).__new__(cls)
                return cls.store[k]

            d = dct.copy()
            d['__new__'] = new
            d['__init__'] = init
            d['store'] = {}
            # dirty shorthand
            d['a'] = property(lambda self: self.data[0])
            d['b'] = property(lambda self: self.data[1])

            result = super().__new__(cls, name, bases, d)
            return result
    return operator_


class atomic(formula, metaclass=operator(arity=1)):
    def __str__(self):
        return self.a

    def __repr__(self):
        return f'atomic({self.a!r})'


bot = atomic('⊥')


class impl(formula, metaclass=operator(arity=2)):
    def __str__(self):
        # This is temporarily disabled
        # if self.b is bot:
        #     return f'¬{self.a}'
        return f'({self.a} → {self.b})'

    def __repr__(self):
        return f'impl({self.a!r}, {self.b!r})'


class disj(formula, metaclass=operator(arity=2)):
    def __str__(self):
        return f'({self.a} ∨ {self.b})'

    def __repr__(self):
        return f'disj({self.a!r}, {self.b!r})'


class conj(formula, metaclass=operator(arity=2)):
    def __str__(self):
        return f'({self.a} ∧ {self.b})'

    def __repr__(self):
        return f'conj({self.a!r}, {self.b!r})'


if __name__ == '__main__':
    a = atomic('A')
    b = atomic('B')
    c = atomic('C')
    print(a | ~a)
    print(a > a | b)
    print(a & b > a)
    print(a | b & c)
