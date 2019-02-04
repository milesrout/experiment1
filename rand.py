import formula
import random


def iterate(f, n, variables=2, connectives=3):
    xs = [variables]
    for i in range(1, n):
        xs.append(connectives * f(xs))
    return xs


def random_depth(maxdepth, *, samples=1, variables=2, connectives=3):
    return random.choices(population=range(maxdepth),
                          weights=iterate(f, maxdepth, variables, connectives),
                          k=samples)


def f(x):
    return x[-1] * (2 * sum(x) - x[-1])


def rand_lt_depth(depth, variables, connectives):
    if depth == 0:
        return formula.atomic(random.choice(variables))

    c, v = len(connectives), len(variables)
    d = random_depth(depth, samples=1, variables=v, connectives=c)[-1]
    return rand_eq_depth(d, variables, connectives)


def rand_eq_depth(depth, variables, connectives):
    if depth == 0:
        return formula.atomic(random.choice(variables))

    conn = random.choice(connectives)

    if depth == 1:
        return conn(rand_eq_depth(0, variables, connectives),
                    rand_eq_depth(0, variables, connectives))

    c, v = len(connectives), len(variables)
    a = iterate(f, depth, v, c)[-1]
    b = sum(iterate(f, depth - 1, v, c))

    k = random.randrange(a + b + b)
    if k < a:
        return conn(rand_eq_depth(depth - 1, variables, connectives),
                    rand_eq_depth(depth - 1, variables, connectives))
    elif k < a + b:
        return conn(rand_lt_depth(depth - 1, variables, connectives),
                    rand_eq_depth(depth - 1, variables, connectives))
    else:
        return conn(rand_eq_depth(depth - 1, variables, connectives),
                    rand_lt_depth(depth - 1, variables, connectives))
