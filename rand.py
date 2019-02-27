import random


def iterate(f, n, variables=2, connectives=3):
    xs = [variables]
    for i in range(1, n):
        xs.append(connectives * f(xs))
    return xs


def choose_formula(formulae):
    return random.choices(population=formulae,
                          weights=[1 / f.depth**2 for f in formulae],
                          k=1)[0]


def random_depth(maxdepth, *, samples=1, num_variables=2, num_connectives=3):
    weights = iterate(f, maxdepth, num_variables, num_connectives)
    return random.choices(population=range(maxdepth),
                          weights=weights,
                          k=samples)


def f(x):
    return x[-1] * (2 * sum(x) - x[-1])


def rand_lt_depth(depth, base_formulae, connectives):
    if depth == 0:
        # return formula.atomic(random.choice(variables))
        return choose_formula(base_formulae)

    c, v = len(connectives), len(base_formulae)
    d = random_depth(depth, samples=1, num_variables=v, num_connectives=c)[-1]
    return rand_eq_depth(d, base_formulae, connectives)


def rand_lt_depth_nodups(depth, base_formulae, connectives):
    if depth == 0:
        # return formula.atomic(random.choice(variables))
        return choose_formula(base_formulae)

    c, v = len(connectives), len(base_formulae)
    d = random_depth(depth, samples=1, num_variables=v, num_connectives=c)[-1]
    return rand_eq_depth_nodups(d, base_formulae, connectives)


def rand_eq_depth(depth, base_formulae, connectives):
    if depth == 0:
        return choose_formula(base_formulae)

    conn = random.choice(connectives)

    if depth == 1:
        return conn(rand_eq_depth(0, base_formulae, connectives),
                    rand_eq_depth(0, base_formulae, connectives))

    c, v = len(connectives), len(base_formulae)
    a = iterate(f, depth, v, c)[-1]
    b = sum(iterate(f, depth - 1, v, c))

    k = random.randrange(a + b + b)
    if k < a:
        return conn(rand_eq_depth(depth - 1, base_formulae, connectives),
                    rand_eq_depth(depth - 1, base_formulae, connectives))
    elif k < a + b:
        return conn(rand_lt_depth(depth - 1, base_formulae, connectives),
                    rand_eq_depth(depth - 1, base_formulae, connectives))
    else:
        return conn(rand_eq_depth(depth - 1, base_formulae, connectives),
                    rand_lt_depth(depth - 1, base_formulae, connectives))


def rand_eq_depth_nodups(depth, base_formulae, connectives):
    if depth == 0:
        return choose_formula(base_formulae)

    conn = random.choice(connectives)

    if depth == 1:
        form1 = form2 = rand_eq_depth_nodups(0, base_formulae, connectives)
        while form2 == form1:
            form2 = rand_eq_depth_nodups(0, base_formulae, connectives)
        return conn(form1, form2)

    c, v = len(connectives), len(base_formulae)
    a = iterate(f, depth, v, c)[-1]
    b = sum(iterate(f, depth - 1, v, c))

    k = random.randrange(a + b + b)
    if k < a:
        form1 = form2 = rand_eq_depth_nodups(depth - 1, base_formulae, connectives)
        while form2 == form1:
            form2 = rand_eq_depth_nodups(depth - 1, base_formulae, connectives)
        return conn(form1, form2)
    elif k < a + b:
        return conn(rand_lt_depth_nodups(depth - 1, base_formulae, connectives),
                    rand_eq_depth_nodups(depth - 1, base_formulae, connectives))
    else:
        return conn(rand_eq_depth_nodups(depth - 1, base_formulae, connectives),
                    rand_lt_depth_nodups(depth - 1, base_formulae, connectives))
