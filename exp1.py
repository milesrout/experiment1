import collections
import functools
import itertools
import math
import rand
import random

from formula import atomic, impl


POPSIZE = 20
PROB_MUTATION = 0.2
PROB_CROSSOVER = 0.5
ADD_OR_REMOVE_FACTOR = 1 - 1/math.sqrt(2)
depths = collections.Counter()


def shuffled(pop):
    return random.sample(pop, len(pop))


def compose(f):
    def outer(g):
        @functools.wraps(g)
        def inner(*args, **kwds):
            return f(g(*args, **kwds))
        return inner
    return outer


class Premise:
    def __init__(self, formula):
        self.formula = formula
        self.conclusion = formula
        self.dependencies = set()

    def __repr__(self):
        return f'P:{self.formula}'


class Substitution:
    def __init__(self, original, subst):
        self.original = original
        self.subst = subst
        self.conclusion = original.conclusion.subst(subst)
        self.dependencies = {original}

    def __repr__(self):
        if isinstance(self.original, Premise):
            return f'{self.original}|SUB:{self.conclusion}'
        else:
            return f'SUB:{self.conclusion}'


class ModusPonens:
    def __init__(self, atob, a):
        self.atob = atob
        self.a = a

    @property
    def conclusion(self):
        return self.atob.conclusion.b

    @property
    def dependencies(self):
        return {self.atob, self.a}

    def __repr__(self):
        if isinstance(self.atob, Premise) and isinstance(self.a, Premise):
            return f'{self.atob}|{self.a}|MP:{self.conclusion}'
        elif isinstance(self.atob, Premise):
            return f'{self.atob}|MP:{self.conclusion}'
        elif isinstance(self.a, Premise):
            return f'{self.a}|MP:{self.conclusion}'
        else:
            return f'MP:{self.conclusion}'


class Proof1:
    def __init__(self, goal, premises, steps):
        self.goal = goal
        self.premises = premises
        self.steps = steps

    def __str__(self):
        return '(' + '|'.join(str(x) for x in self.steps) + ')'

    def __repr__(self):
        return str(self)
        return f'Proof1({self.goal}, {self.premises}, {self.steps})'

    @staticmethod
    def crossover(left, right):
        return (left, right)

    def mutate(self):
        # remove an unused step, or add a new step,
        # or replace a step with a new one
        if len(self.steps) == 0:
            return self.add_random_step()

        if random.random() < ADD_OR_REMOVE_FACTOR:
            return self.add_random_step()
        elif random.random() < ADD_OR_REMOVE_FACTOR:
            return self.remove_unused_step()
        else:
            return self.remove_unused_step().add_random_step()

    def add_random_step(self):
        steps = list(self.steps)
        step = self.random_step()
        if step is not None:
            steps.append(step)
        return Proof1(self.goal, self.premises, steps).remove_duplicates()

    def remove_unused_step(self):
        used_steps = set()
        for step in self.steps:
            used_steps |= step.dependencies
            # it's not a useless step if it results in the goal!
            if step.conclusion == self.goal:
                used_steps.add(step)
        # the final step is never useless
        used_steps.add(self.steps[-1])
        unused_steps = dict((x, i) for (i, x) in enumerate(self.steps))
        for x in used_steps:
            if x in unused_steps:
                del unused_steps[x]
        if len(unused_steps.values()) == 0:
            return self
        idx = random.choice(list(unused_steps.values()))

        steps = list(self.steps)
        steps.pop(idx)
        return Proof1(self.goal, self.premises, steps)

    def random_step(self):
        return random.choice([self.random_modusponens,
                              self.random_substitution])()

    def all_vars(self):
        xs = [step.conclusion.free_vars() for step in self.steps]
        ys = [premise.conclusion.free_vars() for premise in self.premises]
        zs = self.goal.free_vars()
        return [x.a for x in set.union(*xs, *ys, zs)]

    def random_substitution(self):
        step = random.choice(self.premises)
        subst = {}
        for x in step.conclusion.free_vars():
            depth = math.floor(random.expovariate(1.5))
            depths[depth] += 1
            subst[x] = rand.rand_eq_depth(
                depth, variables=self.all_vars(), connectives=[impl])
        return Substitution(step, subst)

    def random_modusponens(self):
        for atob in shuffled(self.premises + self.steps):
            if isinstance(atob.conclusion, impl):
                options = [x for x in self.premises + self.steps
                           if x.conclusion == atob.conclusion.a]
                if len(options) == 0:
                    continue
                a = random.choice(options)
                return ModusPonens(atob, a)
        return None

    def _remove_duplicates(self):
        seen_steps = set()
        for step in self.steps:
            if step.conclusion not in seen_steps:
                seen_steps.add(step.conclusion)
                yield step

    def remove_duplicates(self):
        return Proof1(self.goal, self.premises,
                      list(self._remove_duplicates()))

    def apply(self, goal, premises):
        for premise in self.premises:
            if premise.conclusion == goal:
                return True
        for step in self.steps:
            if step.conclusion == goal:
                return True
        return False

    @staticmethod
    def fitness(goal, premises):
        def evaluate(proof):
            if proof.apply(goal, premises):
                return 1000
            else:
                return 0.1
        return evaluate


pA = atomic('A')
pB = atomic('B')
pC = atomic('C')


def main():
    # goal = ~pA > (pA > ~pA)
    goal = (~pA > (pA > ~pA)) > (~(pA > ~pA) > ~~pA)
    # goal = (~~pA > pA) > (~(pA > ~pA) > pA)
    # goal = (~~pA > pA) > (~(pA > ~pA) > pA)
    premises = [
        Premise(pA > (pB > pA)),
        Premise((pA > pB) > ((pB > pC) > (pA > pC))),
    ]
    lastgen = None
    newgen = [Proof1(goal, premises, []) for i in range(POPSIZE)]
    print(f'{", ".join(map(str, premises))} |- {goal}')
    for generation in itertools.count():
        lastgen, newgen = newgen, []

        for i, indiv in enumerate(lastgen):
            if random.random() < PROB_CROSSOVER:
                idx = random.randrange(len(lastgen))
                new1, new2 = Proof1.crossover(indiv, lastgen[idx])
                newgen.append(new1)
                newgen.append(new2)
            else:
                newgen.append(indiv)

        for i, indiv in enumerate(newgen):
            if random.random() < PROB_MUTATION:
                newgen[i] = indiv.mutate()

        # print('Before pruning:')
        # print(newgen)

        for x in newgen:
            if x.apply(goal, premises):
                print('\n\nPROOF FOUND')
                print(x)
                print('\n\nWITH USELESS STEPS REMOVED')
                y = x
                while x is y:
                    y = x.remove_unused_step()
                    x, y = y, x
                print(x)
                return

        # STRICT ELITISM
        # newgen.sort(key=Proof1.fitness(goal, premises), reverse=True)
        # newgen = newgen[:POPSIZE]

        # WEIGHTED ELITISM
        weights = map(Proof1.fitness(goal, premises), newgen)
        newgen = random.choices(newgen, weights, k=POPSIZE)

        # print('After pruning:')
        if generation % 3000 == 0:
            print(f'Generation {generation}:')
            print(newgen)

        # print(depths)


if __name__ == '__main__':
    main()
