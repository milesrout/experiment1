import functools
import random
import unicodedata

from formula import atomic, impl


POPSIZE = 20
PROB_MUTATION = 0.2
PROB_CROSSOVER = 0.5
ADD_OR_REMOVE_FACTOR = 0.5


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
    def __init__(self, premises, steps):
        self.premises = premises
        self.steps = steps

    def __str__(self):
        return '(' + '|'.join(str(x) for x in self.steps) + ')'

    def __repr__(self):
        return str(self)
        return f'Proof1({self.premises}, {self.steps})'

    @staticmethod
    def crossover(left, right):
        return (left, right)

    def mutate(self):
        # remove an unused step, or add a new step
        if len(self.steps) == 0 or random.random() < ADD_OR_REMOVE_FACTOR:
            return self.add_random_step()
        return self.remove_unused_step()

    def add_random_step(self):
        steps = list(self.steps)
        steps.append(self.random_step())
        return Proof1(self.premises, steps).remove_duplicates()

    def remove_unused_step(self):
        used_steps = set()
        for step in self.steps:
            used_steps |= step.dependencies
        unused_steps = dict((x, i) for (i, x) in enumerate(self.steps))
        for x in used_steps:
            if x in unused_steps:
                del unused_steps[x]
        idx = random.choice(list(unused_steps.values()))

        steps = list(self.steps)
        steps.pop(idx)
        return Proof1(self.premises, steps)

    def random_step(self):
        return random.choice([self.random_modusponens])()

    def random_modusponens(self):
        for atob in shuffled(self.premises + self.steps):
            if isinstance(atob.conclusion, impl):
                options = [x for x in self.premises + self.steps
                           if x.conclusion == atob.conclusion.a]
                if len(options) == 0:
                    continue
                a = random.choice(options)
                return ModusPonens(atob, a)
        raise RuntimeError('What should I do here?')

    def _remove_duplicates(self):
        seen_steps = set()
        for step in self.steps:
            if step.conclusion not in seen_steps:
                seen_steps.add(step.conclusion)
                yield step

    def remove_duplicates(self):
        return Proof1(self.premises, list(self._remove_duplicates()))

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
                return 0.5 + 0.5 / len(proof.steps)
            else:
                return 0.5 - (0.5 / (len(proof.steps) + 1))
        return evaluate


pA = atomic('A')
pB = atomic('B')
pC = atomic('C')


def main():
    goal = pC
    premises = [
        Premise(pA > pB),
        Premise(pA > (pB > pC)),
        Premise(pB > pC),
        Premise(pA)
    ]
    lastgen, newgen = None, [Proof1(premises, []) for i in range(POPSIZE)]
    print(f'{", ".join(map(str, premises))} |- {goal}')
    for i in range(10000):
        print(f'Generation {i+1}:')
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

        print('Before pruning:')
        print(newgen)

        newgen.sort(key=Proof1.fitness(goal, premises), reverse=True)
        newgen = newgen[:POPSIZE]

        for x in newgen:
            if x.apply(goal, premises):
                print('\n\nPROOF FOUND')
                print(x)
                return

        print('After pruning:')
        print(newgen)


if __name__ == '__main__':
    main()
