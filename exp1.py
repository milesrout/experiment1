import collections
import functools
import itertools
import math
import rand
import random
import unicodedata

from formula import atomic, impl


POPSIZE = 20
PROB_MUTATION = 0.2
PROB_CROSSOVER = 0.5
ADD_OR_REMOVE_FACTOR = 0.99
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

    def subst_dep(self, old):
        return self

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

    def subst_dep(self, old):
        original = old.get(self.original.conclusion,
                           self.original.subst_dep(old))
        if original is self.original:
            return self
        return Substitution(original, self.subst)


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

    def subst_dep(self, old):
        atob = old.get(self.atob.conclusion, self.atob.subst_dep(old))
        a = old.get(self.a.conclusion, self.a.subst_dep(old))
        if atob is self.atob and a is self.a:
            return self
        return ModusPonens(atob, a)

    def __repr__(self):
        if isinstance(self.atob, Premise) and isinstance(self.a, Premise):
            return f'{self.atob}|{self.a}|MP:{self.conclusion}'
        elif isinstance(self.atob, Premise):
            return f'{self.atob}|MP:{self.conclusion}'
        elif isinstance(self.a, Premise):
            return f'{self.a}|MP:{self.conclusion}'
        else:
            return f'MP:{self.conclusion}'


class Proof:
    def __init__(self, goal, premises, steps):
        self.goal = goal
        self.premises = premises
        self.steps = steps

    def __str__(self):
        return '(' + '|'.join(str(x) for x in self.steps) + ')'

    def __repr__(self):
        return str(self)
        return f'Proof({self.goal}, {self.premises}, {self.steps})'

    @staticmethod
    def crossover(left, right):
        # select an unused step from each
        stepL = left.get_unused_step()
        stepR = right.get_unused_step()
        if stepL is not None and stepR is not None:
            right = right.add_new_step(stepL).remove_step(stepR)
            left = left.add_new_step(stepR).remove_step(stepL)
        return (left, right)

    def mutate(self):
        # remove an unused step, or add a new step,
        # or replace a step with a new one
        if len(self.steps) == 0:
            return self.add_random_step()

        if random.random() < ADD_OR_REMOVE_FACTOR:
            return self.add_random_step()
        elif random.random() > ADD_OR_REMOVE_FACTOR:
            return self.remove_unused_step()
        else:
            return self.remove_unused_step().add_random_step()

    def add_random_step(self):
        steps = list(self.steps)
        step = self.random_step()
        if step is not None:
            steps.append(step)
        return Proof(self.goal, self.premises, steps).remove_duplicates()

    def add_new_step(self, new_step):
        new = new_step.subst_dep({s.conclusion: s for s in self.steps})
        steps = set(self.steps)
        new_steps = set()
        for dep in new.dependencies:
            if dep not in steps and not isinstance(dep, Premise):
                new_steps.add(dep)
        return Proof(self.goal, self.premises,
                     self.steps + list(new_steps) + [new])

    def remove_step(self, step):
        return Proof(self.goal, self.premises,
                     [s for s in self.steps if s != step])

    def get_unused_step(self):
        steps = self.get_unused_steps()
        if len(steps) == 0:
            return None
        return self.steps[random.choice(list(steps))]

    def get_unused_steps(self):
        used_steps = set()
        for step in self.steps:
            used_steps |= step.dependencies
        unused_steps = dict((x, i) for (i, x) in enumerate(self.steps))
        for x in used_steps:
            if x in unused_steps:
                del unused_steps[x]
        return unused_steps.values()

    def remove_unused_step(self):
        # it's not a useless step if it results in the goal!
        # also, the final step is never useless.
        unused_steps = {x for x in self.get_unused_steps()
                        if self.steps[x].conclusion != self.goal
                        and x != len(self.steps) - 1}
        if len(unused_steps) == 0:
            return self
        idx = random.choice(list(unused_steps))

        steps = list(self.steps)
        steps.pop(idx)
        return Proof(self.goal, self.premises, steps)

    def random_step(self):
        step = self.random_modusponens()
        if step is not None:
            return step
        return self.random_substitution()
        # return random.choice([self.random_substitution])()

    def all_vars(self):
        xs = [step.conclusion.free_vars() for step in self.steps]
        ys = [premise.conclusion.free_vars() for premise in self.premises]
        zs = self.goal.free_vars()
        return [x.a for x in set.union(*xs, *ys, zs)]

    def all_subformulae(self):
        ss = [step.conclusion.subformulae() for step in self.steps]
        gs = self.goal.subformulae()
        return list(set.union(*ss, gs))

    def random_substitution(self):
        step = random.choice(self.premises)
        all_subformulae = self.all_subformulae()
        subst = {}
        for x in step.conclusion.free_vars():
            depth = math.floor(random.expovariate(1.5))
            depths[depth] += 1
            subst[x] = rand.rand_eq_depth(
                depth, base_formulae=all_subformulae, connectives=[impl])
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
        return Proof(self.goal, self.premises,
                     list(self._remove_duplicates()))

    def apply(self, goal, premises):
        for step in self.steps:
            if step.conclusion == goal:
                return True
        return False

    @staticmethod
    def fitness(goal, premises):
        def evaluate(proof):
            subgoals = [
                (~pA > (pA > ~pA)),
                # (~pA > pA) > (~pA > ~~pA),
                (~pA > (pA > ~pA)) > (~(pA > ~pA) > ~~pA)
            ]
            total = 1.1 - 1 / (1 + len(proof.steps))
            seen = set()
            for step in proof.steps:
                if step.conclusion in subgoals and step.conclusion not in seen:
                    seen.add(step.conclusion)
                    total += 1
                    total *= 10
            return total
        return evaluate


pA = atomic('A')

pa = atomic(unicodedata.lookup('GREEK SMALL LETTER PHI'))
pb = atomic(unicodedata.lookup('GREEK SMALL LETTER THETA'))
pc = atomic(unicodedata.lookup('GREEK SMALL LETTER PSI'))


def main():
    # goal = ~pA > (pA > ~pA)
    # goal = (~pA > pA) > (~pA > ~~pA)
    # goal = (~pA > (pA > ~pA)) > (~(pA > ~pA) > ~~pA)
    # goal = (~~pA > pA) > (~(pA > ~pA) > pA)
    goal = ~(pA > ~pA) > ~~pA
    premises = [
        Premise(pa > (pb > pa)),
        Premise((pa > (pb > pc)) > ((pa > pb) > (pa > pc))),
        Premise((pa > pb) > ((pb > pc) > (pa > pc))),
    ]
    lastgen = None
    newgen = [Proof(goal, premises, []) for i in range(POPSIZE)]
    print(f'{", ".join(map(str, premises))} |- {goal}')
    for generation in itertools.count():
        lastgen, newgen = newgen, []

        for i, indiv in enumerate(lastgen):
            if random.random() < PROB_CROSSOVER:
                idx = random.randrange(len(lastgen))
                new1, new2 = Proof.crossover(indiv, lastgen[idx])
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
                y = None
                while x is not y:
                    y = x.remove_unused_step()
                    x, y = y, x
                print(x)
                return

        # STRICT ELITISM
        # newgen.sort(key=Proof.fitness(goal, premises), reverse=True)
        # newgen = newgen[:POPSIZE]

        # WEIGHTED ELITISM
        weights = map(Proof.fitness(goal, premises), newgen)
        newgen = random.choices(newgen, weights, k=POPSIZE)

        # print('After pruning:')
        #if generation % 3000 == 0:
        if 1:
            print(f'Generation {generation}:')
            print(newgen)

        # print(depths)


if __name__ == '__main__':
    main()
