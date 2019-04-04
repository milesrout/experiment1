import _thread
import contextlib
import functools
import random
import signal
import threading
import time


class TimeLimit(BaseException):
    @staticmethod
    def throw():
        raise TimeLimit


@contextlib.contextmanager
def timelimit(limit=1):
    t = threading.Timer(limit / 1000, _thread.interrupt_main)
    h = signal.signal(signal.SIGINT, lambda sig, frame: TimeLimit.throw())
    t.start()
    yield
    t.cancel()
    signal.signal(signal.SIGINT, h)


@contextlib.contextmanager
def timelimit_soft(limit=1):
    global start_time
    if limit == 0:
        start_time = None
    else:
        start_time = time.perf_counter() + (limit / 1000)
    yield


def check_timelimit():
    if start_time is None:
        return
    if time.perf_counter() > start_time:
        raise TimeLimit


def frozen(x):
    return x
    a, b = x
    if isinstance(b, list):
        b = tuple(b)
    if isinstance(a, set):
        a = frozenset(a)
    return a, b


def memoisemethod(f):
    @functools.wraps(f)
    def wrapper(self, o):
        if not hasattr(self, '_memory'):
            setattr(self, '_memory', {})
        memory = self._memory[f] = self._memory.get(f, {})
        if frozen(o) not in memory:
            memory[frozen(o)] = f(self, o)
        return memory[frozen(o)]
    return wrapper


def memoise(f):
    memory = {}

    @functools.wraps(f)
    def wrapper(o):
        if frozen(o) not in memory:
            memory[frozen(o)] = f(o)
        return memory[frozen(o)]
    return wrapper


def compose(f):
    def outer(g):
        @functools.wraps(g)
        def inner(*args, **kwds):
            return f(g(*args, **kwds))
        return inner
    return outer


def overload():
    def decorator(f):
        registry = {}

        @functools.wraps(f)
        def overloaded(x, *args, **kwds):
            def do_overload():
                for k, v in registry.items():
                    if isinstance(x, k):
                        return v(x, *args, **kwds)
                raise TypeError('no overload found for {}'.format(
                    x.__class__.__qualname__))

            r = do_overload()
            return r

        def on(t):
            def register(g):
                if registry.get(t) is None:
                    registry[t] = g
                else:
                    raise ValueError('can\'t overload on the same type twice')
            return register

        overloaded.on = on
        return overloaded
    return decorator


def nearby(x, a=0, b=1, alpha=20):
    """Returns a value near x within the range [a,b]

    alpha - higher means nearer x
    """
    v = (x - a) / (b - a)
    return a + (b - a) * random.betavariate(alpha, alpha * ((1 / v) - 1))
