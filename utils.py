import functools


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
