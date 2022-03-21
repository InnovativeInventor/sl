#!/usr/bin/env python

from sugar import *

def test_contrapositive():
    p = Atomic("p")
    q = Atomic("q")

    left = Implies(p, q)
    right = Implies(Not(q), Not(p))

    context = ProofContext({left}, {right})
    context.solve()
    context.generate_graphviz("contrapositive", view = False)
    assert context.solve()
