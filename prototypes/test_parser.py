#!/usr/bin/env python

from parser import ProofContext, Formula, Atomic, And, Or, Not, Implies

def test_formula_constructions():
    assert isinstance(Atomic(), Formula)
    assert isinstance(Not(c = Atomic()), Formula)
    assert isinstance(And(l = Atomic(), r = Atomic()), Formula)
    assert isinstance(Or(l = Atomic(), r = Atomic()), Formula)
    assert isinstance(Implies(l = Atomic(), r = Atomic()), Formula)

def test_proof_context_init():
    x = Atomic()
    ctx = ProofContext({x}, {x})
    assert ctx.closed == False


"""
Correctness tests
"""

def test_proof_identity_taut():
    """
    Proof that x |- x.
    """
    x = Atomic()
    ctx = ProofContext({x}, {x})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_proof_identity_taut_not():
    """
    Proof that (not x) |- (not x).
    """
    atom = Atomic()
    x = Not(c=atom)
    y = Not(c=atom)

    ctx = ProofContext({x}, {y})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_conjunction_elim_taut_1():
    """
    Proof that (p and q) |- p
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({And(l=p, r=q)}, {p})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_conjunction_elim_taut_2():
    """
    Proof that (p and q) |- p
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({And(l=p, r=q)}, {q})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_disjunction_elim_taut_1():
    """
    Proof that p |- (p or q)
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({p}, {Or(l=p, r=q)})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_disjunction_elim_taut_2():
    """
    Proof that q |- (p or q)
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({q}, {Or(l=p, r=q)})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_or_disjunction_elim_multi():
    """
    Proof that p, q |- (p or q)
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({p, q}, {Or(l=p, r=q)})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_conditional_taut_1():
    """
    Proof that q |- (p -> q)
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({q}, {Implies(l=p, r=q)})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_conditional_taut_2_complex():
    """
    Proof that (not p) |- (p -> q)
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({Not(c=p)}, {Implies(l=p, r=q)})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True

def test_negated_conditional_taut():
    """
    Proof that (not (p -> q)) |- ((not p) and q)
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext(
        {Not(c=
                Implies(l=p, r=q)
             )},
        {And(l=p, r=Not(c=q))}
    )
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == True


"""
Impossible tests
"""

def test_proof_identity_impossible():
    """
    Proof that this is an open tree (not x) |- (not y).
    """
    x = Not(c=Atomic())
    y = Not(c=Atomic())

    ctx = ProofContext({x}, {y})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == False  # still closed

def test_conjunction_elim_impossible():
    """
    Proof that (p and q) |- p
    """
    p = Atomic()
    q = Atomic()
    ctx = ProofContext({And(l=p, r=q)}, {Atomic()})
    assert ctx.closed == False
    ctx.solve()
    assert ctx.closed == False
