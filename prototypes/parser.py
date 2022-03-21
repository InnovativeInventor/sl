#!/usr/bin/env python
from __future__ import annotations

from ast import For
from dataclasses import dataclass
from pydantic import BaseModel
from typing import Optional, List, Set
import secrets

# Logical primitives
class Formula(BaseModel):
    def __hash__(self):
        return hash(repr(self))

    def __eq__(self, other):
        return repr(self) == repr(other)

    def __len__(self):
        return len(repr(self))

# @dataclass
class Atomic(Formula):
    name: Optional[str]
    value: Optional[bool]  # defaults to unknown

    # if no name is given, default to generating a fresh one
    fresh_name: Optional[str]

    def __repr__(self):
        if self.name:
            return self.name
        elif self.fresh_name:
            return self.fresh_name
        else:
            self.fresh_name = secrets.token_hex(4)
            return self.fresh_name

class Not(Formula):
    c: Formula  # c for child

    def __repr__(self):
        return f"(not {repr(self.c)})"

class And(Formula):
    l: Formula
    r: Formula

    def __repr__(self):
        return f"({repr(self.l)} and {repr(self.r)})"

class Or(Formula):
    l: Formula
    r: Formula

    def __repr__(self):
        return f"({repr(self.l)} or {repr(self.r)})"

class Implies(Formula):
    l: Formula
    r: Formula

    def __repr__(self):
        return f"({repr(self.l)} -> {repr(self.r)})"

"""
Non-branching rules
"""

# TODO: implement rule combinators to make it easier to write new deduction rules
def not_reduce_l(ctx: ProofContext) -> List[ProofContext]:
    l = ctx.l()
    r = ctx.r()

    new_r = set()

    for statement in l:
        if isinstance(statement, Not) and not ctx.is_reduced(statement):
            new_r.add(statement.c)
            ctx.marked_reduced.add(statement)

    if new_r:
        return [ProofContext(set(), new_r, parent=ctx)]

    return []

def not_reduce_r(ctx: ProofContext) -> List[ProofContext]:
    l = ctx.l()
    r = ctx.r()

    new_l = set()

    for statement in r:
        if isinstance(statement, Not) and not ctx.is_reduced(statement):
            new_l.add(statement.c)
            ctx.marked_reduced.add(statement)

    if new_l:
        return [ProofContext(new_l, set(), parent=ctx)]

    return []

def and_reduce_l(ctx: ProofContext) -> Optional[ProofContext]:
    l = ctx.l()
    r = ctx.r()

    new_l = set()
    for statement in l:
        if isinstance(statement, And) and not ctx.is_reduced(statement):
            if statement.l not in l:
                new_l.add(statement.l)

            if statement.r not in l:
                new_l.add(statement.r)

            ctx.marked_reduced.add(statement)

    if new_l:
        return [ProofContext(new_l, set(), parent=ctx)]

    return []

def or_reduce_r(ctx: ProofContext) -> Optional[ProofContext]:
    l = ctx.l()
    r = ctx.r()

    new_r = set()
    for statement in r:
        if isinstance(statement, Or) and not ctx.is_reduced(statement):
            if statement.l not in r:
                new_r.add(statement.l)

            if statement.r not in r:
                new_r.add(statement.r)

            ctx.marked_reduced.add(statement)

    if new_r:
        return [ProofContext(set(), new_r, parent=ctx)]

    return []

def implies_reduce_r(ctx: ProofContext) -> Optional[ProofContext]:
    l = ctx.l()
    r = ctx.r()

    new_l = set()
    new_r = set()
    for statement in r:
        if isinstance(statement, Implies) and not ctx.is_reduced(statement):
            if statement.l not in l:
                new_l.add(statement.l)

            if statement.r not in r:
                new_r.add(statement.r)

            ctx.marked_reduced.add(statement)

    if new_r:
        return [ProofContext(new_l, new_r, parent=ctx)]

    return []

"""
Branchers
"""

def or_reduce_l(ctx: ProofContext) -> Optional[ProofContext]:
    l = ctx.l()

    for statement in l:
        if isinstance(statement, Or) and not ctx.is_reduced(statement):
            new_ctx = []
            new_ctx.append(ProofContext({statement.l}, set(), parent=ctx))
            new_ctx.append(ProofContext({statement.r}, set(), parent=ctx))
            ctx.marked_reduced.add(statement)
            return new_ctx
    return []


def and_reduce_r(ctx: ProofContext) -> Optional[ProofContext]:
    r = ctx.r()

    for statement in r:
        if isinstance(statement, And) and not ctx.is_reduced(statement):
            new_ctx = []
            new_ctx.append(ProofContext(set(), {statement.l}, parent=ctx))
            new_ctx.append(ProofContext(set(), {statement.r}, parent=ctx))
            ctx.marked_reduced.add(statement)
            return new_ctx
    return []

def implies_reduce_l(ctx: ProofContext) -> Optional[ProofContext]:
    l = ctx.l()

    for statement in l:
        if isinstance(statement, Implies) and not ctx.is_reduced(statement):
            new_ctx = []
            new_ctx.append(ProofContext(set(), {statement.l}, parent=ctx))
            new_ctx.append(ProofContext({statement.r}, set(), parent=ctx))
            ctx.marked_reduced.add(statement)
            return new_ctx
    return []

# hueristically ordered by priority
REDUCTION_RULES = [
    not_reduce_l, not_reduce_r, and_reduce_l, or_reduce_r, implies_reduce_r, # non-branching
    and_reduce_r, implies_reduce_l, or_reduce_l # branching
]

class ProofContext():
    """
    Prototype implementation of the two-sided tree system to build intuition for formal verification.
    For now: sentential logic only
    """
    def __init__(self,
                 new_l: Set[Formula],
                 new_r: Set[Formula],
                 parent: Optional[ProofContext] = None,
                 ):
        if parent is None:
            self.depth = 0
        else:
            self.depth = parent.depth + 1

        self.parent = parent
        self.new_l = new_l
        self.new_r = new_r

        self.children = []
        self.closed = False
        self.uuid = secrets.token_hex(4)
        self.marked_reduced = set()

    def __repr__(self):
        try:
            max_l = max([len(x) for x in self.new_l])
        except ValueError:
            max_l = 0

        try:
            max_r = max([len(x) for x in self.new_r])
        except ValueError:
            max_r = 0

        max_length = max(max_l, max_r)

        l_reprs = [repr(x).ljust(max_length) for x in self.new_l]
        r_reprs = [repr(x).rjust(max_length) for x in self.new_r]

        while len(l_reprs) != len(r_reprs):
            if len(l_reprs) < len(r_reprs):
                l_reprs.append(" " * max_length)
            elif len(l_reprs) > len(r_reprs):
                r_reprs.append(" " * max_length)

        final_repr = ""
        for l, r in zip(l_reprs, r_reprs):
            final_repr += f"{l} | {r}\n"

        if len(self.children) == 0:
            if self.closed:
                final_repr += "X"
            else:
                final_repr += "O"

        return final_repr.strip("\n")

    def generate_graphviz(self, filename: str, comment: str = "", view: str = True):
        dot = self.generate_dots_graphviz(comment = comment)
        dot = self.fill_edges_graphviz(dot)
        dot.render(f"{filename}", view = view)

    def generate_dots_graphviz(self, dot = None, comment: str = ""):
        import graphviz  # optional dep
        if not dot:
            dot = graphviz.Digraph(comment=comment)
            dot.attr(fontname="Courier")

        dot.node(self.uuid, repr(self))
        for c in self.children:
            dot = c.generate_dots_graphviz(dot)

        return dot

    def fill_edges_graphviz(self, dot):
        import graphviz  # optional dep
        for c in self.children:
            dot.edge(self.uuid, c.uuid)

        for c in self.children:
            dot = c.fill_edges_graphviz(dot)

        return dot

    def reduced_formula(self):
        if self.parent:
            return self.parent.reduced_formula().union(self.marked_reduced)
        return self.marked_reduced

    def is_reduced(self, item: Formula):
        return item in self.reduced_formula()

    def l(self):
        if self.parent:
            return self.parent.l().union(self.new_l)
        return self.new_l

    def r(self):
        if self.parent:
            return self.parent.r().union(self.new_r)
        return self.new_r

    def solve(self, rules = REDUCTION_RULES, recursive: bool = True): # TODO: add type, check
        """
        Recursively apply the rules until computation finishes
        """
        print(self.l(), self.r())
        if self.contradiction_found():  # in this case, our work is done and we short-cut
            self.closed = True

        else:
            for rule in rules:
                if children := rule(self):
                    print(rule)
                    self.children = children
                    break

            if recursive and self.depth <= 5:
                for c in children:
                    print(self.depth)
                    # breakpoint()
                    c.solve()

            if len(children) == 0 and self.contradiction_found():
                self.closed = True
            elif len(children) != 0 and all([c.closed for c in children]):
                self.closed = True

        return self.closed

    def contradiction_found(self):
        return len(self.l().intersection(self.r())) > 0
