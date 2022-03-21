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
    child: Formula

    def __repr__(self):
        return f"(not {repr(self.child)})"

class And(Formula):
    left: Formula
    right: Formula

    def __repr__(self):
        return f"({repr(self.left)} and {repr(self.right)})"

class Or(Formula):
    left: Formula
    right: Formula

    def __repr__(self):
        return f"({repr(self.left)} or {repr(self.right)})"

class Then(Formula):
    left: Formula
    right: Formula

    def __repr__(self):
        return f"({repr(self.left)} -> {repr(self.right)})"

"""
Non-branching rules
"""

# TODO: implement rule combinators to make it easier to write new deduction rules
def not_reduce(ctx: ProofContext) -> List[ProofContext]:
    left = ctx.left()
    right = ctx.right()

    new_left = set()
    new_right = set()

    for statement in left:
        if isinstance(statement, Not) and statement.child not in right:
            new_right.add(statement.child)

    for statement in right:
        if isinstance(statement, Not) and statement.child not in left:
            new_left.add(statement.child)

    if new_right or new_right:
        return [ProofContext(new_left, new_right, parent=ctx)]

    return []

def and_reduce_left(ctx: ProofContext) -> Optional[ProofContext]:
    left = ctx.left()
    right = ctx.right()

    new_left = set()
    for statement in left:
        if isinstance(statement, And):
            if statement.left not in left:
                new_left.add(statement.left)

            if statement.right not in left:
                new_left.add(statement.right)

    if new_left:
        return [ProofContext(new_left, set(), parent=ctx)]

    return []

def or_reduce_right(ctx: ProofContext) -> Optional[ProofContext]:
    left = ctx.left()
    right = ctx.right()

    new_right = set()
    for statement in right:
        if isinstance(statement, Or):
            if statement.left not in right:
                new_right.add(statement.left)

            if statement.right not in right:
                new_right.add(statement.right)

    if new_right:
        return [ProofContext(set(), new_right, parent=ctx)]

    return []

def then_reduce_right(ctx: ProofContext) -> Optional[ProofContext]:
    left = ctx.left()
    right = ctx.right()

    new_left = set()
    new_right = set()
    for statement in right:
        if isinstance(statement, Then):
            if statement.left not in left:
                new_left.add(statement.left)

            if statement.right not in right:
                new_right.add(statement.right)

    if new_right:
        return [ProofContext(new_left, new_right, parent=ctx)]

    return []

"""
Branchers
"""

def or_reduce_left(ctx: ProofContext) -> Optional[ProofContext]:
    left = ctx.left()

    new_ctx = []
    for statement in left:
        if isinstance(statement, Or):
            if not (statement.left in left and statement.right in left):
            # if statement.left not in left:
                new_ctx.append(ProofContext({statement.left}, set(), parent=ctx))

            # if statement.right not in left:
                new_ctx.append(ProofContext({statement.right}, set(), parent=ctx))

            if new_ctx:
                return new_ctx
    return []


def and_reduce_right(ctx: ProofContext) -> Optional[ProofContext]:
    left = ctx.left()
    right = ctx.right()

    new_ctx = []
    for statement in right:
        if isinstance(statement, And):
            if not (statement.left in right and statement.right in right):
            # if statement.left not in right:
                new_ctx.append(ProofContext(set(), {statement.left}, parent=ctx))

            # if statement.right not in right:
                new_ctx.append(ProofContext(set(), {statement.right}, parent=ctx))

            if new_ctx:
                return new_ctx
    return []

def then_reduce_left(ctx: ProofContext) -> Optional[ProofContext]:
    left = ctx.left()
    right = ctx.left()

    new_ctx = []
    for statement in left:
        if isinstance(statement, Or):
            if not (statement.left in right and statement.right not in left):
            # if statement.left not in right:
                new_ctx.append(ProofContext(set(), {statement.left}, parent=ctx))

            # if statement.right not in left:
                new_ctx.append(ProofContext({statement.right}, set(), parent=ctx))

            if new_ctx:
                return new_ctx
    return []

# hueristically ordered by priority
REDUCTION_RULES = [
    not_reduce, and_reduce_left, or_reduce_right, then_reduce_right, # non-branching
    and_reduce_right  # branching
]

class ProofContext():
    """
    Prototype implementation of the two-sided tree system to build intuition for formal verification.
    For now: sentential logic only
    """
    def __init__(self,
                 new_left: Set[Formula],
                 new_right: Set[Formula],
                 parent: Optional[ProofContext] = None
                 ):
        self.parent = parent
        self.new_left = new_left
        self.new_right = new_right
        self.children = []
        self.closed = False
        self.uuid = secrets.token_hex(4)

    def __repr__(self):
        try:
            max_left = max([len(x) for x in self.new_left])
        except ValueError:
            max_left = 0

        try:
            max_right = max([len(x) for x in self.new_right])
        except ValueError:
            max_right = 0

        max_length = max(max_left, max_right)

        left_reprs = [repr(x).ljust(max_length) for x in self.new_left]
        right_reprs = [repr(x).rjust(max_length) for x in self.new_right]

        while len(left_reprs) != len(right_reprs):
            if len(left_reprs) < len(right_reprs):
                left_reprs.append(" " * max_length)
            elif len(left_reprs) > len(right_reprs):
                right_reprs.append(" " * max_length)

        final_repr = ""
        for left, right in zip(left_reprs, right_reprs):
            final_repr += f"{left} | {right}\n"

        if len(self.children) == 0:
            if self.closed:
                final_repr += "X"
            else:
                final_repr += "O"

        return final_repr.strip("\n")

    def generate_graphviz(self):
        dot = self.generate_dots_graphviz()
        dot = self.fill_edges_graphviz(dot)

        print(dot.source)

        # doctest_mark_exe()
        dot.render('two-sided-tree.gv', view=True)

    def generate_dots_graphviz(self, dot = None):
        import graphviz  # optional dep

        if not dot:
            dot = graphviz.Digraph(comment='Two-Sided Tree')

        dot.node(self.uuid, repr(self))
        for child in self.children:
            dot = child.generate_dots_graphviz(dot)

        return dot

    def fill_edges_graphviz(self, dot):
        import graphviz  # optional dep
        for child in self.children:
            dot.edge(self.uuid, child.uuid)

        for child in self.children:
            dot = child.fill_edges_graphviz(dot)

        return dot

    def left(self):
        if self.parent:
            return self.parent.left().union(self.new_left)
        return self.new_left

    def right(self):
        if self.parent:
            return self.parent.right().union(self.new_right)
        return self.new_right

    def solve(self, rules = REDUCTION_RULES, recursive: bool = True): # TODO: add type, check
        """
        Recursively apply the rules until computation finishes
        """
        print(self.left(), self.right())
        if self.contradiction_found():  # in this case, our work is done and we short-cut
            self.closed = True

        else:
            for rule in rules:
                if children := rule(self):
                    print(rule)
                    self.children = children
                    break

            if recursive:
                for child in children:
                    child.solve()

            if len(children) == 0 and self.contradiction_found():
                self.closed = True
            elif len(children) != 0 and all([child.closed for child in children]):
                self.closed = True

        return self.closed

    def contradiction_found(self):
        """
        """
        return len(self.left().intersection(self.right())) > 0

