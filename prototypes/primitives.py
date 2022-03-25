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
    free: Optional[bool]  # defaults to unknown

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

    def replace(self, match: Formula, replacement: Formula):
        if isinstance(self.c, Atomic) and self.c == match:
            self.c = replacement
        else:
            self.c.replace(match, replacement)

class And(Formula):
    l: Formula
    r: Formula

    def __repr__(self):
        return f"({repr(self.l)} and {repr(self.r)})"

    def replace(self, match: Formula, replacement: Formula):
        if isinstance(self.l, Atomic) and self.l == match:
            self.l = replacement
        else:
            self.l.replace(match, replacement)

        if isinstance(self.r, Atomic) and self.r == match:
            self.r = replacement
        else:
            self.r.replace(match, replacement)

class Or(Formula):
    l: Formula
    r: Formula

    def __repr__(self):
        return f"({repr(self.l)} or {repr(self.r)})"

    def replace(self, match: Formula, replacement: Formula):
        if isinstance(self.l, Atomic) and self.l == match:
            self.l = replacement
        else:
            self.l.replace(match, replacement)

        if isinstance(self.r, Atomic) and self.r == match:
            self.r = replacement
        else:
            self.r.replace(match, replacement)

class Implies(Formula):
    l: Formula
    r: Formula

    def __repr__(self):
        return f"({repr(self.l)} -> {repr(self.r)})"

    def replace(self, match: Formula, replacement: Formula):
        if isinstance(self.l, Atomic) and self.l == match:
            self.l = replacement
        else:
            self.l.replace(match, replacement)

        if isinstance(self.r, Atomic) and self.r == match:
            self.r = replacement
        else:
            self.r.replace(match, replacement)

class Forall(Formula):
    var: Atomic
    expr: Formula
    # TODO: run-time validation of syntax
    def __repr__(self):
        return f"(forall {repr(self.var)}, {repr(self.expr)})"

    def replace(self, match: Formula, replacement: Formula):
        if isinstance(self.expr, Atomic) and self.expr == match:
            self.expr = replacement
        else:
            self.expr.replace(match, replacement)

class Exists(Formula):
    var: Atomic
    expr: Formula
    # TODO: run-time validation of syntax
    def __repr__(self):
        return f"(exists {repr(self.var)}, {repr(self.expr)})"

    def replace(self, match: Formula, replacement: Formula):
        if isinstance(self.expr, Atomic) and self.expr == match:
            self.expr = replacement
        else:
            self.expr.replace(match, replacement)
