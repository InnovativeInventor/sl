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
