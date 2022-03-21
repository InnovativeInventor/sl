#!/usr/bin/env python

import parser
from parser import ProofContext

def Atomic(name: str = ""):
    return parser.Atomic(name = name)

def Not(formula: parser.Formula):
    return parser.Not(c = formula)

def And(left: parser.Formula, right: parser.Formula):
    return parser.And(l = left, r = right)

def Or(left: parser.Formula, right: parser.Formula):
    return parser.Or(l = left, r = right)

def Implies(left: parser.Formula, right: parser.Formula):
    return parser.Implies(l = left, r = right)
