## Example usage

``` python
from sugar import *  # some syntatic sugar

p = Atomic("p")
q = Atomic("q")

left = Implies(p, q)
right = Implies(Not(q), Not(p))

context = ProofContext({left}, {right})
assert context.solve() # it's true!

# Generate some figs:
context.generate_graphviz("contrapositive", view = True) 
```
