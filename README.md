# HEBB (Higher-order Environments + Black-Box ops)

HEBB is an abstract machine, implemented as a bytecode interpreter and
designed to facilitate automatic differentiation at a low level.

The starting point for the HEBB abstract machine is the extended family of
environment machines, e.g. the SECD machine, Krivine's machine, CAM, and Zinc.
The first idealized property we'd like in HEBB is the ability to track
computations and their dependencies through the graph of environments stored in
closures. Adjoints can then be calculated by traversing the environment graph
and building a new environment with the respective variables rebound to their
adjoint values.

The second property is the ability to easily add primitive operators with
associated adjoint code. These operators are essentially black boxes from the
point of view of the abstract machine.
