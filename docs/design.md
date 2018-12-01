`hebb` is an approach to computing with numbers and math.
A few sample motivating problems that should be easy to tackle with `hebb`:
automatic differentiation, hardware resource constraints (e.g. memory limits),
parallelism (e.g. multiple GPUs, distributed settings), and program optimization
(e.g. fusion systems, other transformations).

`hebb` in practice consists of a few parts:

* a (mostly) pure, strict, higher-order functional language
* an embeddable virtual machine for evaluating the language
* a standard library of "black box" data types and operations

# the hebb language

* syntactically, similar to OCaml
* application is explicit and (currently!) uses square brackets
* no partial evaluation or currying
* typical "features" like record types, strings, even types are not really
  prioritized at the outset
* but, a good semantics for modules is important; could simply mean first-class
  environments, or another implementation
* "mostly" pure: mutation can be queued, then on program termination and
  restart, queued mutations are applied as a form of initial state
* strict evaluation: easier to reason about
* program optimizations: easier to do what we want on first-class programs
  (liveness analysis is one of the main desiderata); some higher-order versions
  exist based on flow analysis

# the hebb virtual machine

* embeddable: has a C API for embedding inside other languages; think Lua
* rather directly corresponds to operational semantics of a CEK/CESK-style
  abstract machine
* has thunks but "simulates" call-by-value
* by having thunks, alternative evaluation strategies (e.g. non-deterministic
  or repeated evaluations) are possible to implement; as long as the evaluation
  terminates, the result is the same (Church-Rosser)
* good support for implementing custom "black box" boxed types and "primitive"
  operators

# the hebb standard library

* some lessons learned from previous implementations:
  * it is way too much work to support all the needed variations of operators,
    especially with some kind of polymorphism or multimethods
  * reduction, broadcast, concatenation, slicing can be particularly annoying
    (if not done the "right" way)
* opinion: rely as much as possible on a few ingredients:
  * functional combinators: fmap is one, but we also want "shaped" combinators
  * fusion systems (can have more than one)
  * let remaining program optimizations handle the details
