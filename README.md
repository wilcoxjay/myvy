# myvy: my reimplementation of some of Ivy

Files:

- `solver.rkt` thin wrapper around Z3's SMTLIB-2 interface.
- `myvy.rkt` implements inductive invariant checking, bounded model checking, and UPDR on transition systems
- Examples:
  - `leader.rkt` toy leader election using quorums
  - `leader-term.rkt` adding "terms" to leader election
  - `lockserv.rkt` Verdi lock service example
  - `lockserv-ironfleet.rkt` Ironfleet lock service example

Documentation:

- There is some basic documentation for using myvy in `leader.rkt`.
  Be sure to read the instructions near the bottom on how to tell myvy where Z3 is installed.
- The solver interface is also lightly documented in `solver.rkt`
- The internals of myvy are not yet documented.


