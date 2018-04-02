# myvy: my reimplementation of some of Ivy

Files:

- `solver.rkt` thin wrapper around Z3's SMTLIB-2 interface.
- `myvy.rkt` implements inductive invariant checking, bounded model checking, and UPDR on transition systems
- `leader-election.rkt` example transition system

Note that UPDR is currently not working properly. BMC and inductive checking should work though.

Documentation:

- There is some basic documentation for using myvy in `leader-election.rkt`.
- The solver interface is also lightly documented in `solver.rkt`
- The internals of myvy are not yet documented.


