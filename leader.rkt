#lang racket

(require "solver.rkt")
(require "myvy.rkt")

; A myvy system is a list of declarations.
;
; Most kinds of declarations should be self-explanatory to Ivy users, but there are some differences:
; - Myvy requires you to say whether relations/constants are mutable or immutable.
;   For example, in leader election, the `member` relation is immutable, but, eg, `leader` is mutable.
; - Myvy does not currently support function symbols, but not for any deep reason.
; - Myvy distinguishes between invariants and corollaries (the latter are somewhat poorly named,
;   better would be "safety properties" or "specification").
;   During verification, the conjunction of all invariants is checked to be inductive.
;   Then, separately, the conjunction of all invariants is checked to imply the corollaries.
;   During UPDR,  myvy starts from the corollaries and tries to find an invariant.
; - Transitions (actions) are written directly as two state formulas in logic, rather than
;   as imperative programs. Use `(old (R x y))` to refer to the (mutable) relation R in the prestate.
; - Transitions must fully constrain the state. In a system with two mutable constants C and D,
;   the transition (= C (old D)) is equivalent to the imperative program
;       C := D;
;       D := *;
;   rather than just the first statement, because the formula fails to otherwise constrain the value
;   of D in the poststate. Thus, many transitions will have conjunctions of the form (= D (old D))
;   for every part of the state they do not touch.
;   Myvy supports a shorthand for these transitions, by analogy to "modifies" clauses.
;   So the example transition above could be written
;       (modifies (C)
;           (= C (old D)))
;   which myvy desugars into
;       (and (= D (old D))
;            (= C (old D)))
;   In other words, a modifies clause adds "framing" conjuncts for every unmodified part of the state.

(define leader-election
  (list
   (type node)
   (type quorum)

   (immutable-relation member (node quorum))

   (axiom quorum-intersection
     (forall ((Q1 quorum) (Q2 quorum))
       (exists ((N node))
               (and (member N Q1) (member N Q2)))))

   (mutable-relation votes (node node))
   (init votes (forall ((N node) (V node)) (not (votes N V))))

   (mutable-relation leader (node))
   (init leader (forall ((N node)) (not (leader N))))

   (mutable-relation voted (node))
   (init voted (forall ((N node)) (not (voted N))))

   (mutable-relation request-vote-msg (node node))
   (init request-vote-msg (forall ((N1 node) (N2 node)) (not (request-vote-msg N1 N2))))

   (mutable-relation vote-msg (node node))
   (init vote-msg (forall ((N1 node) (N2 node)) (not (vote-msg N1 N2))))

   (mutable-constant voting-quorum quorum)

   (transition become-leader
     (modifies (voting-quorum leader)
       (exists ((n node))
         (and (forall ((N node)) (=> (member N voting-quorum) (old (votes n N))))
              (forall ((N node)) (= (leader N) (or (old (leader N))
                                                   (= N n))))))))
   (transition send-request-vote
     (modifies (request-vote-msg)
       (exists ((n node))
         (forall ((N1 node) (N2 node))
           (= (request-vote-msg N1 N2)
              (or (old (request-vote-msg N1 N2))
                  (= N1 n)))))))

   (transition receive-request-vote
     (modifies (voted vote-msg)
       (exists ((n node) (sender node))
         (and (not (old (voted n)))
              (old (request-vote-msg sender n))
              (forall ((N node))
                (= (voted N)
                   (or (old (voted N))
                       (= N n))))
              (forall ((N1 node) (N2 node))
                (= (vote-msg N1 N2)
                   (or (old (vote-msg N1 N2))
                       (and (= N1 n)
                            (= N2 sender)))))))))

   (transition receive-vote
     (modifies (votes)
       (exists ((n node) (sender node))
         (and (old (vote-msg sender n))
              (forall ((N1 node) (N2 node))
                (= (votes N1 N2)
                   (or (old (votes N1 N2))
                       (and (= N1 n)
                            (= N2 sender)))))))))

   (corollary at-most-one-leader
     (forall ((N1 node) (N2 node))
       (=> (and (leader N1) (leader N2))
           (= N1 N2))))

   (invariant at-most-one-votes
       (forall ((C1 node) (C2 node) (V node))
         (=> (and (votes C1 V) (votes C2 V))
             (= C1 C2))))

   (invariant leader-has-quorum
     (forall ((L node))
       (=> (leader L)
           (forall ((V node))
             (=> (member V voting-quorum)
                 (votes L V))))))

   (invariant votes-were-received
       (forall ((C node) (V node))
         (=> (votes C V) (vote-msg V C))))

   (invariant at-most-one-vote-msg
       (forall ((C1 node) (C2 node) (V node))
         (=> (and (vote-msg V C1) (vote-msg V C2))
             (= C1 C2))))

   (invariant vote-msg-voted
       (forall ((C node) (V node))
         (=> (vote-msg V C) (voted V))))

   ))


; I usually use myvy by loading this file in the REPL
; and then executing one of the following lines.

; You need to edit this line in myvy.rkt to point to your z3 binary
; (around line 517 at time of writing)
;
;     (parameterize ([z3 "/Users/jrw12/local/bin/z3"])
;       (solver-init))
;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BMC corollary (safety property) at-most-one-leader to depth 5 (ie, 5 transitions, so 6 states).
; myvy-bmc's third argument is a (required) "goal" formula.
; Here we pass the negation of the safety property, but BMC is also good for other goals,
; like ensuring that it is possible to reach a state where a leader is elected.
; `solver-not` is a function that negates a formula represented as an s-expression, and
; also does a little bit of negation normal form stuff. See solver.rkt.

#;(myvy-bmc leader-election 5
             (solver-not (get-corollary-by-name leader-election 'at-most-one-leader)))

; should return 'unsat, indicating there are no concrete counterexamples at depth 5.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Verify inductive invariant:

#;(myvy-verify leader-election)

; should print a bunch of "ok!" messages.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Infer invariant (ignoring invariant declarations and starting from corollaries)
; On this file, typically takes between 4 and 6 minutes to find an invariant.
; See the lockserv for a simpler system where it works faster.
#; (myvy-updr leader-election)


