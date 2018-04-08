#lang racket

(require "solver.rkt")
(require "myvy.rkt")

(define leader-election-term
  (append
   (list
    (type node)
    (type quorum)
    (type term)

    (immutable-relation member (node quorum))

    (axiom quorum-intersection
      (forall ((Q1 quorum) (Q2 quorum))
        (exists ((N node))
          (and (member N Q1) (member N Q2))))))

   (total-order 'term)

   (list
    (mutable-relation votes (node term node))
    (init votes (forall ((N node) (T term)  (V node)) (not (votes N T V))))

    (mutable-relation leader (node term))
    (init leader (forall ((N node) (T term)) (not (leader N T))))

    (mutable-relation voted (node term))
    (init voted (forall ((N node) (T term)) (not (voted N T))))

    (mutable-relation request-vote-msg (node term node))
    (init request-vote-msg
      (forall ((N1 node) (T term) (N2 node))
        (not (request-vote-msg N1 T N2))))

    (mutable-relation vote-msg (node term node))
    (init vote-msg
      (forall ((N1 node) (T term) (N2 node))
        (not (vote-msg N1 T N2))))

    (mutable-function voting-quorum (term) quorum)

    (mutable-relation current-term (node term))
    (init current-term
      (forall ((N node) (T term))
        (= (current-term N T)
           (= T term-zero))))

    (transition become-leader
      (modifies (voting-quorum leader)
        (exists ((n node) (t term))
          (and (old (current-term n t))
               (forall ((T term))
                 (=> (not (= T t))
                     (= (voting-quorum T) (old (voting-quorum T)))))
               (forall ((N node)) (=> (member N (voting-quorum t)) (old (votes n t N))))
               (forall ((N node) (T term))
                 (= (leader N T)
                    (or (old (leader N T))
                        (and (= N n) (= T t)))))))))

    (transition timeout
      (modifies (current-term)
        (exists ((n node) (t1 term) (t2 term))
          (and (old (current-term n t1))
               (term-le t1 t2)
               (not (= t1 t2))
               (forall ((N node) (T term))
                 (= (current-term N T)
                    (ite (= N n)
                         (= T t2)
                         (old (current-term N T)))))))))

    (transition send-request-vote
      (modifies (request-vote-msg)
        (exists ((n node) (t term))
          (and (old (current-term n t))
               (forall ((N1 node) (T term) (N2 node))
                 (= (request-vote-msg N1 T N2)
                    (or (old (request-vote-msg N1 T N2))
                        (and (= N1 n)
                             (= T t)))))))))

    (transition receive-request-vote
      (modifies (voted vote-msg)
        (exists ((n node) (t term) (sender node))
          (and (old (current-term n t))
               (not (old (voted n t)))
               (old (request-vote-msg sender t n))
               (forall ((N node) (T term))
                 (= (voted N T)
                    (or (old (voted N T))
                        (and (= N n) (= T t)))))
               (forall ((N1 node) (T term) (N2 node))
                 (= (vote-msg N1 T N2)
                    (or (old (vote-msg N1 T N2))
                        (and (= N1 n)
                             (= T t)
                             (= N2 sender)))))))))

    (transition receive-vote
      (modifies (votes)
        (exists ((n node) (t term) (sender node))
          (and (old (current-term n t))
               (old (vote-msg sender t n))
               (forall ((N1 node) (T term) (N2 node))
                 (= (votes N1 T N2)
                    (or (old (votes N1 T N2))
                        (and (= N1 n)
                             (= T t)
                             (= N2 sender)))))))))

    (corollary at-most-one-leader
      (forall ((N1 node) (N2 node) (T term))
        (=> (and (leader N1 T) (leader N2 T))
            (= N1 N2))))

    (invariant at-most-one-leader
      (forall ((N1 node) (N2 node) (T term))
        (=> (and (leader N1 T) (leader N2 T))
            (= N1 N2))))

    (invariant leader-has-quorum
      (forall ((L node) (T term))
        (=> (leader L T)
            (forall ((V node))
              (=> (member V (voting-quorum T))
                  (votes L T V))))))

    (invariant at-most-one-votes
      (forall ((C1 node) (C2 node) (T term) (V node))
        (=> (and (votes C1 T V) (votes C2 T V))
            (= C1 C2))))

    (invariant votes-were-received
      (forall ((C node) (T term) (V node))
        (=> (votes C T V) (vote-msg V T C))))

    (invariant at-most-one-vote-msg
      (forall ((C1 node) (C2 node) (T term) (V node))
        (=> (and (vote-msg V T C1) (vote-msg V T C2))
            (= C1 C2))))

    (invariant vote-msg-voted
      (forall ((C node) (T term) (V node))
        (=> (vote-msg V T C) (voted V T)))))))


#;(myvy-bmc leader-election-term 5
            (solver-not (get-corollary-by-name leader-election-term 'at-most-one-leader)))

#;(myvy-verify leader-election-term)

#; (myvy-updr leader-election-term)

(define log null)

(define (main)
  (for ([i (in-naturals)])
    (define op (open-output-string))
    (define-values (result x t y)
      (parameterize ([current-output-port op])
        (time-apply myvy-updr (list leader-election-term))))
    (pretty-print (list t result))
    (set! log (cons (list t result (get-output-string op)) log))))
