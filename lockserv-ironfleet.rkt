#lang racket

(require "solver.rkt")
(require "myvy.rkt")

(define lockserv-ironfleet
  (append
   (list
    (type node)
    (type epoch))

   (total-order 'epoch)

   (list

    (mutable-relation held (node))
    (init held
      (forall ((N1 node) (N2 node))
        (=> (and (held N1) (held N2))
            (= N1 N2))))

    (mutable-function current-epoch (node) epoch)
    (init current-epoch
      (forall ((N node))
        (= (current-epoch N) epoch-zero)))

    (mutable-relation grant (node epoch))
    (init grant
      (forall ((R node) (E epoch))
        (not (grant R E))))

    (mutable-relation announce (node epoch))
    (init announce
      (forall ((S node) (E epoch))
        (not (announce S E))))

    ; assume held(n);
    ; var e;
    ; assume current-epoch(n) < e;
    ; held(n) := false;
    ; var next;
    ; grant(next e) := true;
    (transition grant
      (modifies (held grant)
        (exists ((n node) (next node) (e epoch))
          (and (old (held n))
               (and (epoch-le (old (current-epoch n)) e)
                    (not (= (old (current-epoch n)) e)))
               (forall ((N node))
                 (= (held N)
                    (and (old (held N))
                         (not (= n N)))))
               (forall ((N node) (E epoch))
                 (= (grant N E)
                    (or (old (grant N E))
                        (and (= N next)
                             (= E e)))))))))

    ; assume grant(n, e);
    ; grant(n, e) := false;
    ; current-epoch(n) := e;
    ; held(n) := true;
    (transition accept
      (modifies (grant current-epoch held)
        (exists ((n node) (e epoch))
          (and (old (grant n e))
               (forall ((N node) (E epoch))
                 (= (grant N E)
                    (and (old (grant N E))
                         (not (and (= N n) (= E e))))))
               (forall ((N node))
                 (= (current-epoch N)
                    (ite (= N n)
                         e
                         (old (current-epoch N)))))
               (forall ((N node))
                 (= (held N)
                    (or (old (held N))
                        (= N n))))))))

    ; assume held(n);
    ; announce(n, current-epoch(n)) := true;
    (transition announce
      (modifies (announce)
        (exists ((n node))
          (and (old (held n))
               (forall ((N node) (E epoch))
                 (= (announce N E)
                    (or (old (announce N E))
                        (and (= N n) (= E (current-epoch n))))))))))

    #;(corollary mutex
      (forall ((N1 node) (N2 node))
        (=> (and (held N1) (held N2))
            (= N1 N2))))

    (invariant mutex
        (forall ((N1 node) (N2 node))
          (=> (and (held N1) (held N2))
              (= N1 N2))))

    (invariant one-grant
        (forall ((N1 node) (E1 epoch) (N2 node) (E2 epoch))
          (=> (and (grant N1 E1) (grant N2 E2))
              (and (= N1 N2) (= E1 E2)))))

    (invariant grant-held
        (forall ((N1 node) (E1 epoch) (N2 node))
          (not (and (grant N1 E1) (held N2)))))

    )))


#;(myvy-verify lockserv-ironfleet)






