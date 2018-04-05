#lang racket

(require "solver.rkt")
(require "myvy.rkt")

(define lockserv
  (list
   (type client)

   (mutable-relation request (client))
   (mutable-relation grant (client))
   (mutable-relation release (client))

   (mutable-relation client-held (client))

   (mutable-relation server-held ())

   (init init-request (forall ((C client)) (not (request C))))
   (init init-grant (forall ((C client)) (not (grant C))))
   (init init-release (forall ((C client)) (not (release C))))
   (init init-client-held (forall ((C client)) (not (client-held C))))
   (init init-server-held (not server-held))

   (transition send-request
     (modifies (request)
       (exists ((c client))
         (forall ((C client))
           (= (request C) (or (old (request C))
                              (= C c)))))))

   (transition do-grant
     (modifies (request grant server-held)
       (exists ((c client))
         (and (not (old server-held))
              server-held
              (old (request c))
              (forall ((C client))
                (= (request C)
                   (and (old (request C))
                        (not (= C c)))))
              (forall ((C client))
                (= (grant C) (or (old (grant C))
                                 (= C c))))))))

   (transition recv-grant
     (modifies (grant client-held)
       (exists ((c client))
         (and (old (grant c))
              (forall ((C client))
                (= (grant C)
                   (and (old (grant C))
                        (not (= C c)))))
              (forall ((C client))
                (= (client-held C)
                   (or (old (client-held C))
                       (= C c))))))))


   (transition do-release
     (modifies (client-held release)
       (exists ((c client))
         (and (old (client-held c))
              (forall ((C client))
                (= (client-held C)
                   (and (old (client-held C))
                        (not (= C c)))))
              (forall ((C client))
                (= (release C) (or (old (release C))
                                   (= C c))))))))

   (transition recv-release
     (modifies (release server-held)
       (exists ((c client))
         (and (old (release c))
              (forall ((C client))
                (= (release C)
                   (and (old (release C))
                        (not (= C c)))))
              (not server-held)))))

   (corollary mutex
     (forall ((C1 client) (C2 client))
       (=> (and (client-held C1) (client-held C2))
           (= C1 C2))))

   (invariant mutex
     (forall ((C1 client) (C2 client))
       (=> (and (client-held C1) (client-held C2))
           (= C1 C2))))

   (invariant grant-not-client-held
     (forall ((C1 client) (C2 client))
       (not (and (client-held C1) (grant C2)))))

   (invariant release-not-client-held
     (forall ((C1 client) (C2 client))
       (not (and (client-held C1) (release C2)))))

   (invariant not-grant-and-release
     (forall ((C1 client) (C2 client))
       (not (and (grant C1) (release C2)))))

   (invariant client-held-server-held
     (forall ((C client))
       (=> (client-held C) server-held)))

   (invariant at-most-one-grant
     (forall ((C1 client) (C2 client))
       (=> (and (grant C1) (grant C2))
           (= C1 C2))))

   (invariant at-most-one-release
     (forall ((C1 client) (C2 client))
       (=> (and (release C1) (release C2))
           (= C1 C2))))

   (invariant grant-server-held
     (forall ((C client))
       (=> (grant C) server-held)))

   (invariant release-server-held
     (forall ((C client))
       (=> (release C) server-held)))



))


#;(myvy-verify lockserv)

