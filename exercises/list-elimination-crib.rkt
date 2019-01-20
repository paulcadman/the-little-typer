#lang pie

;; Exercises on Pi types and using the List elimiator from Chapters 4 and 5
;; of The Little Typer
;;
;; Some exercises are adapted from assignments at Indiana University

(claim elim-Pair
       (Π ([A U]
           [D U]
           [X U])
          (-> (Pair A D)
              (-> A D
                  X)
              X)))

(define elim-Pair
  (λ (A D X)
    (λ (p f)
      (f (car p) (cdr p)))))


(claim + (-> Nat Nat
             Nat))
(define +
  (lambda (n m)
    (rec-Nat n
             m
             (lambda (n-1 m+n-1)
               (add1 m+n-1)))))

;; Exercise 4.1
;;
;; Extend the definitions of kar and kdr (frame 4.42) so they work with arbirary
;; Pairs (instead of just for Pair Nat Nat).

(claim kar
       (Π ([A U]
           [D U])
          (-> (Pair A D)
              A)))

(define kar
  (λ (A D)
    (λ (p)
      (elim-Pair
       A
       D
       A
       p
       (λ (a _)
         a)))))

(check-same Nat (kar Nat Nat (cons 1 2)) 1)

(claim kdr
       (Π ([A U]
           [D U])
          (-> (Pair A D)
              D)))

(define kdr
  (λ (A D)
    (λ (p)
      (elim-Pair
       A
       D
       D
       p
       (λ (_ d)
         d)))))

(check-same Nat (kdr Nat Nat (cons 1 2)) 2)


;; Exercise 4.2
;;
;; Define a function called compose that takes (in addition to the type
;; arguments A, B, C) an argument of type (-> A B) and an argument of
;; type (-> B C) that and evaluates to a value of type (-> A C), the function
;; composition of the arguments.

(claim compose
       (Π ([A U]
           [B U]
           [C U])
          (-> (-> A B) (-> B C)
              (-> A C))))

(define compose
  (λ (A B C)
    (λ (f g)
      (λ (a)
        (g (f a))))))

(check-same Nat ((compose Nat Nat Nat (+ 3) (+ 7)) 0) 10)


;; Exercise 5.1
;;
;; Define a function called sum-List that takes one List Nat argument and
;; evaluates to a Nat, the sum of the Nats in the list.


(claim sum-List
       (-> (List Nat)
           Nat))

(claim sum-List-step
       (-> Nat (List Nat) Nat
           Nat))

(define sum-List-step
  (λ (e _ es-sum)
    (+ e es-sum)))

(define sum-List
  (λ (es)
    (rec-List es
              0
              sum-List-step)))

(check-same Nat (sum-List (:: 1 (:: 2 nil))) 3)
(check-same Nat (sum-List (:: 1 (:: 4 (:: 2 nil)))) 7)


;; Exercise 5.2
;;
;; Define a function called maybe-last which takes (in addition to the type
;; argument for the list element) one (List E) argument and one E argument and
;; evaluates to an E with value of either the last element in the list, or the
;; value of the second argument if the list is empty.


(claim maybe-last
       (Π ([E U])
          (-> (List E) E
              E)))

(claim maybe-last-step
       (Π ([E U])
          (-> E (List E) (-> E E)
              (-> E E))))

(define maybe-last-step
  (λ (E)
    (λ (e es maybe-last-es)
      (rec-List es
                (the (-> E E) (λ (_) e))
                (λ (_ _ _) maybe-last-es)))))

(define maybe-last
  (λ (E)
    (λ (es)
      (rec-List es
                (the (-> E E) (λ (default) default))
                (maybe-last-step E)))))

(check-same Nat (maybe-last Nat nil 0) 0)
(check-same Nat (maybe-last Nat (:: 42 nil) 0) 42)
(check-same Nat (maybe-last Nat (:: 41 (:: 42 nil)) 0) 42)

;; Exercise 5.3
;;
;; Define a function called filter-list which takes (in addition to the type
;; argument for the list element) one (-> E Nat) argument representing a
;; predicate and one (List E) argument.
;;
;; The function evaluates to a (List E) consisting of elements from the list
;; argument where the predicate is true.
;;
;; Consider the predicate to be false for an element if it evaluates to zero,
;; and true otherwise.


(claim if
       (Π ([A U])
          (-> Nat A A
              A)))

(define if
  (λ (A)
    (λ (e if-then if-else)
      (which-Nat e
                 if-else
                 (λ (_) if-then)))))

(claim filter-list
       (Π ([E U])
          (-> (-> E Nat) (List E)
              (List E))))

(claim filter-list-step
       (Π ([E U])
          (-> (-> E Nat)
              (-> E (List E) (List E)
                  (List E)))))

(define filter-list-step
  (λ (E)
    (λ (p)
      (λ (e es filtered-es)
        (if (List E) (p e)
            (:: e filtered-es)
            filtered-es)))))

(define filter-list
  (λ (E)
    (λ (p es)
      (rec-List es
                (the (List E) nil)
                (filter-list-step E p)))))

(claim id
       (Π ([E U])
          (-> E
              E)))

(define id
  (λ (E)
    (λ (x) x)))

(claim different-from-zero
       (-> Nat
           Nat))

(define different-from-zero (id Nat))

(check-same (List Nat) (filter-list Nat different-from-zero (:: 0 (:: 1 (:: 0 nil)))) (:: 1 nil))
(check-same (List Nat) (filter-list Nat different-from-zero (:: 0 (:: 0 (:: 0 nil)))) nil)
(check-same (List Nat) (filter-list Nat different-from-zero nil) nil)

;; Exercise 5.4
;;
;; Define a function called sort-List-Nat which takes (in addition to the type
;; argument for the list element) one (List E) argument and evaluates to a
;; a (List E) consisting of the elements from the list argument sorted in
;; ascending order.
