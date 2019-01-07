#lang pie

;; Exercises on using Nat elimiators from Chapter 3 of The Little Typer
;;
;; Some exercises are adapted from assignments at Indiana University

;; Exercise 3.1
;;
;; Define a function called at-least-two? that takes one Nat argument and evaluates to an Atom.
;;
;; at-least-two? evaluates to 't if the Nat is greater than or equal to 2 otherwise it evaluates to 'nil.
;;
;; Note: The only Nat eliminator you should need in the body of at-least-two? is which-Nat.

(claim at-least-two? (-> Nat
                         Atom))

(define at-least-two?
  (λ (n)
    (which-Nat n
               'nil
               (λ (n-1)
                 (which-Nat n-1
                            'nil
                            (λ (n-2) 't))))))

(check-same Atom (at-least-two? 0) 'nil)
(check-same Atom (at-least-two? 1) 'nil)
(check-same Atom (at-least-two? 2) 't)
(check-same Atom (at-least-two? 3) 't)
(check-same Atom (at-least-two? 10) 't)


;; Exercise 3.2
;;
;; Rewrite the definition of + (in frame 3.27) using the rec-Nat eliminator instead of the iter-Nat eliminator.

(claim + (-> Nat Nat
             Nat))

(define +
  (λ (n m)
    (rec-Nat n
             m
             (λ (n-1 n-1+m)
               (add1 n-1+m)))))

(check-same Nat (+ 0 0) 0)
(check-same Nat (+ 0 1) 1)
(check-same Nat (+ 1 0) 1)
(check-same Nat (+ 1 1) 2)
(check-same Nat (+ 2 3) 5)

;; Exercise 3.3
;;
;; Define a function called exp that takes two Nat arguments and evaluates to a Nat.
;;
;; exp evaluates to the exponentiation, a^b, of the two passed arguments.

(claim * (-> Nat Nat
             Nat))
(define *
  (λ (n m)
    (rec-Nat n
             0
             (λ (n-1 n-1*m)
               (+ m n-1*m)))))

(check-same Nat (* 0 0) 0)
(check-same Nat (* 1 0) 0)
(check-same Nat (* 0 1) 0)
(check-same Nat (* 1 1) 1)
(check-same Nat (* 1 2) 2)
(check-same Nat (* 3 4) 12)
(check-same Nat (* 10 10) 100)

(claim exp (-> Nat Nat
             Nat))
(define exp
  (λ (n m)
    (rec-Nat m
             1
             (λ (m-1 n^m-1)
               (* n n^m-1)))))

(check-same Nat (exp 0 0) 1)
(check-same Nat (exp 1 0) 1)
(check-same Nat (exp 0 1) 0)
(check-same Nat (exp 1 1) 1)
(check-same Nat (exp 1 2) 1)
(check-same Nat (exp 2 3) 8)
(check-same Nat (exp 10 3) 1000)


;; Exercise 3.4
;;
;; Define a function called max that takes two Nat arguments and evaluates to a Nat.
;;
;; max evaluates to the larger of the two passed arguments.

(claim sub1 (-> Nat Nat))
(define sub1 (λ (n) (which-Nat n
                               0
                               (λ (k) k))))

(claim max (-> Nat Nat
               Nat))
(define max
  (λ (n m)
    (which-Nat (iter-Nat n
                         m
                         (λ (smaller)
                           (sub1 smaller)))
               n
               (λ (k)
                 m))))

(check-same Nat (max 0 1) 1)
(check-same Nat (max 1 2) 2)
(check-same Nat (max 2 1) 2)
(check-same Nat (max 2 2) 2)
(check-same Nat (max 3 2) 3)
(check-same Nat (max 4 4) 4)
(check-same Nat (max 5 10) 10)
