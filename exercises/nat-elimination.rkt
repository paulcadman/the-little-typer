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


;; Exercise 3.2
;;
;; Rewrite the definition of + (in frame 3.27) using the rec-Nat eliminator instead of the iter-Nat eliminator.


;; Exercise 3.3
;;
;; Define a function called exp that takes two Nat arguments and evaluates to a Nat.
;;
;; exp evaluates to the exponentiation, a^b, of the two passed arguments.


;; Exercise 3.4
;;
;; Define a function called max that takes two Nat arguments and evaluates to a Nat.
;;
;; max evaluates to the larger of the two passed arguments.
