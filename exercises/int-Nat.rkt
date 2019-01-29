#lang pie

;; Exercises on Vec and ind-Nat from Chapters 6 and 7 of The Little
;; Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (a-k b+a-k)
               (add1 b+a-k)))))

;; Exercise 7.1
;;
;; Define a function called append that takes an argument of type (Vect E n) and an
;; argument of type (Vect E m) and evaluates to a value of type (Vec (+ n m)), the 
;; result of appending the elements of the second argument to the end of the first.

(claim append
       (Π ([E U]
           [n Nat]
           [m Nat])
          (-> (Vec E n) (Vec E m)
              (Vec E (+ n m)))))
