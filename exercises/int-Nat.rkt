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

;; Exercise 7.0
;;
;; Define a function called zip that takes an argument of type (Vec A n) and a
;; second argument of type (Vec B n) and evaluates to a vlue of type (Vec (Pair A B) n),
;; the result of zipping the first and second arguments.

;; Exercise 7.1
;;
;; Define a function called append that takes an argument of type (Vec E n) and an
;; argument of type (Vect E m) and evaluates to a value of type (Vec (+ n m)), the
;; result of appending the elements of the second argument to the end of the first.

(claim append
       (Π ([E U]
           [n Nat]
           [m Nat])
          (-> (Vec E n) (Vec E m)
              (Vec E (+ n m)))))

;; Exercise 7.2
;;
;; Define a function called drop-last-k that takes an argument of type (Vec E ?) and
;; evaluates to a value of type (Vec E ?), the result of dropping the last k elements
;; from the first argument.
;;
;; NB: The type of the function should guarantee that we can't drop more elements
;; than there are in the first argument.
