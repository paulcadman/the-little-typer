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
;; Define a function called append that appends the elements of a Vect
;; to another.

(claim append
       (Π ([E U]
           [n Nat]
           [m Nat])
          (-> (Vec E n) (Vec E m)
              (Vec E (+ n m)))))
