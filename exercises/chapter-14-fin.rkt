#lang pie

;; Exercises on Fin from Chapter 14 of The Little Typer

(claim Maybe
       (-> U
           U))

(define Maybe
  (λ (X)
    (Either X Trivial)))

(claim nothing
       (Π ([E U])
          (Maybe E)))

(define nothing
  (λ (_)
    (right sole)))

(claim just
       (Π ([E U])
          (-> E
              (Maybe E))))

(define just
  (λ (_ e)
    (left e)))

(claim Fin
       (-> Nat
           U))

(define Fin
  (λ (n)
    (iter-Nat n
              Absurd
              Maybe)))

(claim fzero
       (Π ([n Nat])
          (Fin (add1 n))))

(define fzero
  (λ (n)
    (nothing (Fin n))))

(claim fadd1
       (Π ([n Nat])
          (-> (Fin n)
              (Fin (add1 n)))))

(define fadd1
  (λ (n)
    (λ (i-1)
      (just (Fin n) i-1))))

;; Exercise 14.1
;;
;; Define a function called insert-at that inserts a Nat into
;; a Vector.
;;
;; The signature of the function should only allow calls that
;; insert the Nat at an existing position in the Vector.

(claim insert-at
       (Π ([l Nat])
          (-> (Fin (add1 l)) (Vec Nat l) Nat
              (Vec Nat (add1 l)))))

;; Define Matrix be the type of Nat valued matricies.

(claim Matrix
       (-> Nat Nat
           U))

(define Matrix
  (λ (rows columns)
    (Vec (Vec Nat columns) rows)))

;; Exercise 14.2
;;
;; Define a function called matrix-ref that can be used to find the
;; entries of a Matrix. Use Fin types for the arguments of this function
;; that bounds check the call to the dimenstions of the matrix.
