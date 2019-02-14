#lang pie

;; Exercises on Nat equality from Chapter 8 and 9 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

;; Exercise 8.1
;; Define a function called zero+n=n that states and proves that
;; 0+n = n for all Nat n.

;; Exercise 8.2
;;
;; Define a function called a=b->a+n=b+n that states and proves that
;; a = b implies a+n = b+n for all Nats a, b, n.

;; Exercise 8.3
;;
;; Define a function called plusAssociative that states and proves that
;; + is associative.

(claim plusAssociative
       (Π ([n Nat]
           [m Nat]
           [k Nat])
          (= Nat (+ k (+ n m)) (+ (+ k n) m))))

;; Exercise 8.4
;;
;; Define a function called plusCommutative that states and proves that
;; + is commutative
;;
;; Bonus: Write the solution using the trans elimiator instead of
;; the replace elimiator.
;; https://docs.racket-lang.org/pie/index.html#%28def._%28%28lib._pie%2Fmain..rkt%29._trans%29%29

(claim plusCommutative
       (Π ([n Nat]
           [m Nat])
          (= Nat (+ n m) (+ m n))))
