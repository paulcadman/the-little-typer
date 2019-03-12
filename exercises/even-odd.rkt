#lang pie

;; Exercises on Even and Odd from Chapter 12 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ a+b-1)
               (add1 a+b-1)))))

(claim double
       (-> Nat
           Nat))

(define double
  (λ (n)
    (rec-Nat n
             0
             (λ (_ n+n-2)
               (+ 2 n+n-2)))))

(claim Even
       (-> Nat
           U))

(define Even
  (λ (n)
    (Σ ([half Nat])
       (= Nat n (double half)))))

(claim Odd
       (-> Nat
           U))

(define Odd
  (λ (n)
    (Σ ([haf Nat])
       (= Nat n (add1 (double haf))))))

(claim <=
       (-> Nat Nat
           U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
       (= Nat (+ k a) b))))


;; Exercise 12.1
;;
;; Define a function called sumOfTwoEvensIsEven that states and proves that the sum
;; of two Even Nats is Even.

(claim sumOfTwoEvensIsEven
       (Π ([n Nat]
           [m Nat])
          (-> (Even n) (Even m)
              (Even (+ n m)))))

;; Exercise 12.2
;;
;; Define a function called sumOfTwoOddsIsEven that states and proves that the sum of
;; two Odd Nats is Even.

(claim sumOfTwoOddsIsEven
       (Π ([n Nat]
           [m Nat])
          (-> (Odd n) (Odd m)
              (Even (+ n m)))))


;; Exercise 12.3
;;
;; Define a function called nOrSuccnIsEven that states and proves that for all Nats n, either
;; n is Even or n+1 is Even.

(claim nOrSuccnIsEven
       (Π ([n Nat])
          (Either (Even n) (Even (add1 n)))))

;; Exercise 12.4
;;
;; Define a function called either-a<=b-or-b<=a that states and proves that for all Nats a b,
;; either a<=b or b<=a

(claim either-a<=b-or-b<=a
       (Π ([a Nat]
           [b Nat])
          (Either (<= a b) (<= b a))))
